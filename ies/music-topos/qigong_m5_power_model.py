#!/usr/bin/env python3
"""
qigong_m5_power_model.py

Apple M5 Power Model Implementation
Implements P = C × f × V² for dynamic power consumption estimation
and provides optimization parameters for red team / blue team resource management.

Based on:
- Apple M5 specifications (October 2025)
- Thermal design power: 27W base, 40W boost
- P-cores: 4x @ 4.42 GHz max
- E-cores: 6x @ 2.85 GHz max
"""

import json
import subprocess
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np


class CoreType(Enum):
    """Apple Silicon core types"""
    P_CORE = "p_core"
    E_CORE = "e_core"


class QoSClass(Enum):
    """macOS Quality of Service classes"""
    BACKGROUND = 9
    UTILITY = 17
    USER_INITIATED = 25
    USER_INTERACTIVE = 33
    DEFAULT = 4


@dataclass
class CoreConfig:
    """Configuration for a core type"""
    count: int
    min_freq_hz: float
    max_freq_hz: float
    typical_freq_hz: float
    min_voltage_v: float
    max_voltage_v: float
    typical_voltage_v: float
    capacitance_f: float
    l1_icache_kb: int
    l1_dcache_kb: int
    l2_cache_mb: int


@dataclass
class PowerState:
    """Power consumption state for a core"""
    core_type: CoreType
    frequency_hz: float
    voltage_v: float
    power_w: float
    utilization_percent: float


class M5PowerModel:
    """
    Apple M5 Power Model

    Implements thermal power modeling using P = C × f × V²
    Provides optimization parameters for qigong resource management.
    """

    # M5 Specifications
    P_CORE_CONFIG = CoreConfig(
        count=4,
        min_freq_hz=1.26e9,
        max_freq_hz=4.42e9,
        typical_freq_hz=4.10e9,
        min_voltage_v=0.65,
        max_voltage_v=1.05,
        typical_voltage_v=0.85,
        capacitance_f=1.2e-10,
        l1_icache_kb=768,
        l1_dcache_kb=512,
        l2_cache_mb=64
    )

    E_CORE_CONFIG = CoreConfig(
        count=6,
        min_freq_hz=1.02e9,
        max_freq_hz=2.85e9,
        typical_freq_hz=2.50e9,
        min_voltage_v=0.60,
        max_voltage_v=0.85,
        typical_voltage_v=0.75,
        capacitance_f=0.8e-10,
        l1_icache_kb=768,
        l1_dcache_kb=384,
        l2_cache_mb=6
    )

    # Thermal limits
    TDP_BASE_W = 27.0
    TDP_BOOST_W = 40.0
    THERMAL_THROTTLE_CELSIUS = 100.0
    MAX_JUNCTION_CELSIUS = 114.0

    # Power budgets
    IDLE_POWER_W = 1.5
    P_CORE_IDLE_MW = 2.0
    E_CORE_IDLE_MW = 1.0

    def __init__(self, config_path: Optional[Path] = None):
        """Initialize M5 power model"""
        self.config_path = config_path
        if config_path and config_path.exists():
            with open(config_path) as f:
                self.config = json.load(f)
        else:
            self.config = None

    @staticmethod
    def calculate_dynamic_power(
        capacitance: float,
        frequency: float,
        voltage: float
    ) -> float:
        """
        Calculate dynamic power consumption using P = C × f × V²

        Args:
            capacitance: Effective capacitance (Farads)
            frequency: Operating frequency (Hz)
            voltage: Supply voltage (Volts)

        Returns:
            Power consumption (Watts)
        """
        return capacitance * frequency * (voltage ** 2)

    def estimate_voltage_for_frequency(
        self,
        core_type: CoreType,
        frequency_hz: float
    ) -> float:
        """
        Estimate required voltage for a given frequency using linear interpolation.

        Real DVFS curves are non-linear, but this provides reasonable estimates.
        """
        config = self.P_CORE_CONFIG if core_type == CoreType.P_CORE else self.E_CORE_CONFIG

        # Normalize frequency to [0, 1] range
        freq_normalized = (frequency_hz - config.min_freq_hz) / (config.max_freq_hz - config.min_freq_hz)
        freq_normalized = np.clip(freq_normalized, 0.0, 1.0)

        # Voltage scales roughly with frequency (simplified)
        voltage = config.min_voltage_v + freq_normalized * (config.max_voltage_v - config.min_voltage_v)

        return voltage

    def calculate_core_power(
        self,
        core_type: CoreType,
        frequency_hz: float,
        utilization_percent: float = 100.0,
        voltage_v: Optional[float] = None
    ) -> PowerState:
        """
        Calculate power consumption for a single core at given frequency and utilization.

        Args:
            core_type: P-core or E-core
            frequency_hz: Operating frequency (Hz)
            utilization_percent: Core utilization (0-100)
            voltage_v: Optional voltage override (auto-estimated if None)

        Returns:
            PowerState with detailed power metrics
        """
        config = self.P_CORE_CONFIG if core_type == CoreType.P_CORE else self.E_CORE_CONFIG

        # Estimate voltage if not provided
        if voltage_v is None:
            voltage_v = self.estimate_voltage_for_frequency(core_type, frequency_hz)

        # Calculate dynamic power
        dynamic_power = self.calculate_dynamic_power(
            config.capacitance_f,
            frequency_hz,
            voltage_v
        )

        # Static (leakage) power - rough estimate as 10% of dynamic at typical voltage
        static_power = 0.1 * self.calculate_dynamic_power(
            config.capacitance_f,
            frequency_hz,
            config.typical_voltage_v
        )

        # Total power scaled by utilization
        total_power = (dynamic_power + static_power) * (utilization_percent / 100.0)

        return PowerState(
            core_type=core_type,
            frequency_hz=frequency_hz,
            voltage_v=voltage_v,
            power_w=total_power,
            utilization_percent=utilization_percent
        )

    def calculate_cluster_power(
        self,
        core_type: CoreType,
        frequency_hz: float,
        active_cores: int,
        utilization_percent: float = 100.0
    ) -> float:
        """
        Calculate total power for a cluster of cores.

        Args:
            core_type: P-core or E-core
            frequency_hz: Operating frequency (Hz)
            active_cores: Number of active cores
            utilization_percent: Average utilization across cores

        Returns:
            Total cluster power (Watts)
        """
        config = self.P_CORE_CONFIG if core_type == CoreType.P_CORE else self.E_CORE_CONFIG

        if active_cores > config.count:
            raise ValueError(f"Cannot activate {active_cores} {core_type.value}s (max: {config.count})")

        single_core = self.calculate_core_power(core_type, frequency_hz, utilization_percent)
        return single_core.power_w * active_cores

    def optimize_for_power_budget(
        self,
        target_power_w: float,
        core_type: CoreType,
        active_cores: int,
        utilization_percent: float = 100.0
    ) -> Tuple[float, float, float]:
        """
        Find optimal frequency to meet power budget.

        Args:
            target_power_w: Target power budget (Watts)
            core_type: P-core or E-core
            active_cores: Number of active cores
            utilization_percent: Core utilization

        Returns:
            (optimal_frequency_hz, optimal_voltage_v, actual_power_w)
        """
        config = self.P_CORE_CONFIG if core_type == CoreType.P_CORE else self.E_CORE_CONFIG

        # Binary search for optimal frequency
        low_freq = config.min_freq_hz
        high_freq = config.max_freq_hz
        tolerance = 1e6  # 1 MHz tolerance

        best_freq = low_freq
        best_voltage = config.min_voltage_v
        best_power = 0.0

        while high_freq - low_freq > tolerance:
            mid_freq = (low_freq + high_freq) / 2.0
            power = self.calculate_cluster_power(core_type, mid_freq, active_cores, utilization_percent)

            if power <= target_power_w:
                best_freq = mid_freq
                best_power = power
                best_voltage = self.estimate_voltage_for_frequency(core_type, mid_freq)
                low_freq = mid_freq
            else:
                high_freq = mid_freq

        return (best_freq, best_voltage, best_power)

    def generate_qos_recommendations(self) -> Dict[str, Dict]:
        """
        Generate QoS-specific frequency and power recommendations.

        Returns:
            Dictionary mapping QoS class names to configurations
        """
        recommendations = {}

        # Background (E-core only, minimal power)
        bg_freq, bg_volt, bg_power = self.optimize_for_power_budget(
            target_power_w=6.0,
            core_type=CoreType.E_CORE,
            active_cores=6,
            utilization_percent=80.0
        )
        recommendations["background"] = {
            "qos_class": QoSClass.BACKGROUND.value,
            "cores": "E-cores only",
            "frequency_hz": bg_freq,
            "voltage_v": bg_volt,
            "power_w": bg_power,
            "taskpolicy": "sudo taskpolicy -b -p <pid>"
        }

        # Utility (E-cores, moderate power)
        util_freq, util_volt, util_power = self.optimize_for_power_budget(
            target_power_w=8.0,
            core_type=CoreType.E_CORE,
            active_cores=6,
            utilization_percent=100.0
        )
        recommendations["utility"] = {
            "qos_class": QoSClass.UTILITY.value,
            "cores": "E-cores preferred",
            "frequency_hz": util_freq,
            "voltage_v": util_volt,
            "power_w": util_power,
            "taskpolicy": "sudo taskpolicy -c e -t <tid>"
        }

        # User Initiated (P-cores, balanced)
        ui_freq, ui_volt, ui_power = self.optimize_for_power_budget(
            target_power_w=20.0,
            core_type=CoreType.P_CORE,
            active_cores=4,
            utilization_percent=80.0
        )
        recommendations["user_initiated"] = {
            "qos_class": QoSClass.USER_INITIATED.value,
            "cores": "P-cores preferred",
            "frequency_hz": ui_freq,
            "voltage_v": ui_volt,
            "power_w": ui_power,
            "taskpolicy": "sudo taskpolicy -B -p <pid>"
        }

        # User Interactive (P-cores, high performance)
        uix_freq = self.P_CORE_CONFIG.typical_freq_hz
        uix_volt = self.estimate_voltage_for_frequency(CoreType.P_CORE, uix_freq)
        uix_power = self.calculate_cluster_power(CoreType.P_CORE, uix_freq, 4, 90.0)
        recommendations["user_interactive"] = {
            "qos_class": QoSClass.USER_INTERACTIVE.value,
            "cores": "P-cores prioritized",
            "frequency_hz": uix_freq,
            "voltage_v": uix_volt,
            "power_w": uix_power,
            "taskpolicy": "sudo taskpolicy -c p -t <tid>"
        }

        return recommendations

    def generate_red_team_config(self) -> Dict:
        """
        Generate optimal configuration for red team (stealth, E-core only).

        Returns:
            Configuration dictionary
        """
        freq, volt, power = self.optimize_for_power_budget(
            target_power_w=6.0,
            core_type=CoreType.E_CORE,
            active_cores=6,
            utilization_percent=75.0
        )

        return {
            "name": "Red Team Stealth Mode",
            "objective": "Minimal power signature, E-core exclusive",
            "cores": {
                "type": "E-cores only",
                "count": 6,
                "frequency_hz": freq,
                "voltage_v": volt
            },
            "power": {
                "target_w": 6.0,
                "actual_w": power,
                "thermal_signature_w": power,
                "headroom_w": self.TDP_BASE_W - power
            },
            "qos": {
                "class": "background",
                "level": QoSClass.BACKGROUND.value
            },
            "taskpolicy": "sudo taskpolicy -b -p <pid>",
            "validation": {
                "p_core_wakeups": 0,
                "power_under_threshold": bool(power < 8.0),
                "thermal_signature_minimal": "yes"
            }
        }

    def generate_blue_team_config(self) -> Dict:
        """
        Generate optimal configuration for blue team (detection, P-core).

        Returns:
            Configuration dictionary
        """
        # Aim for sustained P-core frequency with thermal headroom
        freq = 4.1e9  # 4.1 GHz sustained
        volt = self.estimate_voltage_for_frequency(CoreType.P_CORE, freq)
        power = self.calculate_cluster_power(CoreType.P_CORE, freq, 4, 85.0)

        return {
            "name": "Blue Team Detection Mode",
            "objective": "High-throughput detection, P-core prioritized",
            "cores": {
                "type": "P-cores prioritized",
                "count": 4,
                "frequency_hz": freq,
                "voltage_v": volt
            },
            "power": {
                "target_w": 20.0,
                "actual_w": power,
                "thermal_signature_w": power,
                "headroom_w": self.TDP_BOOST_W - power
            },
            "qos": {
                "class": "user_initiated",
                "level": QoSClass.USER_INITIATED.value
            },
            "taskpolicy": "sudo taskpolicy -B -p <pid>",
            "thermal_monitoring": "enabled",
            "validation": {
                "p_core_utilization_percent": [60, 100],
                "sustained_frequency_above_hz": 4.0e9,
                "power_within_budget": bool(power < 25.0),
                "detection_latency_ms": [1, 50]
            }
        }

    def capture_powermetrics(self, duration_seconds: int = 10) -> Optional[Dict]:
        """
        Capture real-time power metrics from macOS powermetrics tool.

        Args:
            duration_seconds: Duration to capture metrics

        Returns:
            Parsed powermetrics JSON or None if unavailable
        """
        try:
            result = subprocess.run(
                ['sudo', 'powermetrics', '-n', '1', '-i', str(duration_seconds * 1000),
                 '-s', 'cpu_power,gpu_power,thermal_pressure', '-f', 'json'],
                capture_output=True,
                text=True,
                timeout=duration_seconds + 5
            )

            if result.returncode == 0:
                return json.loads(result.stdout)
            else:
                print(f"powermetrics failed: {result.stderr}", file=sys.stderr)
                return None

        except subprocess.TimeoutExpired:
            print("powermetrics timed out", file=sys.stderr)
            return None
        except FileNotFoundError:
            print("powermetrics not found (requires macOS)", file=sys.stderr)
            return None
        except Exception as e:
            print(f"Error capturing powermetrics: {e}", file=sys.stderr)
            return None

    def print_power_table(self):
        """Print a table of power consumption at different frequencies."""
        print("=" * 80)
        print("Apple M5 Power Consumption Table (P = C × f × V²)")
        print("=" * 80)

        # P-cores
        print("\n--- P-Cores (4x Firestorm, 4.42 GHz max) ---")
        print(f"{'Frequency (GHz)':>15} {'Voltage (V)':>12} {'Power/Core (W)':>15} {'4-Core Total (W)':>18}")
        print("-" * 80)

        p_freqs = [1.26e9, 2.0e9, 3.0e9, 4.0e9, 4.1e9, 4.42e9]
        for freq in p_freqs:
            state = self.calculate_core_power(CoreType.P_CORE, freq, 100.0)
            total = state.power_w * 4
            print(f"{freq/1e9:>15.2f} {state.voltage_v:>12.2f} {state.power_w:>15.3f} {total:>18.3f}")

        # E-cores
        print("\n--- E-Cores (6x Icestorm, 2.85 GHz max) ---")
        print(f"{'Frequency (GHz)':>15} {'Voltage (V)':>12} {'Power/Core (W)':>15} {'6-Core Total (W)':>18}")
        print("-" * 80)

        e_freqs = [1.02e9, 1.5e9, 2.0e9, 2.5e9, 2.85e9]
        for freq in e_freqs:
            state = self.calculate_core_power(CoreType.E_CORE, freq, 100.0)
            total = state.power_w * 6
            print(f"{freq/1e9:>15.2f} {state.voltage_v:>12.2f} {state.power_w:>15.3f} {total:>18.3f}")

        print("\n" + "=" * 80)
        print(f"TDP Base: {self.TDP_BASE_W} W | TDP Boost: {self.TDP_BOOST_W} W")
        print(f"Thermal Throttle: {self.THERMAL_THROTTLE_CELSIUS}°C")
        print("=" * 80)

    def export_qigong_config(self, output_path: Path):
        """
        Export complete qigong configuration file.

        Args:
            output_path: Path to write JSON config
        """
        config = {
            "chip": "Apple M5",
            "red_team": self.generate_red_team_config(),
            "blue_team": self.generate_blue_team_config(),
            "qos_recommendations": self.generate_qos_recommendations(),
            "power_model": {
                "formula": "P = C × f × V²",
                "p_core_capacitance_f": self.P_CORE_CONFIG.capacitance_f,
                "e_core_capacitance_f": self.E_CORE_CONFIG.capacitance_f
            },
            "thermal": {
                "tdp_base_w": self.TDP_BASE_W,
                "tdp_boost_w": self.TDP_BOOST_W,
                "throttle_celsius": self.THERMAL_THROTTLE_CELSIUS,
                "max_junction_celsius": self.MAX_JUNCTION_CELSIUS
            }
        }

        with open(output_path, 'w') as f:
            json.dump(config, f, indent=2)

        print(f"[✓] Exported qigong config to: {output_path}")


def main():
    """CLI entry point"""
    import argparse

    parser = argparse.ArgumentParser(
        description="Apple M5 Power Model and qigong Configuration Generator"
    )
    parser.add_argument(
        '--config', type=Path,
        help='Path to M5 config JSON'
    )
    parser.add_argument(
        '--export', type=Path,
        help='Export qigong configuration to file'
    )
    parser.add_argument(
        '--table', action='store_true',
        help='Print power consumption table'
    )
    parser.add_argument(
        '--red-team', action='store_true',
        help='Print red team configuration'
    )
    parser.add_argument(
        '--blue-team', action='store_true',
        help='Print blue team configuration'
    )
    parser.add_argument(
        '--qos', action='store_true',
        help='Print QoS recommendations'
    )
    parser.add_argument(
        '--powermetrics', type=int, metavar='SECONDS',
        help='Capture powermetrics for specified duration'
    )

    args = parser.parse_args()

    # Initialize model
    model = M5PowerModel(config_path=args.config)

    # Print power table
    if args.table or len(sys.argv) == 1:
        model.print_power_table()

    # Red team config
    if args.red_team:
        print("\n" + "=" * 80)
        print("Red Team Configuration (Stealth Mode)")
        print("=" * 80)
        red_config = model.generate_red_team_config()
        print(json.dumps(red_config, indent=2))

    # Blue team config
    if args.blue_team:
        print("\n" + "=" * 80)
        print("Blue Team Configuration (Detection Mode)")
        print("=" * 80)
        blue_config = model.generate_blue_team_config()
        print(json.dumps(blue_config, indent=2))

    # QoS recommendations
    if args.qos:
        print("\n" + "=" * 80)
        print("QoS Class Recommendations")
        print("=" * 80)
        qos_recs = model.generate_qos_recommendations()
        print(json.dumps(qos_recs, indent=2))

    # Capture powermetrics
    if args.powermetrics:
        print(f"\n[*] Capturing powermetrics for {args.powermetrics} seconds...")
        metrics = model.capture_powermetrics(args.powermetrics)
        if metrics:
            print(json.dumps(metrics, indent=2))

    # Export config
    if args.export:
        model.export_qigong_config(args.export)


if __name__ == '__main__':
    main()
