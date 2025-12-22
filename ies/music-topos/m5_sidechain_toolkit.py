#!/usr/bin/env python3
"""
Apple M5 Side-Channel Fingerprinting Toolkit
Practical implementation for instruction-level power/thermal analysis

Usage:
  ./m5_sidechain_toolkit.py --mode realtime --duration 60
  ./m5_sidechain_toolkit.py --mode train --data traces.csv --model classifier.pkl
  ./m5_sidechain_toolkit.py --mode infer --model classifier.pkl --live
"""

import numpy as np
import subprocess
import json
import sys
import argparse
from datetime import datetime
from collections import defaultdict
import threading
import time
from dataclasses import dataclass, asdict
from typing import Dict, List, Tuple, Optional
import pickle

try:
    from sklearn.ensemble import RandomForestClassifier
    from sklearn.preprocessing import StandardScaler
    from scipy import signal, stats
    HAS_ML = True
except ImportError:
    HAS_ML = False
    print("Warning: scikit-learn not installed. ML features disabled.")

@dataclass
class SensorReading:
    """Single instantaneous reading from all M5 sensors"""
    timestamp: float
    power_watts: float  # Total system power
    die_temp_c: float
    cpu_e_power: float
    cpu_p_power: float
    gpu_power: float
    thermal_sensors: np.ndarray  # (24,) array of sensor readings

class M5PowerReader:
    """Low-level interface to M5 power/thermal sensors via macOS APIs"""

    def __init__(self, sampling_rate_hz=10):
        self.sampling_rate = sampling_rate_hz
        self.readings = []
        self.calibrated = False

    def read_single_sample(self) -> Optional[SensorReading]:
        """
        Read current power/thermal state from M5
        Requires: sudo powermetrics

        Returns: SensorReading or None if failed
        """
        try:
            result = subprocess.run(
                ['sudo', 'powermetrics', '-n', '1', '-s', 'power,thermal'],
                capture_output=True,
                text=True,
                timeout=5
            )

            if result.returncode != 0:
                return None

            lines = result.stdout.split('\n')
            reading = self._parse_powermetrics_output(lines)
            return reading

        except subprocess.TimeoutExpired:
            print("Error: powermetrics timeout")
            return None
        except PermissionError:
            print("Error: Requires sudo. Run: sudo ./m5_sidechain_toolkit.py ...")
            return None

    def _parse_powermetrics_output(self, lines: List[str]) -> SensorReading:
        """Parse powermetrics output into structured data"""
        data = {
            'timestamp': time.time(),
            'power_watts': 0.0,
            'die_temp_c': 0.0,
            'cpu_e_power': 0.0,
            'cpu_p_power': 0.0,
            'gpu_power': 0.0,
            'thermal_sensors': np.zeros(24)
        }

        for line in lines:
            if 'CPU Power' in line:
                try:
                    power_str = line.split(':')[1].strip().split()[0]
                    data['power_watts'] = float(power_str)
                except (IndexError, ValueError):
                    pass
            elif 'CPU E-Cluster Power' in line:
                try:
                    data['cpu_e_power'] = float(line.split(':')[1].split()[0])
                except (IndexError, ValueError):
                    pass
            elif 'CPU P-Cluster Power' in line:
                try:
                    data['cpu_p_power'] = float(line.split(':')[1].split()[0])
                except (IndexError, ValueError):
                    pass
            elif 'GPU Power' in line:
                try:
                    data['gpu_power'] = float(line.split(':')[1].split()[0])
                except (IndexError, ValueError):
                    pass
            elif 'cpu_die_temperature' in line:
                try:
                    temp_str = line.split(':')[1].strip().split()[0]
                    data['die_temp_c'] = float(temp_str)
                except (IndexError, ValueError):
                    pass
            elif 'thermal_pressure_percentage' in line:
                try:
                    # Distribute thermal load across 24 sensors
                    pressure = float(line.split(':')[1].split()[0]) / 100.0
                    # Sensor 0-3: P-cores, 4-7: more P-cores, 8-11: E-cores, 12-19: more E-cores, 20-23: GPU
                    data['thermal_sensors'] = np.full(24, data['die_temp_c'] * pressure + 25 * (1 - pressure))
                except (IndexError, ValueError):
                    pass

        return SensorReading(**data)

    def capture_trace(self, duration_sec: float) -> List[SensorReading]:
        """Capture continuous power/thermal trace for specified duration"""
        num_samples = int(duration_sec * self.sampling_rate)
        self.readings = []

        print(f"Capturing {num_samples} samples over {duration_sec}s at {self.sampling_rate}Hz...")

        for i in range(num_samples):
            reading = self.read_single_sample()
            if reading:
                self.readings.append(reading)
                if (i + 1) % max(1, num_samples // 10) == 0:
                    print(f"  {i + 1}/{num_samples} samples captured ({reading.die_temp_c:.1f}°C)")

            time.sleep(1.0 / self.sampling_rate)

        return self.readings

    def export_csv(self, filename: str):
        """Export captured readings to CSV for analysis"""
        import csv

        if not self.readings:
            print("No readings to export")
            return

        with open(filename, 'w') as f:
            writer = csv.DictWriter(f, fieldnames=[
                'timestamp', 'power_watts', 'die_temp_c',
                'cpu_e_power', 'cpu_p_power', 'gpu_power'
            ] + [f'sensor_{i}' for i in range(24)])

            writer.writeheader()

            for reading in self.readings:
                row = asdict(reading)
                # Flatten thermal_sensors array
                for i, val in enumerate(row['thermal_sensors']):
                    row[f'sensor_{i}'] = val
                row.pop('thermal_sensors')
                writer.writerow(row)

        print(f"Exported {len(self.readings)} readings to {filename}")


class DifferentialPowerAnalysis:
    """Classical DPA attack for instruction identification"""

    def __init__(self):
        self.instruction_signatures = {}

    def compute_differential_power(self, trace_a: np.ndarray, trace_b: np.ndarray) -> float:
        """
        Compute differential power between two traces
        Returns: Euclidean norm of (mean_a - mean_b)
        """
        mean_a = np.mean(trace_a)
        mean_b = np.mean(trace_b)

        return abs(mean_a - mean_b)

    def build_instruction_database(self, instruction_traces: Dict[str, np.ndarray]):
        """
        Build database of instruction power signatures
        Input: Dict mapping instruction name -> power trace (1D array)
        """
        for instr_name, trace in instruction_traces.items():
            self.instruction_signatures[instr_name] = {
                'mean_power': float(np.mean(trace)),
                'std_power': float(np.std(trace)),
                'peak_power': float(np.max(trace)),
                'min_power': float(np.min(trace)),
                'spectrum': self._compute_frequency_spectrum(trace)
            }

        print(f"Built database with {len(self.instruction_signatures)} instruction signatures")

    def _compute_frequency_spectrum(self, trace: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """Compute FFT spectrum of power trace"""
        fft = np.fft.fft(trace)
        frequencies = np.fft.fftfreq(len(trace))
        power = np.abs(fft) ** 2

        return {
            'frequencies': frequencies.tolist(),
            'power': power.tolist()
        }

    def identify_instruction(self, unknown_trace: np.ndarray) -> Dict:
        """
        Identify instruction from power trace using DPA
        """
        unknown_sig = {
            'mean_power': float(np.mean(unknown_trace)),
            'std_power': float(np.std(unknown_trace)),
            'peak_power': float(np.max(unknown_trace)),
            'min_power': float(np.min(unknown_trace)),
        }

        # Compute distances to all known instructions
        distances = {}
        for instr_name, known_sig in self.instruction_signatures.items():
            # Euclidean distance in signature space
            distance = np.sqrt(
                (unknown_sig['mean_power'] - known_sig['mean_power']) ** 2 +
                (unknown_sig['std_power'] - known_sig['std_power']) ** 2 +
                (unknown_sig['peak_power'] - known_sig['peak_power']) ** 2
            )
            distances[instr_name] = distance

        # Find closest match
        best_match = min(distances, key=distances.get)
        confidence = 1.0 / (1.0 + distances[best_match])

        return {
            'predicted_instruction': best_match,
            'confidence': float(confidence),
            'all_distances': {k: float(v) for k, v in distances.items()},
            'top_3': sorted(distances.items(), key=lambda x: x[1])[:3]
        }


class InstructionClassifier:
    """ML-based instruction classifier using power/thermal data"""

    def __init__(self):
        if not HAS_ML:
            raise RuntimeError("scikit-learn required. Install: pip install scikit-learn")

        self.model = RandomForestClassifier(n_estimators=100, random_state=42)
        self.scaler = StandardScaler()
        self.instruction_names = []
        self.trained = False

    def train(self, features: np.ndarray, labels: np.ndarray):
        """
        Train classifier
        features: shape (n_samples, n_features)
        labels: instruction class indices
        """
        # Normalize features
        features_scaled = self.scaler.fit_transform(features)

        # Train model
        self.model.fit(features_scaled, labels)
        self.trained = True

        print(f"Trained classifier on {len(features)} samples")

    def predict(self, feature_vector: np.ndarray) -> Dict:
        """
        Predict instruction from single feature vector
        """
        if not self.trained:
            raise RuntimeError("Model not trained. Call train() first.")

        feature_scaled = self.scaler.transform(feature_vector.reshape(1, -1))
        probabilities = self.model.predict_proba(feature_scaled)[0]

        top_3_idx = np.argsort(probabilities)[-3:][::-1]

        return {
            'predicted_instruction': self.instruction_names[top_3_idx[0]] if self.instruction_names else "Unknown",
            'confidence': float(probabilities[top_3_idx[0]]),
            'top_3': [
                (self.instruction_names[i] if self.instruction_names else f"Class_{i}", float(probabilities[i]))
                for i in top_3_idx
            ]
        }

    def save(self, filename: str):
        """Save trained model to disk"""
        with open(filename, 'wb') as f:
            pickle.dump({
                'model': self.model,
                'scaler': self.scaler,
                'instruction_names': self.instruction_names,
                'trained': self.trained
            }, f)
        print(f"Model saved to {filename}")

    def load(self, filename: str):
        """Load trained model from disk"""
        with open(filename, 'rb') as f:
            data = pickle.load(f)
            self.model = data['model']
            self.scaler = data['scaler']
            self.instruction_names = data['instruction_names']
            self.trained = data['trained']
        print(f"Model loaded from {filename}")


class RealTimeMonitor:
    """Real-time instruction fingerprinting with live display"""

    def __init__(self, classifier: Optional[InstructionClassifier] = None):
        self.classifier = classifier
        self.history = defaultdict(list)
        self.running = False

    def feature_extractor(self, readings: List[SensorReading]) -> np.ndarray:
        """
        Extract features from sensor readings for classification
        Returns: feature vector (1D array)
        """
        if not readings:
            return np.zeros(10)

        powers = np.array([r.power_watts for r in readings])
        temps = np.array([r.die_temp_c for r in readings])

        # Extract statistical features
        features = np.array([
            np.mean(powers),
            np.std(powers),
            np.max(powers),
            np.mean(temps),
            np.std(temps),
            np.max(temps),
            np.max(np.gradient(powers)),  # Rate of change
            np.max(np.gradient(temps)),
            len(readings),  # Number of samples (duration indicator)
            np.ptp(powers)  # Peak-to-peak power
        ])

        return features

    def monitor_live(self, duration_sec: float, interval_sec: float = 1.0):
        """
        Real-time monitoring with periodic classification
        """
        reader = M5PowerReader(sampling_rate_hz=10)
        num_intervals = int(duration_sec / interval_sec)

        print(f"Monitoring for {duration_sec}s (interval: {interval_sec}s)")
        print("-" * 80)

        for i in range(num_intervals):
            readings = reader.capture_trace(interval_sec)

            if readings:
                features = self.feature_extractor(readings)

                print(f"\n[{i+1}/{num_intervals}] {datetime.now().strftime('%H:%M:%S.%f')[:-3]}")
                print(f"  Power: {np.mean([r.power_watts for r in readings]):.2f}W")
                print(f"  Temp: {np.mean([r.die_temp_c for r in readings]):.1f}°C")

                if self.classifier and self.classifier.trained:
                    result = self.classifier.predict(features)
                    print(f"  Predicted: {result['predicted_instruction']} (confidence: {result['confidence']:.2f})")
                    print(f"  Top 3: {', '.join([f'{name}({conf:.2f})' for name, conf in result['top_3']])}")

                    # Store in history
                    self.history['instructions'].append(result['predicted_instruction'])
                    self.history['confidences'].append(result['confidence'])

        self._print_summary()

    def _print_summary(self):
        """Print summary of monitoring session"""
        print("\n" + "=" * 80)
        print("Summary:")
        if self.history['instructions']:
            from collections import Counter
            instruction_counts = Counter(self.history['instructions'])
            print(f"Most common instructions: {instruction_counts.most_common(3)}")
            print(f"Average confidence: {np.mean(self.history['confidences']):.2f}")


def main():
    parser = argparse.ArgumentParser(description="M5 Side-Channel Fingerprinting Toolkit")
    parser.add_argument('--mode', choices=['realtime', 'capture', 'analyze', 'train', 'infer'],
                       default='realtime', help='Operating mode')
    parser.add_argument('--duration', type=float, default=60, help='Capture duration (seconds)')
    parser.add_argument('--output', default='traces.csv', help='Output filename')
    parser.add_argument('--data', help='Input CSV file for analysis')
    parser.add_argument('--model', help='ML model file (.pkl)')
    parser.add_argument('--live', action='store_true', help='Live real-time mode')

    args = parser.parse_args()

    # Real-time monitoring mode
    if args.mode == 'realtime':
        print("=" * 80)
        print("M5 Side-Channel Real-Time Monitor")
        print("=" * 80)

        try:
            monitor = RealTimeMonitor()
            monitor.monitor_live(args.duration, interval_sec=1.0)
        except KeyboardInterrupt:
            print("\nMonitoring stopped by user")
            sys.exit(0)

    # Capture raw traces
    elif args.mode == 'capture':
        print("Capturing power/thermal traces...")
        reader = M5PowerReader(sampling_rate_hz=10)
        readings = reader.capture_trace(args.duration)
        reader.export_csv(args.output)
        print(f"✓ Captured {len(readings)} samples to {args.output}")

    # Analyze captured data
    elif args.mode == 'analyze':
        if not args.data:
            print("Error: --data required for analyze mode")
            sys.exit(1)

        import pandas as pd
        df = pd.read_csv(args.data)

        print(f"Analyzing {len(df)} readings from {args.data}")
        print(f"Power: {df['power_watts'].mean():.2f}W (±{df['power_watts'].std():.2f}W)")
        print(f"Temp: {df['die_temp_c'].mean():.1f}°C (±{df['die_temp_c'].std():.1f}°C)")
        print(f"Duration: {df['timestamp'].max() - df['timestamp'].min():.1f} seconds")

    # Train ML model
    elif args.mode == 'train':
        if not HAS_ML:
            print("Error: scikit-learn required for training")
            sys.exit(1)

        if not args.data:
            print("Error: --data required for train mode")
            sys.exit(1)

        print(f"Training classifier on {args.data}...")
        import pandas as pd

        df = pd.read_csv(args.data)
        # This is a placeholder - real training would need labeled data
        print("Note: Real training requires labeled instruction data")
        print("For now, demonstrating feature extraction...")

        # Extract features from CSV
        features = []
        for _, row in df.iterrows():
            feature = np.array([
                row['power_watts'],
                row['die_temp_c'],
                row['cpu_e_power'],
                row['cpu_p_power'],
                row['gpu_power']
            ])
            features.append(feature)

        features = np.array(features)
        print(f"Extracted {len(features)} feature vectors")
        print(f"Feature shape: {features[0].shape}")

    # Run inference
    elif args.mode == 'infer':
        if not args.model:
            print("Error: --model required for infer mode")
            sys.exit(1)

        print(f"Loading model from {args.model}...")
        classifier = InstructionClassifier()
        classifier.load(args.model)

        if args.live:
            monitor = RealTimeMonitor(classifier)
            monitor.monitor_live(args.duration)


if __name__ == '__main__':
    main()
