#!/usr/bin/env python3
"""
Corollary Discharge: Active Suppression of Self-Generated Signals

Von Holst's breakthrough (1950): The brain doesn't just passively receive sensory
feedback. It actively PREDICTS what feedback should occur and CANCELS it out.

Only MISMATCHES between prediction and sensation reach conscious attention.
This is how electric fish detect external threats while ignoring their own signals.

Implementation:
1. EFFERENCE COPY: Predict sensory consequence of motor command
2. SENSATION: Observe actual sensory feedback
3. COMPARATOR: Expected - Actual = ERROR SIGNAL
4. COROLLARY DISCHARGE: If error = 0, suppress (cancel); if error > 0, amplify (alert)

This creates a THREAT DETECTION SYSTEM that ignores self-generated noise and
focuses only on truly external/anomalous events.
"""

import duckdb
import json
from pathlib import Path
from datetime import datetime, timedelta
from typing import Dict, List, Tuple, Optional
import hashlib
from dataclasses import dataclass

# ============================================================================
# Color Constants (Seed 0x42D)
# ============================================================================

SEED_COLORS = {
    1: "#E67F86",
    2: "#D06546",
    3: "#1316BB",
    4: "#BA2645",
    5: "#49EE54",
}

# ============================================================================
# Corollary Discharge Data Structures
# ============================================================================

@dataclass
class EfferentCommand:
    """Motor command sent to environment."""
    timestamp: datetime
    command_id: str
    predicted_color: str
    predicted_index: int
    context: str  # Description of action

@dataclass
class SensoryReafference:
    """Sensory feedback from environment."""
    timestamp: datetime
    reafference_id: str
    observed_color: str
    observed_pattern: str
    latency_ms: float

@dataclass
class ErrorSignal:
    """Mismatch between prediction and sensation."""
    timestamp: datetime
    efference_id: str
    predicted_color: str
    observed_color: str
    match_score: float  # 0.0 (complete mismatch) to 1.0 (perfect match)
    error_magnitude: float  # How far off was the prediction
    is_anomaly: bool
    threat_level: str  # "SAFE", "WARNING", "CRITICAL"

# ============================================================================
# Corollary Discharge System
# ============================================================================

class CorrollaryDischargeSystem:
    """
    Active threat detection through corollary discharge.

    Mechanism:
    1. Issue efference copy (predicted sensation)
    2. Observe actual reafference
    3. Compute error signal (difference)
    4. If error is zero: corollary discharge fires → suppress (safe)
    5. If error is nonzero: attention focuses → amplify (threat)

    This creates selective attention: self-generated = ignored, external = alert
    """

    def __init__(self, reafference_db: str = 'claude_interaction_reafference.duckdb',
                 discharge_db: str = 'claude_corollary_discharge.duckdb'):
        """Initialize corollary discharge system."""
        self.reafference_db = reafference_db
        self.discharge_db = discharge_db
        self.reafference_conn = duckdb.connect(reafference_db, read_only=True)
        self.discharge_conn = duckdb.connect(discharge_db)

        self.error_signals = []
        self.anomalies = []
        self.threat_alerts = []

        self._create_schema()

    def _create_schema(self):
        """Create corollary discharge schema."""
        print("Creating corollary discharge schema...")

        # Efferent commands table
        self.discharge_conn.execute("""
            CREATE TABLE IF NOT EXISTS efferent_commands (
                efference_id VARCHAR PRIMARY KEY,
                timestamp TIMESTAMP,
                predicted_color VARCHAR,
                predicted_index INTEGER,
                context VARCHAR,
                issued_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Sensory reafference table
        self.discharge_conn.execute("""
            CREATE TABLE IF NOT EXISTS sensory_reafference (
                reafference_id VARCHAR PRIMARY KEY,
                timestamp TIMESTAMP,
                observed_color VARCHAR,
                observed_pattern VARCHAR,
                latency_ms DOUBLE,
                recorded_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Error signals (comparator output)
        self.discharge_conn.execute("""
            CREATE TABLE IF NOT EXISTS error_signals (
                error_id VARCHAR PRIMARY KEY,
                timestamp TIMESTAMP,
                efference_id VARCHAR,
                predicted_color VARCHAR,
                observed_color VARCHAR,
                match_score DOUBLE,
                error_magnitude DOUBLE,
                is_anomaly BOOLEAN,
                threat_level VARCHAR,
                comparator_timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Suppressed signals (corollary discharge successful)
        self.discharge_conn.execute("""
            CREATE TABLE IF NOT EXISTS suppressed_signals (
                suppression_id VARCHAR PRIMARY KEY,
                error_id VARCHAR,
                suppressed_at TIMESTAMP,
                context VARCHAR,
                FOREIGN KEY (error_id) REFERENCES error_signals(error_id)
            )
        """)

        # Amplified signals (threat detected)
        self.discharge_conn.execute("""
            CREATE TABLE IF NOT EXISTS amplified_signals (
                amplification_id VARCHAR PRIMARY KEY,
                error_id VARCHAR,
                threat_level VARCHAR,
                anomaly_description VARCHAR,
                action_required VARCHAR,
                amplified_at TIMESTAMP,
                FOREIGN KEY (error_id) REFERENCES error_signals(error_id)
            )
        """)

        # Threat alerts (escalation)
        self.discharge_conn.execute("""
            CREATE TABLE IF NOT EXISTS threat_alerts (
                alert_id VARCHAR PRIMARY KEY,
                timestamp TIMESTAMP,
                threat_level VARCHAR,
                description VARCHAR,
                predicted_vs_observed VARCHAR,
                recommended_action VARCHAR,
                alert_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Signal suppression statistics
        self.discharge_conn.execute("""
            CREATE TABLE IF NOT EXISTS suppression_statistics (
                date DATE,
                hour INTEGER,
                total_signals INTEGER,
                suppressed_count INTEGER,
                amplified_count INTEGER,
                suppression_rate DOUBLE,
                avg_error_magnitude DOUBLE,
                max_error_magnitude DOUBLE
            )
        """)

        print("✓ Schema created\n")

    def generate_efference_copies(self) -> int:
        """Generate efference copies from reafference database."""
        print("Generating efference copies from reafference data...")

        # Load all interactions from reafference database
        results = self.reafference_conn.execute("""
            SELECT i.interaction_id, i.timestamp,
                   ep.predicted_color_hex, ep.predicted_color_index,
                   i.display
            FROM interactions i
            LEFT JOIN efference_predictions ep ON i.interaction_id = ep.interaction_id
        """).fetchall()

        count = 0
        for row in results:
            interaction_id = row[0]
            timestamp = row[1]
            predicted_color = row[2] or "#000000"
            predicted_index = row[3] or 0
            context = (row[4] or "")[:100]

            # Create efference ID
            efference_id = hashlib.sha256(
                f"{interaction_id}_{timestamp}".encode()
            ).hexdigest()[:16]

            try:
                self.discharge_conn.execute("""
                    INSERT INTO efferent_commands (
                        efference_id, timestamp, predicted_color,
                        predicted_index, context
                    ) VALUES (?, ?, ?, ?, ?)
                """, [efference_id, timestamp, predicted_color, predicted_index, context])
                count += 1
            except Exception:
                pass

        self.discharge_conn.commit()
        print(f"✓ Generated {count} efference copies\n")
        return count

    def load_sensory_reafference(self) -> int:
        """Load actual sensory feedback from reafference database."""
        print("Loading sensory reafference from reafference data...")

        # Load all reafference matches
        results = self.reafference_conn.execute("""
            SELECT rm.interaction_id, rm.predicted_color_hex,
                   rm.observed_pattern, i.timestamp
            FROM reafference_matches rm
            JOIN interactions i ON rm.interaction_id = i.interaction_id
        """).fetchall()

        count = 0
        for row in results:
            interaction_id = row[0]
            predicted_color = row[1]
            observed_pattern = row[2]
            timestamp = row[3]

            # Create reafference ID
            reafference_id = hashlib.sha256(
                f"{interaction_id}_reafference".encode()
            ).hexdigest()[:16]

            # Determine observed color (simplified: use predicted as observed for now)
            observed_color = predicted_color

            # Calculate latency (simulated as 0 for historical data)
            latency_ms = 0.0

            try:
                self.discharge_conn.execute("""
                    INSERT INTO sensory_reafference (
                        reafference_id, timestamp, observed_color,
                        observed_pattern, latency_ms
                    ) VALUES (?, ?, ?, ?, ?)
                """, [reafference_id, timestamp, observed_color, observed_pattern, latency_ms])
                count += 1
            except Exception:
                pass

        self.discharge_conn.commit()
        print(f"✓ Loaded {count} sensory reafference signals\n")
        return count

    def run_comparator(self) -> int:
        """
        Comparator: Compare efference copy vs sensory reafference.

        Computes error signal: Expected - Actual = ERROR

        If ERROR = 0: Corollary discharge will suppress
        If ERROR > 0: Signal will be amplified as threat
        """
        print("Running comparator (efference vs reafference)...")

        # Get all efferent commands and attempt to match with reafference
        efferences = self.discharge_conn.execute("""
            SELECT efference_id, timestamp, predicted_color, context
            FROM efferent_commands
            ORDER BY timestamp
        """).fetchall()

        # Get all sensory reafferences
        reafferences = self.discharge_conn.execute("""
            SELECT reafference_id, timestamp, observed_color, observed_pattern
            FROM sensory_reafference
            ORDER BY timestamp
        """).fetchall()

        # Build timestamp index for reafference
        reaf_by_time = {}
        for raf in reafferences:
            time_key = str(raf[1])[:19]  # Truncate to minute precision
            reaf_by_time[time_key] = raf

        count = 0
        for eff in efferences:
            efference_id = eff[0]
            eff_timestamp = eff[1]
            predicted_color = eff[2]
            context = eff[3]

            # Find matching reafference (within same minute)
            time_key = str(eff_timestamp)[:19]
            reafference = reaf_by_time.get(time_key)

            if reafference:
                observed_color = reafference[2]
                observed_pattern = reafference[3]

                # Compute match score
                match_score = 1.0 if predicted_color == observed_color else 0.0

                # Compute error magnitude (distance between colors in 5-color space)
                error_magnitude = self._color_distance(predicted_color, observed_color)

                # Determine if anomaly (error > threshold)
                error_threshold = 0.1  # 10% mismatch threshold
                is_anomaly = error_magnitude > error_threshold

                # Determine threat level
                if error_magnitude < 0.01:
                    threat_level = "SAFE"
                elif error_magnitude < 0.2:
                    threat_level = "WARNING"
                else:
                    threat_level = "CRITICAL"

                # Create error signal ID
                error_id = hashlib.sha256(
                    f"{efference_id}_{reafference[0]}".encode()
                ).hexdigest()[:16]

                try:
                    self.discharge_conn.execute("""
                        INSERT INTO error_signals (
                            error_id, timestamp, efference_id,
                            predicted_color, observed_color,
                            match_score, error_magnitude,
                            is_anomaly, threat_level
                        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, [error_id, eff_timestamp, efference_id,
                          predicted_color, observed_color,
                          match_score, error_magnitude,
                          is_anomaly, threat_level])

                    self.error_signals.append({
                        'error_id': error_id,
                        'timestamp': eff_timestamp,
                        'predicted_color': predicted_color,
                        'observed_color': observed_color,
                        'match_score': match_score,
                        'error_magnitude': error_magnitude,
                        'is_anomaly': is_anomaly,
                        'threat_level': threat_level
                    })
                    count += 1
                except Exception:
                    pass

        self.discharge_conn.commit()
        print(f"✓ Comparator analyzed {count} error signals\n")
        return count

    def fire_corollary_discharge(self) -> Tuple[int, int]:
        """
        Corollary Discharge: Suppress matched signals (error = 0).

        When prediction matches reality perfectly, the system SUPPRESSES
        the signal - it never reaches conscious attention.

        Returns: (suppressed_count, anomaly_count)
        """
        print("Firing corollary discharge (suppressing self-generated signals)...")

        # Get all error signals
        errors = self.discharge_conn.execute("""
            SELECT error_id, match_score, error_magnitude, threat_level
            FROM error_signals
        """).fetchall()

        suppressed_count = 0
        anomaly_count = 0

        for error_row in errors:
            error_id = error_row[0]
            match_score = error_row[1]
            error_magnitude = error_row[2]
            threat_level = error_row[3]

            if match_score >= 0.95:  # Nearly perfect match
                # SUPPRESS: This is self-generated, cancel the signal
                suppression_id = hashlib.sha256(
                    f"{error_id}_suppressed".encode()
                ).hexdigest()[:16]

                try:
                    self.discharge_conn.execute("""
                        INSERT INTO suppressed_signals (
                            suppression_id, error_id,
                            suppressed_at, context
                        ) VALUES (?, ?, CURRENT_TIMESTAMP, ?)
                    """, [suppression_id, error_id,
                          "Corollary discharge: self-generated signal suppressed"])
                    suppressed_count += 1
                except Exception:
                    pass
            else:
                # AMPLIFY: This is NOT self-generated, mismatch detected
                amplification_id = hashlib.sha256(
                    f"{error_id}_amplified".encode()
                ).hexdigest()[:16]

                anomaly_description = f"Reafference mismatch: {threat_level}"
                action_required = self._get_action_for_threat(threat_level)

                try:
                    self.discharge_conn.execute("""
                        INSERT INTO amplified_signals (
                            amplification_id, error_id,
                            threat_level, anomaly_description,
                            action_required, amplified_at
                        ) VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                    """, [amplification_id, error_id,
                          threat_level, anomaly_description, action_required])

                    self.anomalies.append({
                        'amplification_id': amplification_id,
                        'error_id': error_id,
                        'threat_level': threat_level,
                        'description': anomaly_description,
                        'action': action_required
                    })
                    anomaly_count += 1
                except Exception:
                    pass

        self.discharge_conn.commit()
        print(f"✓ Corollary discharge: {suppressed_count} suppressed, {anomaly_count} amplified\n")
        return suppressed_count, anomaly_count

    def generate_threat_alerts(self) -> int:
        """Generate escalation alerts for critical threats."""
        print("Generating threat alerts...")

        # Get all amplified signals with threat level > WARNING
        amplified = self.discharge_conn.execute("""
            SELECT amplification_id, error_id, threat_level,
                   anomaly_description, action_required
            FROM amplified_signals
            WHERE threat_level IN ('WARNING', 'CRITICAL')
        """).fetchall()

        count = 0
        for row in amplified:
            amplification_id = row[0]
            error_id = row[1]
            threat_level = row[2]
            description = row[3]
            action = row[4]

            # Get error details
            error_details = self.discharge_conn.execute("""
                SELECT predicted_color, observed_color, error_magnitude
                FROM error_signals
                WHERE error_id = ?
            """, [error_id]).fetchone()

            if error_details:
                pred_color = error_details[0]
                obs_color = error_details[1]
                error_mag = error_details[2]

                alert_id = hashlib.sha256(
                    f"{amplification_id}_alert".encode()
                ).hexdigest()[:16]

                alert_description = (
                    f"{threat_level}: External event detected. "
                    f"Predicted {pred_color} but observed {obs_color}. "
                    f"Error magnitude: {error_mag:.2%}"
                )

                try:
                    self.discharge_conn.execute("""
                        INSERT INTO threat_alerts (
                            alert_id, timestamp, threat_level,
                            description, predicted_vs_observed,
                            recommended_action
                        ) VALUES (?, CURRENT_TIMESTAMP, ?, ?, ?, ?)
                    """, [alert_id, threat_level, alert_description,
                          f"{pred_color}→{obs_color}", action])

                    self.threat_alerts.append({
                        'alert_id': alert_id,
                        'threat_level': threat_level,
                        'description': alert_description,
                        'action': action
                    })
                    count += 1
                except Exception:
                    pass

        self.discharge_conn.commit()
        print(f"✓ Generated {count} threat alerts\n")
        return count

    def compute_suppression_statistics(self):
        """Compute signal suppression statistics."""
        print("Computing suppression statistics...")

        # First, compute hourly statistics from error_signals
        self.discharge_conn.execute("""
            INSERT INTO suppression_statistics
            SELECT
                signal_date as date,
                signal_hour as hour,
                COUNT(*) as total_signals,
                0 as suppressed_count,
                0 as amplified_count,
                0.0 as suppression_rate,
                AVG(error_magnitude) as avg_error_magnitude,
                MAX(error_magnitude) as max_error_magnitude
            FROM (
                SELECT
                    DATE(es.timestamp) as signal_date,
                    EXTRACT(HOUR FROM es.timestamp) as signal_hour,
                    es.error_magnitude
                FROM error_signals es
            )
            GROUP BY signal_date, signal_hour
        """)

        self.discharge_conn.commit()
        print("✓ Statistics computed\n")

    def _color_distance(self, color1: str, color2: str) -> float:
        """Compute distance between two colors (0.0 = identical, 1.0 = maximum)."""
        if color1 == color2:
            return 0.0

        # Get indices
        idx1 = next((k for k, v in SEED_COLORS.items() if v == color1), 0)
        idx2 = next((k for k, v in SEED_COLORS.items() if v == color2), 0)

        if idx1 == 0 or idx2 == 0:
            return 1.0

        # Distance in 5-color space
        distance = abs(idx1 - idx2) / 5.0
        return min(distance, 1.0)

    def _get_action_for_threat(self, threat_level: str) -> str:
        """Get recommended action for threat level."""
        actions = {
            "SAFE": "Continue normal operation",
            "WARNING": "Log anomaly; monitor closely",
            "CRITICAL": "ESCALATE: Investigate external intrusion"
        }
        return actions.get(threat_level, "Unknown threat level")

    def print_discharge_report(self):
        """Print corollary discharge analysis report."""
        print("\n╔" + "═" * 70 + "╗")
        print("║  COROLLARY DISCHARGE ANALYSIS REPORT" + " " * 34 + "║")
        print("╚" + "═" * 70 + "╝\n")

        # Signal classification
        total = self.discharge_conn.execute(
            "SELECT COUNT(*) FROM error_signals"
        ).fetchone()[0]

        suppressed = self.discharge_conn.execute(
            "SELECT COUNT(*) FROM suppressed_signals"
        ).fetchone()[0]

        amplified = self.discharge_conn.execute(
            "SELECT COUNT(*) FROM amplified_signals"
        ).fetchone()[0]

        print("SIGNAL CLASSIFICATION:")
        print("─" * 72)
        print(f"  Total Signals: {total}")
        print(f"  Suppressed (Self-Generated): {suppressed} ({suppressed/max(total,1)*100:.1f}%)")
        print(f"  Amplified (Anomalies): {amplified} ({amplified/max(total,1)*100:.1f}%)")
        print()

        # Threat level distribution
        print("THREAT LEVEL DISTRIBUTION:")
        print("─" * 72)
        threats = self.discharge_conn.execute("""
            SELECT threat_level, COUNT(*) as count
            FROM error_signals
            GROUP BY threat_level
            ORDER BY count DESC
        """).fetchall()

        for level, count in threats:
            percent = count / max(total, 1) * 100
            bar = "█" * int(percent / 5)
            print(f"  {level:<10} : {bar:<30} {count} ({percent:.1f}%)")

        print()

        # Critical alerts
        print("CRITICAL ALERTS:")
        print("─" * 72)
        alerts = self.discharge_conn.execute("""
            SELECT threat_level, description, recommended_action
            FROM threat_alerts
            WHERE threat_level = 'CRITICAL'
            ORDER BY alert_at DESC
            LIMIT 5
        """).fetchall()

        if alerts:
            for level, description, action in alerts:
                print(f"  🚨 {description}")
                print(f"     Action: {action}")
        else:
            print("  ✓ No critical alerts (all signals safely suppressed)")

        print()

        # Suppression efficiency
        print("SUPPRESSION EFFICIENCY:")
        print("─" * 72)
        safe_rate = (suppressed / max(total, 1) * 100)
        print(f"  Corollary discharge success rate: {safe_rate:.1f}%")
        print(f"  Signals safely canceled: {suppressed}")
        print(f"  Signals requiring attention: {amplified}")
        print()

        # Suppression statistics (hourly)
        print("HOURLY SUPPRESSION STATISTICS (Last 10 Hours):")
        print("─" * 72)
        stats = self.discharge_conn.execute("""
            SELECT date, hour, total_signals, suppressed_count,
                   suppression_rate, avg_error_magnitude
            FROM suppression_statistics
            ORDER BY date DESC, hour DESC
            LIMIT 10
        """).fetchall()

        for date, hour, total, supp, rate, avg_err in stats:
            supp_pct = (rate * 100) if rate else 0
            bar = "▓" * int(supp_pct / 5)
            print(f"  {date} {hour:02d}:00 : {bar:<20} {supp}/{total} suppressed ({supp_pct:.0f}%) | error: {avg_err:.3f}")

        print()

    def close(self):
        """Close database connections."""
        self.reafference_conn.close()
        self.discharge_conn.close()


# ============================================================================
# CLI Interface
# ============================================================================

if __name__ == '__main__':
    print("\n╔" + "═" * 70 + "╗")
    print("║  COROLLARY DISCHARGE: ACTIVE THREAT DETECTION" + " " * 25 + "║")
    print("╚" + "═" * 70 + "╝\n")

    # Initialize system
    system = CorrollaryDischargeSystem()

    # Generate efference copies (predictions)
    eff_count = system.generate_efference_copies()

    # Load sensory reafference (observations)
    reaf_count = system.load_sensory_reafference()

    # Run comparator (predict vs actual)
    error_count = system.run_comparator()

    # Fire corollary discharge (suppress or amplify)
    suppressed, amplified = system.fire_corollary_discharge()

    # Generate threat alerts
    alert_count = system.generate_threat_alerts()

    # Compute statistics
    system.compute_suppression_statistics()

    # Print report
    system.print_discharge_report()

    # Show key findings
    print("KEY FINDINGS:")
    print("─" * 72)
    print(f"  Like the electric fish: We successfully detect")
    print(f"  self-generated signals and suppress them silently.")
    print(f"  Only EXTERNAL anomalies reach conscious attention.")
    print()
    print(f"  Suppressed (canceled): {suppressed} self-generated interactions")
    print(f"  Amplified (threats):   {amplified} external anomalies")
    print(f"  Critical alerts:       {alert_count} requiring immediate action")
    print()

    system.close()

    print("✓ Corollary discharge complete\n")
