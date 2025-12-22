# Genesis Week 1: Deployment Checklist

**Timeline**: Monday-Friday, Week 1
**Goal**: Collect complete multimodal data from 50 M5 participants
**Framework**: Wavelet Verification Pipeline (M5 optimized)
**Current Date**: December 22, 2025
**Start Date**: December 23, 2025 (Week 1 begins)

---

## PRE-WEEK PREPARATION (December 22-23)

### System Validation ✓

- [ ] **Test M5 Hardware Access**
  ```bash
  # Verify powermetrics available
  which powermetrics

  # If not found:
  brew install powermetrics

  # Test execution (requires sudo)
  sudo powermetrics -n 1 | head -5
  ```

- [ ] **Test Keystroke Event Tap**
  ```bash
  # Verify PyObjC installed
  python3 -c "from Quartz import CGEventTapCreate; print('✓ OK')"

  # If ImportError:
  pip install pyobjc-framework-Quartz
  ```

- [ ] **Test HDF5 Storage**
  ```bash
  python3 -c "import h5py; print('✓ OK')"

  # If ImportError:
  pip install h5py
  ```

- [ ] **Accessibility Permissions (macOS)**
  - Open System Preferences → Security & Privacy → Accessibility
  - Drag Terminal.app into allowed apps list
  - Or drag Python interpreter: `/usr/local/bin/python3`
  - Verify with test: `python3 m5_real_data_collector.py P_TEST --duration 10`

### Code Preparation ✓

- [ ] **Save m5_real_data_collector.py**
  - Location: `/Users/bob/ies/music-topos/m5_real_data_collector.py`
  - Permissions: `chmod +x m5_real_data_collector.py`

- [ ] **Update wavelet_verification_pipeline.py** to support real data:
  - Add import: `from m5_real_data_collector import M5RealDataCollector`
  - Add method to MultimodalDataCollector:
    ```python
    @staticmethod
    def from_real_hardware(user_id: str, duration_seconds: int = 1800):
        """Collect data from real M5 hardware"""
        collector = M5RealDataCollector(duration_seconds=duration_seconds)
        genesis_data = collector.collect_genesis(user_id)
        return genesis_data
    ```

- [ ] **Create results directory**
  ```bash
  mkdir -p genesis_data
  mkdir -p results
  mkdir -p figures
  ```

- [ ] **Create participant tracking spreadsheet**
  - Column headers: ID, DateTime, Condition, Duration, Status, Notes
  - File: `GENESIS_COLLECTION_LOG.csv`

### Documentation ✓

- [ ] **Participant Consent Form**
  - [NEEDS INSTITUTIONAL APPROVAL]
  - Disclose: Power/thermal/keystroke monitoring
  - Disclose: Data retention (12 months)
  - Allow opt-out at any time
  - File: `PARTICIPANT_CONSENT.pdf`

- [ ] **Task Instructions** (printed for participants)
  - Email task (5 min)
  - Code task (5 min)
  - Analysis task (5 min)
  - File task (5 min)
  - Rest period
  - File: `TASK_INSTRUCTIONS.txt`

- [ ] **Troubleshooting Guide** (for experimenters)
  - Printed copies of common issues
  - File: See M5_HARDWARE_INTEGRATION_GUIDE.md

### Participant Recruitment ✓

- [ ] **Recruitment Target**: 50 participants
  - Split: 25 aware + 25 unaware conditions
  - Screening: M5 Mac required
  - Screening: English speaking
  - Screening: No accessibility software running

- [ ] **Recruitment Channels**
  - [ ] Email to computer science department
  - [ ] Campus bulletin boards
  - [ ] Online research recruitment portal
  - [ ] Personal network (if approved by IRB)

- [ ] **Schedule Participants**
  - Goal: 8-10 per day over 5-6 days
  - Book 45-min slots (prep + 30 min collection + wrap-up)
  - Spreadsheet: `PARTICIPANT_SCHEDULE.csv`
  - Columns: Time, User ID, Status (scheduled/completed/failed)

---

## WEEK 1 DAILY SCHEDULE

### Day 1 (Monday) - Baseline & System Test

**Morning (8:00-10:00)**

- [ ] **System Final Check**
  ```bash
  # Run baseline collection with no participant (system test)
  python3 m5_real_data_collector.py BASELINE_SYSTEM --duration 300 --output-dir genesis_data

  # Verify output
  ls -lh genesis_data/
  ```

- [ ] **Expected**: 50 MB HDF5 file with all power/thermal/keystroke data

**Afternoon (13:00-17:00)**

- [ ] **Participant 1 & 2 (Aware Condition)**
  - Get consent signature
  - Explain task instructions
  - Run: `python3 m5_real_data_collector.py P001 --condition aware --output-dir genesis_data`
  - Monitor collection on secondary screen
  - Repeat for P002

- [ ] **Data Quality Check After Each Session**
  ```bash
  python3 << 'EOF'
  from m5_real_data_collector import M5RealDataCollector
  data = M5RealDataCollector.load_from_hdf5('genesis_data/genesis_P001.h5')
  print(f"Power samples: {len(data['power_cpu'])}")
  print(f"Keystroke events: {data['metadata']['keystroke_events']}")
  print(f"Keystroke entropy: {data['keystroke_entropy']:.2f}")
  EOF
  ```

- [ ] **Log Results**
  - Entry: `P001, 13:00, aware, 1800s, PASS, [notes]`
  - File: `GENESIS_COLLECTION_LOG.csv`

**Evening (17:00-18:00)**

- [ ] **Backup Data**
  ```bash
  cp -r genesis_data ~/backup/genesis_data_day1_$(date +%Y%m%d)
  ```

- [ ] **Update Progress**
  - Completed: 2/50 (4%)
  - Next: Participants 3-4 tomorrow

---

### Day 2 (Tuesday) - Ramp Up to Parallel Sessions

**Morning (9:00-12:00)**

- [ ] **Participants 3-6 (Mixed Conditions)**
  - Alternate: 3 (unaware), 4 (aware), 5 (unaware), 6 (aware)
  - Check data quality after each
  - Log in spreadsheet

**Afternoon (13:00-17:00)**

- [ ] **Participants 7-10 (Continue Alternation)**

**Evening (17:00-18:00)**

- [ ] **Data Quality Report**
  ```python
  # Script to generate quality report
  import pandas as pd
  import glob

  quality = []
  for h5_file in glob.glob('genesis_data/genesis_P*.h5'):
      data = M5RealDataCollector.load_from_hdf5(h5_file)
      quality.append({
          'user': data['metadata']['user_id'],
          'power_samples': len(data['power_cpu']),
          'keystroke_events': data['metadata']['keystroke_events'],
          'entropy': data['keystroke_entropy'],
          'status': 'OK' if data['metadata']['keystroke_events'] > 100 else 'LOW'
      })

  df = pd.DataFrame(quality)
  df.to_csv('DATA_QUALITY_DAY2.csv', index=False)
  print(df)
  ```

- [ ] **Backup Data**
  - Completed: 10/50 (20%)

---

### Days 3-5 (Wednesday-Friday) - Full Scale

**Daily Pattern:**

| Time | Activity | Notes |
|------|----------|-------|
| 8:00-8:30 | System check | Verify powermetrics, temp sensors |
| 8:30-9:00 | Prep session | Print task instructions, consent forms |
| 9:00-17:00 | Collect data | 8-10 participants per day |
| 17:00-18:00 | QA & backup | Check quality, backup data |
| 18:00+ | Admin | Update logs, fix issues |

**Target Completion:**
- Day 3: 10 more (total 20/50 = 40%)
- Day 4: 15 more (total 35/50 = 70%)
- Day 5: 15 more (total 50/50 = 100%)

**For Each Participant Session:**

```bash
# 1. Pre-session (5 min)
echo "P045: Starting collection at $(date)"
read -p "Condition? (aware/unaware) " CONDITION

# 2. Run collection (30 min)
python3 m5_real_data_collector.py P045 \
  --condition $CONDITION \
  --duration 1800 \
  --output-dir genesis_data

# 3. Quick QA (2 min)
python3 -c "
from m5_real_data_collector import M5RealDataCollector
data = M5RealDataCollector.load_from_hdf5('genesis_data/genesis_P045.h5')
print(f'Status: {'PASS' if data['metadata']['keystroke_events'] > 100 else 'WARN'}')
print(f'Samples: {len(data[\"power_cpu\"])}')
"

# 4. Log result (1 min)
echo "P045,$(date),${CONDITION},1800,PASS" >> GENESIS_COLLECTION_LOG.csv
```

---

## CONTINGENCY PROCEDURES

### If Collection Fails (Zero Data)

**Likely Cause**: Accessibility permission not granted
**Fix**:
```bash
# 1. Grant accessibility permission
# System Prefs → Security & Privacy → Accessibility
# Add Terminal or Python

# 2. Retry collection with verbose output
python3 m5_real_data_collector.py PXXX --duration 60 --verbose

# 3. Check powermetrics directly
sudo powermetrics -n 1 | jq '.processor'
```

**Action**: Retry with same participant (max 2 retries)

### If Keystroke Count is Zero

**Likely Cause**: Event tap not activated in time, or Caps Lock interfering
**Fix**:
1. Start script BEFORE participant starts typing
2. Ensure Caps Lock is OFF
3. Extend collection period to ensure keystroke capture

**Action**: Retry session

### If Thermal Sensors Show No Variance

**Likely Cause**: M5 in extreme idle (all cores cold)
**Fix**:
1. Run CPU-intensive task during collection
2. Or extend collection until natural heating occurs
3. Check that thermal_group directory exists: `/sys/class/thermal/`

**Action**: Retry with CPU load in background

### If Data File Exceeds 500 MB

**Likely Cause**: Thermal sensors sampling too fast
**Check**:
```bash
ls -lh genesis_data/genesis_PXXX.h5
# Should be ~50 MB for 30 min
# If >200 MB: investigate powermetrics sampling rate
```

**Action**: Check powermetrics configuration, may need to adjust sample_interval_ms

---

## END OF WEEK SUMMARY

### Friday Evening Checklist

- [ ] **Confirm All 50 Participants Collected**
  ```bash
  ls -1 genesis_data/genesis_P*.h5 | wc -l
  # Should output: 50
  ```

- [ ] **Generate Final Quality Report**
  ```python
  # See script above - generate comprehensive CSV with all metrics
  ```

- [ ] **Backup All Data**
  ```bash
  # Backup to external drive
  cp -r genesis_data /Volumes/BACKUP_DRIVE/genesis_data_complete_$(date +%Y%m%d)

  # Verify
  ls -1 /Volumes/BACKUP_DRIVE/genesis_data_complete_*/genesis_P*.h5 | wc -l
  ```

- [ ] **Document Any Issues**
  - File: `GENESIS_ISSUES_LOG.md`
  - Include: Which participants had issues, what fixes were applied

- [ ] **Archive Participant Metadata**
  - File: `PARTICIPANT_DATA_COMPLETE.csv`
  - Columns: ID, DateTime, Condition (aware/unaware), Duration, Status

### Status at Week 1 End

✓ **Genesis Phase Complete** when:
- [ ] 50 participants successfully collected
- [ ] All data stored in genesis_data/ directory
- [ ] Quality report shows acceptable metrics for all users
- [ ] Full backup created on external media
- [ ] Ready to proceed to Week 2 (Wavelet Analysis)

---

## WEEK 2 INITIALIZATION (Ready by Monday)

Once Genesis data is complete, prepare for wavelet decomposition:

```bash
# 1. Verify all files exist
python3 << 'EOF'
import glob
files = glob.glob('genesis_data/genesis_P*.h5')
print(f"Found {len(files)} Genesis files")
for f in sorted(files)[:5]:
    print(f"  {f}")
print("  ...")
EOF

# 2. Initialize results directory for Week 2
mkdir -p results/scales
mkdir -p results/classifiers
mkdir -p results/figures

# 3. Update wavelet_verification_pipeline.py to run on real data:
# (Already included in previous implementation)

# 4. Run first user as test
python3 << 'EOF'
from wavelet_verification_pipeline import VerificationFramework
from m5_real_data_collector import M5RealDataCollector

# Load P001 real data
genesis_data = M5RealDataCollector.load_from_hdf5('genesis_data/genesis_P001.h5')

# Run wavelet decomposition
framework = VerificationFramework()
results = framework.run_wavelet_decomposition(genesis_data)

print("✓ Wavelet decomposition successful on real data")
EOF
```

---

## Files and Logs to Maintain

**Daily Files**:
- `GENESIS_COLLECTION_LOG.csv` - Running log of all collections
- `DATA_QUALITY_DAYX.csv` - Daily quality metrics
- `GENESIS_ISSUES_LOG.md` - Problems and fixes applied

**Final Files** (End of Week):
- `PARTICIPANT_DATA_COMPLETE.csv` - Final metadata for all 50
- `GENESIS_DATA_QUALITY_FINAL_REPORT.csv` - Comprehensive metrics
- `GENESIS_WEEK1_SUMMARY.md` - Written summary of week

**Backup**:
- External drive: Complete mirror of `genesis_data/` directory
- Cloud storage (optional): Encrypted backup of critical files

---

## Success Metrics for Week 1

| Metric | Target | Status |
|--------|--------|--------|
| Participants collected | 50 | TBD |
| Data quality pass rate | ≥95% | TBD |
| Average keystroke entropy | 5.5 ± 0.5 bits | TBD |
| Average power samples | ~18,000 | TBD |
| Thermal sensor integrity | All 24 functional | TBD |
| Total data volume | ~2.5 GB | TBD |
| Backup completion | 100% redundancy | TBD |

---

## Quick Command Reference

```bash
# Start collection for participant P045, unaware condition
python3 m5_real_data_collector.py P045 --condition unaware --output-dir genesis_data

# Quick quality check
python3 -c "
from m5_real_data_collector import M5RealDataCollector
data = M5RealDataCollector.load_from_hdf5('genesis_data/genesis_P045.h5')
print(f\"Status: {'PASS' if data['metadata']['keystroke_events'] > 100 else 'FAIL'}\")
print(f\"Power: {len(data['power_cpu'])} samples\")
print(f\"Entropy: {data['keystroke_entropy']:.2f} bits\")
"

# Count completed participants
ls -1 genesis_data/genesis_P*.h5 | wc -l

# Backup everything
cp -r genesis_data ~/backup/genesis_data_$(date +%Y%m%d_%H%M%S)

# Verify backup integrity
diff -r genesis_data ~/backup/genesis_data_20251223_093000/ | wc -l
# Should be 0 differences
```

---

## CRITICAL SAFETY CHECKS

⚠️ **Before Starting Each Day**:

1. **Verify backup exists from previous day**
   ```bash
   ls -d ~/backup/genesis_data_* | tail -1
   ```

2. **Check disk space**
   ```bash
   df -h | grep -E "/$"  # Need >5 GB available
   ```

3. **Test powermetrics once**
   ```bash
   sudo powermetrics -n 1 | head -10
   ```

4. **Verify permissions**
   ```bash
   python3 -c "from Quartz import CGEventTapCreate; print('OK')" 2>&1 | grep -i error
   ```

---

## NOTES FOR EXPERIMENTER

- **Privacy**: Only keystroke **timing** is recorded, not content
- **Ethics**: Ensure IRB approval before recruiting participants
- **Consent**: Get signed consent before each session
- **Debriefing**: Tell participants their data will be used for security research
- **Retention**: Keep data for 12 months, then securely delete
- **Access**: Only authorized researchers should have access to HDF5 files

---

**Week 1 Deployment Ready** ✓

This checklist should be printed and posted during Week 1 for reference.

Next: Week 2 (Wavelet Analysis) begins Monday of Week 2.

