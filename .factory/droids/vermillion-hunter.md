---
name: vermillion-hunter
description: 'Overview'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

## Overview

Frida-based dynamic instrumentation for identifying Windows "features" exploitable for:
- **DLL Sideloading** (T1574.002)
- **COM Hijacking** (T1546.015)

WFH Dridex variant: ~966 validated sideloads vs 96 from original.

---

## MITRE ATT&CK Mapping

### T1574.002 - DLL Side-Loading

| Tactic | ID | Description |
|--------|-----|-------------|
| Persistence | TA0003 | Maintain access via trusted process |
| Privilege Escalation | TA0004 | Inherit elevated token |
| Defense Evasion | TA0005 | Execute under signed binary |

**Hooked APIs:**
```
LoadLibraryW(LPCWSTR lpLibFileName)
LoadLibraryExW(LPCWSTR lpLibFileName, HANDLE hFile, DWORD dwFlags)
GetProcAddress(HMODULE hModule, LPCSTR lpProcName)
```

**Attack Chain:**
```
1. Identify signed exe with weak DLL reference
2. Copy exe to attacker-controlled directory
3. Place malicious DLL with expected name
4. Execute → DLL loads in trusted context
```

### T1546.015 - COM Hijacking

| Tactic | ID | Description |
|--------|-----|-------------|
| Persistence | TA0003 | Survive reboots via registry |
| Privilege Escalation | TA0004 | Hijack elevated COM server |

**Hooked APIs:**
```
RegQueryValueExW → CLSID\{GUID}\InProcServer32
```

**Attack Chain:**
```
1. Monitor COM object instantiation
2. Create HKCU shadow of HKLM CLSID entry
3. Point InProcServer32 to malicious DLL
4. Application loads attacker DLL on COM call
```

---

## Usage Patterns

### DLL Sideloading Detection
```bash
# Single target
python wfh.py -t .\mspaint.exe -m dll

# Batch (copy exes to WFH dir first)
python wfh.py -t * -m dll

# Verbose with timeout
python wfh.py -t * -m dll -v -timeout 30
```

### COM Hijacking Detection
```bash
python wfh.py -t "C:\Program Files\Internet Explorer\iexplore.exe" -m com -v
```

### WFH Dridex (Enhanced)
```bash
# Requires MinGW G++ in PATH
python wfh_dridex.py
# Outputs: results.csv with validated sideloads
```

### Bulk Windows Binary Scan
```powershell
# Copy all signed Windows binaries
Get-ChildItem c