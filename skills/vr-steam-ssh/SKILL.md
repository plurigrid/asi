---
name: vr-steam-ssh
description: Diagnose and fix SteamVR + eGPU issues on remote Windows machines via SSH. Covers GPU routing, SteamVR log analysis, vrdashboard crash loops, Lighthouse tracking, and process management. This skill should be used when troubleshooting VR headsets (especially Bigscreen Beyond) connected to external GPUs on Windows laptops.
---

# VR + Steam + SSH Diagnostic Skill

Record of key diagnostic procedures discovered during a live eGPU + Bigscreen Beyond troubleshooting session on an ASUS laptop (AMD Ryzen AI MAX+ 395 / Radeon 8060S iGPU + NVIDIA RTX 5090 eGPU).

## Key Hows

### 1. SSH Session Management

SSH sessions to Windows drop frequently. Reconnect pattern:

```
ssh bob@<IP>
# password prompt, then Windows cmd shell
```

Windows SSH drops into `cmd.exe`, not PowerShell. Wrap all diagnostics in `powershell -Command "..."`.

### 2. GPU Enumeration (WMIC is deprecated on modern Windows)

```powershell
Get-CimInstance Win32_VideoController | Select-Object Name, DriverVersion, Status, PNPDeviceID | Format-List
```

This reveals all GPUs (iGPU + eGPU) and their PCI device IDs.

### 3. SteamVR Process Inventory

```powershell
Get-Process -Name 'vr*','steam*' -ErrorAction SilentlyContinue | Select-Object Name, Id | Format-Table
```

Key processes: `vrserver`, `vrcompositor`, `vrdashboard`, `vrmonitor`, `steamtours` (SteamVR Home), `vrwebhelper`.

### 4. Compositor Log Analysis — Which GPU is Rendering

```powershell
Get-Content 'C:\Program Files (x86)\Steam\logs\vrcompositor.txt' -Tail 200 | Select-String -Pattern 'GPU|adapter|NVIDIA|AMD|Radeon|render|direct|grey|gray|device|Error'
```

Key lines to look for:
- `GPU Vendor: "NVIDIA GeForce RTX 5090"` — confirms render GPU
- `Headset is using direct mode` — correct for most headsets
- `Error: LiquidVR D3D11CreateDeviceHP3D failed (2)` — AMD LiquidVR SDK conflicting with NVIDIA eGPU. Harmless if compositor still uses NVIDIA, but indicates mixed GPU confusion.
- `Game Info..............FPS Average Target 90  ApplicationTime CPU: 0.000ms` — app not submitting frames (grey screen cause)

### 5. VRDashboard Crash Loop Diagnosis

```powershell
Get-Content 'C:\Program Files (x86)\Steam\logs\vrdashboard.txt' -Tail 30
```

Known crash pattern:
```
GetCursorInfo failed.
Access is denied.
Thread failed to initialize 2
Failed to initialize vrdesktop. Exiting.
```

**Root cause**: `vrdashboard` launched in Session 0 (services/SSH session) cannot access the interactive desktop. Fix: launch SteamVR from the actual desktop, not via SSH. Create a `.bat` file on the user's desktop:

```bat
@echo off
start "" "C:\Program Files (x86)\Steam\steam.exe" steam://rungameid/250820
```

### 6. Force GPU Preference for SteamVR Executables

Set Windows Graphics Preferences via registry to force all SteamVR processes onto the eGPU:

```powershell
$apps = @(
    'C:\Program Files (x86)\Steam\steamapps\common\SteamVR\bin\win64\vrdashboard.exe',
    'C:\Program Files (x86)\Steam\steamapps\common\SteamVR\bin\win64\vrcompositor.exe',
    'C:\Program Files (x86)\Steam\steamapps\common\SteamVR\bin\win64\vrserver.exe',
    'C:\Program Files (x86)\Steam\steamapps\common\SteamVR\tools\steamvr_environments\game\bin\win64\steamtours.exe',
    'C:\Program Files (x86)\Steam\steam.exe'
)
$regPath = 'HKCU:\Software\Microsoft\DirectX\UserGpuPreferences'
if (!(Test-Path $regPath)) { New-Item -Path $regPath -Force }
foreach ($app in $apps) {
    if (Test-Path $app) {
        Set-ItemProperty -Path $regPath -Name $app -Value 'GpuPreference=2;' -Force
        Write-Host "Set $app to High Performance GPU"
    }
}
```

`GpuPreference=2` = High Performance (discrete/eGPU). Requires SteamVR restart to take effect.

**Important**: Don't forget `steamtours.exe` — it's the SteamVR Home renderer and lives in a different path than the other VR executables. Find its path dynamically:

```powershell
(Get-Process -Name 'steamtours').Path
```

### 7. SteamVR Config File (`steamvr.vrsettings`)

Located at `C:\Program Files (x86)\Steam\config\steamvr.vrsettings`. JSON format. Add `forcedGpuIdx` to the `steamvr` section to pin the render GPU:

```json
{
  "steamvr": {
    "forcedGpuIdx": 1
  }
}
```

GPU index 0 is typically the iGPU, 1 is the eGPU. Verify by checking `gpuSpeedVendor` in the `GpuSpeed` section.

### 8. Lighthouse Tracking Diagnosis

```powershell
Get-Content 'C:\Program Files (x86)\Steam\logs\vrserver.txt' -Tail 50 | Select-String 'track|base|lighthouse|pose|error|warn|HMD'
```

If you see:
```
lighthouse: LHR-XXXXXXXX H: No base stations seen...
lighthouse: LHR-XXXXXXXX H: No optical frames in past 5 seconds
```

The headset cannot see any base stations. Bigscreen Beyond requires physical Lighthouse base stations — no software workaround exists for actual tracking.

**Spoofing options** (for testing without base stations):
- [HoboVR](https://github.com/HoboVR-Labs/hobo_vr) — SteamVR driver that feeds fake pose data
- [OpenVR-InputEmulator](https://github.com/ousttrue/OpenVR-InputEmulator) — virtual controllers and pose manipulation

### 9. Full SteamVR Restart via SSH

```powershell
Stop-Process -Name 'vrserver','vrcompositor','vrmonitor','vrdashboard','steamtours','vrwebhelper' -Force -ErrorAction SilentlyContinue
```

Then relaunch from the desktop (not SSH) to avoid Session 0 issues.

### 10. Don't Disable the iGPU

Disabling the iGPU in Device Manager will black out the laptop screen. Only do this if an external monitor or dummy HDMI plug is connected to the eGPU. The GPU preference registry approach (How #6) is the safe alternative.

## Diagnostic Decision Tree

```
Grey screen in headset
├── Check vrcompositor.txt → Which GPU?
│   ├── Wrong GPU → Force GPU preferences (How #6, #7)
│   └── Correct GPU → Continue
├── Check vrdashboard.txt → Crashing?
│   ├── "Access is denied" → Launched from SSH, needs desktop launch (How #5)
│   └── Not crashing → Continue
├── Check vrserver.txt → Tracking?
│   ├── "No base stations seen" → Need base stations or spoof (How #8)
│   └── Tracking OK → Check if steamtours is submitting frames
└── Check compositor "Game Info" line
    ├── CPU: 0.000ms → App not rendering, check GPU preference for steamtours
    └── CPU: >0 → Frames submitting, check headset cable/connection
```
