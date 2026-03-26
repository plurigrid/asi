---
name: nhero-nurse
description: Nurse approval email automation for nhero controlled substance slots. Gmail MCP integration with scrambled slot names — nurse sees only slot letters, never medication names. Dual-address routing to mantissa@gmail.com (primary) and ies@plurigrid.com (backup).
version: 0.1.0
trit: 1
color: "#16FF16"
tags: [nhero, nurse, email, approval, gmail, automation]
---

# nhero-nurse

Nurse approval workflow. Scrambled. Email-automated.

## Flow

```
killdispenser(slot, HOLD) → queue nurse request
  → Gmail MCP creates draft (from mantissa@plurigrid.com)
  → Sent to mantissa@gmail.com (cc: ies@plurigrid.com)
  → Nurse replies APPROVED / DENIED
  → hero_email_monitor.py parses reply
  → killdispenser(slot, DISPENSE) or remains HOLD
```

## Privacy

The nurse email contains:
- Slot letter (e.g., "Q")
- Proposed dosage (e.g., "30.0mg")
- Supply assessment

The nurse email does NOT contain:
- Medication name
- Patient identity
- Diagnosis

## Email Architecture

| Role | Address |
|------|---------|
| Hero registration | `mantissa+hero-h@plurigrid.com` |
| Nurse approval TO | `mantissa@gmail.com` |
| Nurse backup CC | `ies@plurigrid.com` |
| Automation FROM | `mantissa@plurigrid.com` |

## Parent
Part of the [nhero](../nhero/SKILL.md) hierarchy.
