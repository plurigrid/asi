---
name: virustotal-reputation
description: Use when users ask to check a file/hash/URL/IP/domain with VirusTotal, confirm malware reputation, investigate possible false positives, or compare AV detections. Prefer hash-based lookup first and use Exa to find public VirusTotal report links.
---

# VirusTotal Reputation

Perform structured VirusTotal-style reputation triage and report risk with explicit confidence.

## Workflow

1. Identify indicator type: `sha256` (preferred), `sha1`/`md5`, filename+publisher, URL, domain, or IP.
2. Perform hash-first discovery:
   - Query exact file hash first: `site:virustotal.com/gui/file <hash>`.
   - If hash is unavailable, query filename and correlate with vendor, signature, and date context.
3. Search with Exa using `mcp__exa__web_search_exa` and prioritize direct VirusTotal GUI result URLs over reposts.
4. Grade confidence:
   - High: exact hash match and consistent publisher context.
   - Medium: filename/context match without exact hash confirmation.
   - Low: no direct report match or conflicting context.
5. Return verdict, confidence, evidence, and next verification action.

## Query Patterns (Exa)

- `site:virustotal.com/gui/file <sha256>`
- `"<filename>.exe" "virustotal.com/gui/file"`
- `"<vendor>" "<filename>" "VirusTotal"`
- `site:virustotal.com/gui/url <url>`
- `site:virustotal.com/gui/domain <domain>`
- `site:virustotal.com/gui/ip-address <ip>`

## Risk Interpretation

- Treat low detections on properly signed vendor updater/firmware binaries as possible false positives.
- Do not declare a sample "clean" based only on low or zero detections.
- Elevate risk when any of the following exists:
  - signature is missing/invalid for expected publisher
  - path and execution context are inconsistent with legitimate updater behavior
  - parent process chain is unrelated or suspicious
  - sandbox behavior indicates credential theft, persistence, injection, or network beaconing

## Privacy/Safety

- Prefer hash lookups before file uploads.
- Do not upload sensitive/private binaries unless user explicitly asks.
- If uncertainty remains, recommend local hash/signature verification plus multi-source triage.

## Quick Commands (User Device)

### Windows PowerShell
```powershell
Get-FileHash "C:\path\to\file.exe" -Algorithm SHA256
Get-AuthenticodeSignature "C:\path\to\file.exe" | Format-List Status,SignerCertificate
```

### Windows CMD
```cmd
certutil -hashfile "C:\path\to\file.exe" SHA256
```

## Response Template

```markdown
Verdict: <likely benign / suspicious / likely malicious> (confidence: <low|medium|high>)

Evidence:
1. <direct VT link or "no direct VT match">
2. <hash/signature/vendor correlation>
3. <detection context / recency / behavior notes>

Next step:
1. <specific command or verification action>
```
