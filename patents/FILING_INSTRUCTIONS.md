# USPTO Provisional Patent Filing Instructions

## Files Ready for Filing

| File | Title | Claims |
|------|-------|--------|
| `USPTO_GF3_CONSERVATION_PROVISIONAL.txt` | Triadic Conservation-Constrained Parallel Task Dispatch | 8 |
| `USPTO_BISIMULATION_DISPERSAL_PROVISIONAL.txt` | Distributed Skill Verification Using Bisimulation Games | 10 |

## Filing Steps (EFS-Web)

### 1. Create USPTO Account
- Go to https://patentcenter.uspto.gov
- Register for a USPTO.gov account if not already registered

### 2. Prepare Documents
```bash
# Convert to PDF (USPTO prefers PDF)
pandoc USPTO_GF3_CONSERVATION_PROVISIONAL.txt -o USPTO_GF3_CONSERVATION_PROVISIONAL.pdf
pandoc USPTO_BISIMULATION_DISPERSAL_PROVISIONAL.txt -o USPTO_BISIMULATION_DISPERSAL_PROVISIONAL.pdf
```

### 3. Fill In Blanks
Before filing, complete:
- [ ] Inventor 1 name, residence, citizenship
- [ ] Inventor 2 name, residence, citizenship (if applicable)
- [ ] Correspondence address
- [ ] Signature and date on Micro Entity Certification

### 4. File via Patent Center
1. Log in to Patent Center
2. Select "Provisional Application"
3. Upload specification PDF
4. Complete ADS (Application Data Sheet) online
5. Pay fee: **$320** (Micro Entity)
6. Submit and save confirmation number

### 5. Post-Filing
- Receive provisional application number within 24-48 hours
- Mark all related code/docs as "Patent Pending"
- Calendar 12-month deadline for non-provisional conversion

## Timeline

| Date | Action |
|------|--------|
| Filing date | Priority date established |
| Filing + 12 months | Deadline: Convert to non-provisional OR abandon |
| Filing + 18 months | (Non-provisional only) Publication |

## Micro Entity Requirements

You qualify if ALL of:
1. Qualify as small entity (< 500 employees)
2. Named on ≤ 4 prior patent applications
3. Gross income < $250,548 (3x median, 2024)
4. Haven't assigned rights to non-qualifying entity

## Cost Summary

| Phase | Micro Entity Fee |
|-------|------------------|
| Provisional filing | $320 |
| Non-provisional filing (if converted) | $400 |
| Examination fee | $200 |
| Issue fee | $280 |
| **Total through issuance** | ~$1,200 |

## Next Steps After Filing

1. **Defensive publication** (optional): Post abstract to arXiv/Zenodo for additional timestamp
2. **Continue development**: "Patent Pending" status allows public discussion
3. **Prior art monitoring**: Set Google Scholar alerts for related terms
4. **12-month decision**: Convert to non-provisional or let lapse

## Contact IP Counsel

For prosecution support (Bay Area):
- Fenwick & West: (650) 988-8500
- Wilson Sonsini: (650) 493-9300
- Knobbe Martens: (949) 760-0404
