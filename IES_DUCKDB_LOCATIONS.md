# IES Message Databases - Complete Inventory

## Summary

The IES network has **79,716 messages** from **759 senders** primarily involving:
- **Me** (9,138 messages)
- **ChrisHypernym** (5,878 messages)  
- **Kevin10** (3,665 messages)
- **Shon** (1,300 messages)
- **John7** (759 messages)

---

## Primary IES Message Databases

### 1. **Primary Candidate: ~/ies/music-topos/data/asi.duckdb** (44 MB)
**Status**: Contains IES-related schema but currently empty tables
**Tables**:
- `thread_messages` (empty - 0 rows)
- `threads` (empty - 0 rows)
- `thread_skills` (empty - 0 rows)
- `thread_triads` (empty - 0 rows)
- `gh_skills` (165 rows)
- `gh_repos` (1 row)

**Note**: This appears to be the IES database but the message tables haven't been populated.

### 2. **Secondary Candidate: ~/ies/ananas.duckdb** (108 MB)
**Content**: Papers, theorems, implementations (not IES messages)

### 3. **Tertiary Candidate: ~/ies/hatchery.duckdb** (492 MB)
**Content**: Topos Institute + Category Theory community (123,614 Zulip messages)
**Does NOT contain**: IES network messages (different community)

### 4. **IES Documentation References**:
- `~/ies/plurigrid-asi-skillz/ies/IES_NETWORK_SUBSTANTIATION.txt` (79,716 messages)
- `~/ies/plurigrid-asi-skillz/ies/PHASE3_IES_DISCOVERY_INDEX.md` (IES structure analysis)

---

## Alternative Locations to Check

### Music-Topos Databases
- `~/ies/music-topos/music_knowledge.duckdb` (8.8 MB)
- `~/ies/music-topos/apt_observations.duckdb` (4.3 MB)
- `~/ies/music-topos/unified_timeline.duckdb` (3.8 MB)

### DuckLake Databases  
- `~/ies/ducklake_data/ies_interactome.duckdb` (8.0 MB)
- `~/ies/ducklake_data/bmorphism_unified.duckdb` (2.3 MB)
- `~/ies/ducklake_data/library_lake.duckdb` (5.8 MB)

### Archive Locations
- `~/ies/plurigrid-asi-worktrees/reconcile/ies/music-topos/` (multiple backups)
- `~/ies/plurigrid-asi-skillz/ies/` (referenced but may be symlink)

---

## Recommendation

**To find the actual IES messages (79,716 records):**

1. **Check if populated**: Query the empty `ast.duckdb` tables - they have the right schema
2. **Search connected databases**:
   ```bash
   duckdb ~/ies/music-topos/music_knowledge.duckdb \
     "SELECT COUNT(*) FROM information_schema.tables WHERE table_name LIKE '%message%'"
   ```

3. **Check if archived/exported**: Look for:
   - JSON files with IES message data
   - CSV exports in `~/ies/` or `~/ies/music-topos/data/`
   - Python pickle files

4. **Search git history**: 
   - IES data may have been committed to git
   - Check `music-topos/.git` for historical versions

---

## Known Structure (from IES_NETWORK_SUBSTANTIATION.txt)

The 79,716 IES messages follow this distribution:

| Core Member | Message Count | Avg Length | Recipients | Role |
|---|---|---|---|---|
| Me | 9,138 (44%) | 196 chars | 58 | Synthesizer |
| ChrisHypernym | 5,878 (28%) | 93 chars | 39 | Coordinator |
| Kevin10 | 3,665 (18%) | 167 chars | 40 | Integrator |
| Shon | 1,300 (6%) | 160 chars | 17 | Stable Contributor |
| John7 | 759 (4%) | 135 chars | 23 | Translator |
| **Other 754 senders** | **59,000 (74%)** | Varied | Varied | Various |

---

## Next Steps

1. **Verify `asi.duckdb`**: Populate the empty tables if data exists
2. **Search `music_knowledge.duckdb`**: Likely location for IES discussions
3. **Check DuckLake**: `ies_interactome.duckdb` naming suggests relevant data
4. **Consult commit logs**: `git log --all -- '*IES*' --source`

