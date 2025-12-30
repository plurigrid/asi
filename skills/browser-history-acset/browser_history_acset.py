#!/usr/bin/env python3
"""
Browser History ACSet
Unified categorical structure for browser history across:
- ChatGPT Atlas browser (Chromium-based)
- Safari, Chrome, Firefox, Arc, Brave

Schema follows existing OpenAI ACSet patterns with GF(3) trit classification.
"""

import json
import sqlite3
import os
import shutil
import tempfile
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any
from datetime import datetime
from enum import Enum
from pathlib import Path
from urllib.parse import urlparse
import hashlib

GOLDEN = 0x9E3779B97F4A7C15

class Trit(Enum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1

# Browser History ACSet Schema (following OpenAI ACSet patterns)
SCHEMA_BROWSER_HISTORY = {
    "objects": [
        "Browser", "URL", "Visit", "Domain", 
        "SearchQuery", "Download", "Session", "Cluster"
    ],
    "morphisms": {
        "browser_of": ("URL", "Browser"),
        "domain_of": ("URL", "Domain"),
        "url_of": ("Visit", "URL"),
        "session_of": ("Visit", "Session"),
        "from_visit": ("Visit", "Visit"),
        "cluster_of": ("Visit", "Cluster"),
        "url_of_download": ("Download", "URL"),
        "query_url": ("SearchQuery", "URL"),
    },
    "attributes": {
        "Browser": ["name", "path", "browser_type", "trit"],
        "URL": ["url", "title", "visit_count", "typed_count", "last_visit_time", "hidden"],
        "Visit": ["visit_time", "transition", "duration", "trit"],
        "Domain": ["domain", "tld", "visit_total", "trit"],
        "SearchQuery": ["term", "normalized_term", "count"],
        "Download": ["path", "filename", "mime_type", "size", "start_time", "end_time"],
        "Session": ["start_time", "end_time", "visit_count"],
        "Cluster": ["label", "should_show"],
    }
}

# Domain classification for GF(3) trits
DOMAIN_TRITS = {
    # PLUS (+1): Creation/building tools
    "github.com": Trit.PLUS,
    "ampcode.com": Trit.PLUS,
    "huggingface.co": Trit.PLUS,
    "arxiv.org": Trit.PLUS,
    "julialang.org": Trit.PLUS,
    "docs.julialang.org": Trit.PLUS,
    "pkg.julialang.org": Trit.PLUS,
    "chatgpt.com": Trit.PLUS,
    "claude.ai": Trit.PLUS,
    "deepwiki.org": Trit.PLUS,
    "elevenlabs.io": Trit.PLUS,
    "mathpix.com": Trit.PLUS,
    "accounts.mathpix.com": Trit.PLUS,
    "latent.toys": Trit.PLUS,
    "localhost": Trit.PLUS,
    
    # ERGODIC (0): Information/coordination
    "google.com": Trit.ERGODIC,
    "mail.google.com": Trit.ERGODIC,
    "youtube.com": Trit.ERGODIC,
    "www.youtube.com": Trit.ERGODIC,
    "x.com": Trit.ERGODIC,
    "twitter.com": Trit.ERGODIC,
    "bsky.app": Trit.ERGODIC,
    "discord.com": Trit.ERGODIC,
    "slack.com": Trit.ERGODIC,
    "icloud.com": Trit.ERGODIC,
    "www.icloud.com": Trit.ERGODIC,
    
    # MINUS (-1): Consumption/extraction
    "amazon.com": Trit.MINUS,
    "netflix.com": Trit.MINUS,
    "facebook.com": Trit.MINUS,
    "instagram.com": Trit.MINUS,
    "tiktok.com": Trit.MINUS,
    "reddit.com": Trit.MINUS,
}

@dataclass
class BrowserHistoryACSet:
    """Compositional ACSet for browser history."""
    schema: dict = field(default_factory=lambda: SCHEMA_BROWSER_HISTORY)
    parts: dict = field(default_factory=dict)
    subparts: dict = field(default_factory=dict)
    
    def __post_init__(self):
        for ob in self.schema["objects"]:
            self.parts[ob] = []
        for morph in self.schema["morphisms"]:
            self.subparts[morph] = []
        for ob, attrs in self.schema["attributes"].items():
            for attr in attrs:
                self.subparts[f"{ob}_{attr}"] = []
    
    def add_part(self, ob: str, **attrs) -> int:
        idx = len(self.parts[ob])
        self.parts[ob].append(idx)
        for attr in self.schema["attributes"].get(ob, []):
            val = attrs.get(attr)
            self.subparts[f"{ob}_{attr}"].append(val)
        return idx
    
    def set_subpart(self, morph: str, src: int, tgt: int):
        while len(self.subparts[morph]) <= src:
            self.subparts[morph].append(None)
        self.subparts[morph][src] = tgt
    
    def nparts(self, ob: str) -> int:
        return len(self.parts[ob])
    
    def incident(self, tgt: int, morph: str) -> list:
        """Find all sources that map to target via morphism."""
        return [i for i, t in enumerate(self.subparts[morph]) if t == tgt]
    
    def get_attr(self, ob: str, idx: int, attr: str) -> Any:
        """Get attribute value for a part."""
        key = f"{ob}_{attr}"
        if key in self.subparts and idx < len(self.subparts[key]):
            return self.subparts[key][idx]
        return None
    
    def gf3_sum(self) -> int:
        """Calculate GF(3) sum across all domains."""
        total = 0
        for i in range(self.nparts("Domain")):
            trit = self.get_attr("Domain", i, "trit")
            if trit and hasattr(trit, 'value'):
                total += trit.value
            elif isinstance(trit, int):
                total += trit
        return total
    
    def summary(self) -> str:
        lines = [
            "╔═══════════════════════════════════════════════════════════════╗",
            "║              Browser History ACSet                            ║",
            "╠═══════════════════════════════════════════════════════════════╣",
        ]
        for ob in self.schema["objects"]:
            n = self.nparts(ob)
            if n > 0:
                lines.append(f"║  {ob:15} : {n:6} parts                          ║")
        lines.append("╠═══════════════════════════════════════════════════════════════╣")
        lines.append(f"║  GF(3) Sum       : {self.gf3_sum():6}                                ║")
        lines.append("╚═══════════════════════════════════════════════════════════════╝")
        return "\n".join(lines)

class BrowserHistoryExtractor:
    """Extract browser history from various browsers on macOS."""
    
    BROWSER_PATHS = {
        "atlas": {
            "name": "ChatGPT Atlas",
            "path": "~/Library/Application Support/com.openai.atlas/browser-data/host/user-*/History",
            "type": "chromium",
            "trit": Trit.PLUS
        },
        "atlas_default": {
            "name": "ChatGPT Atlas Default",
            "path": "~/Library/Application Support/com.openai.atlas/browser-data/host/Default/History",
            "type": "chromium",
            "trit": Trit.PLUS
        },
        "chrome": {
            "name": "Google Chrome",
            "path": "~/Library/Application Support/Google/Chrome/Default/History",
            "type": "chromium",
            "trit": Trit.ERGODIC
        },
        "arc": {
            "name": "Arc Browser",
            "path": "~/Library/Application Support/Arc/User Data/Default/History",
            "type": "chromium",
            "trit": Trit.PLUS
        },
        "brave": {
            "name": "Brave Browser",
            "path": "~/Library/Application Support/BraveSoftware/Brave-Browser/Default/History",
            "type": "chromium",
            "trit": Trit.ERGODIC
        },
        "firefox": {
            "name": "Mozilla Firefox",
            "path": "~/Library/Application Support/Firefox/Profiles/*/places.sqlite",
            "type": "firefox",
            "trit": Trit.ERGODIC
        },
        "safari": {
            "name": "Safari",
            "path": "~/Library/Safari/History.db",
            "type": "safari",
            "trit": Trit.ERGODIC
        }
    }
    
    def __init__(self):
        self.acset = BrowserHistoryACSet()
        self.domain_cache: Dict[str, int] = {}
        self.url_cache: Dict[str, int] = {}
    
    def find_browser_dbs(self) -> Dict[str, str]:
        """Find all available browser history databases."""
        found = {}
        
        for browser_id, info in self.BROWSER_PATHS.items():
            path = os.path.expanduser(info["path"])
            
            # Handle wildcards
            if "*" in path:
                import glob
                matches = glob.glob(path)
                if matches:
                    found[browser_id] = matches[0]
            else:
                if os.path.exists(path):
                    found[browser_id] = path
        
        return found
    
    def extract_chromium(self, db_path: str, browser_info: dict, browser_idx: int) -> int:
        """Extract history from Chromium-based browser."""
        # Copy to temp to avoid lock issues
        with tempfile.NamedTemporaryFile(suffix='.db', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            shutil.copy2(db_path, tmp_path)
            conn = sqlite3.connect(tmp_path)
            cursor = conn.cursor()
            
            # Extract URLs
            cursor.execute("""
                SELECT id, url, title, visit_count, typed_count, last_visit_time, hidden
                FROM urls ORDER BY visit_count DESC
            """)
            
            url_count = 0
            url_id_map = {}
            
            for row in cursor.fetchall():
                db_id, url, title, visit_count, typed_count, last_visit_time, hidden = row
                
                # Parse domain
                parsed = urlparse(url)
                domain = parsed.netloc.lower()
                
                # Get or create domain
                if domain not in self.domain_cache:
                    tld = ".".join(domain.split(".")[-2:]) if "." in domain else domain
                    domain_trit = DOMAIN_TRITS.get(domain, Trit.ERGODIC)
                    domain_idx = self.acset.add_part("Domain",
                        domain=domain,
                        tld=tld,
                        visit_total=0,
                        trit=domain_trit.value
                    )
                    self.domain_cache[domain] = domain_idx
                
                domain_idx = self.domain_cache[domain]
                
                # Add URL
                url_idx = self.acset.add_part("URL",
                    url=url,
                    title=title or "",
                    visit_count=visit_count,
                    typed_count=typed_count,
                    last_visit_time=last_visit_time,
                    hidden=hidden
                )
                
                self.acset.set_subpart("browser_of", url_idx, browser_idx)
                self.acset.set_subpart("domain_of", url_idx, domain_idx)
                
                url_id_map[db_id] = url_idx
                url_count += 1
            
            # Extract visits
            cursor.execute("""
                SELECT id, url, visit_time, from_visit, transition, visit_duration
                FROM visits ORDER BY visit_time DESC
            """)
            
            visit_id_map = {}
            for row in cursor.fetchall():
                visit_id, url_id, visit_time, from_visit, transition, duration = row
                
                if url_id not in url_id_map:
                    continue
                
                url_idx = url_id_map[url_id]
                domain_idx = self.acset.subparts["domain_of"][url_idx]
                domain_trit = self.acset.get_attr("Domain", domain_idx, "trit") if domain_idx else 0
                
                visit_idx = self.acset.add_part("Visit",
                    visit_time=visit_time,
                    transition=transition,
                    duration=duration,
                    trit=domain_trit
                )
                
                self.acset.set_subpart("url_of", visit_idx, url_idx)
                visit_id_map[visit_id] = visit_idx
            
            # Link from_visit relationships
            cursor.execute("SELECT id, from_visit FROM visits WHERE from_visit > 0")
            for visit_id, from_visit_id in cursor.fetchall():
                if visit_id in visit_id_map and from_visit_id in visit_id_map:
                    self.acset.set_subpart("from_visit", 
                        visit_id_map[visit_id], 
                        visit_id_map[from_visit_id])
            
            # Extract search queries
            cursor.execute("""
                SELECT term, normalized_term, COUNT(*) as count
                FROM keyword_search_terms
                GROUP BY term
                ORDER BY count DESC
            """)
            
            for term, normalized_term, count in cursor.fetchall():
                self.acset.add_part("SearchQuery",
                    term=term[:500],  # Truncate long terms
                    normalized_term=normalized_term[:500] if normalized_term else "",
                    count=count
                )
            
            # Extract downloads
            try:
                cursor.execute("""
                    SELECT target_path, mime_type, total_bytes, start_time, end_time
                    FROM downloads
                    ORDER BY start_time DESC
                """)
                
                for target_path, mime_type, size, start_time, end_time in cursor.fetchall():
                    filename = os.path.basename(target_path) if target_path else ""
                    self.acset.add_part("Download",
                        path=target_path or "",
                        filename=filename,
                        mime_type=mime_type or "",
                        size=size,
                        start_time=start_time,
                        end_time=end_time
                    )
            except sqlite3.OperationalError:
                pass  # Downloads table may not exist
            
            conn.close()
            return url_count
            
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
    
    def extract_safari(self, db_path: str, browser_info: dict, browser_idx: int) -> int:
        """Extract history from Safari."""
        with tempfile.NamedTemporaryFile(suffix='.db', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            shutil.copy2(db_path, tmp_path)
            conn = sqlite3.connect(tmp_path)
            cursor = conn.cursor()
            
            url_count = 0
            url_id_map = {}
            
            # Safari schema: history_items + history_visits
            cursor.execute("""
                SELECT id, url, domain_expansion, visit_count
                FROM history_items
                ORDER BY visit_count DESC
            """)
            
            for row in cursor.fetchall():
                db_id, url, domain_expansion, visit_count = row
                
                if not url:
                    continue
                
                parsed = urlparse(url)
                domain = parsed.netloc.lower()
                
                if domain not in self.domain_cache:
                    tld = ".".join(domain.split(".")[-2:]) if "." in domain else domain
                    domain_trit = DOMAIN_TRITS.get(domain, Trit.ERGODIC)
                    domain_idx = self.acset.add_part("Domain",
                        domain=domain,
                        tld=tld,
                        visit_total=0,
                        trit=domain_trit.value
                    )
                    self.domain_cache[domain] = domain_idx
                
                domain_idx = self.domain_cache[domain]
                
                # Safari doesn't store title in history_items, use domain_expansion
                url_idx = self.acset.add_part("URL",
                    url=url,
                    title=domain_expansion or "",
                    visit_count=visit_count or 0,
                    typed_count=0,
                    last_visit_time=None,
                    hidden=0
                )
                
                self.acset.set_subpart("browser_of", url_idx, browser_idx)
                self.acset.set_subpart("domain_of", url_idx, domain_idx)
                
                url_id_map[db_id] = url_idx
                url_count += 1
            
            # Extract visits
            cursor.execute("""
                SELECT id, history_item, visit_time, title, redirect_source
                FROM history_visits
                ORDER BY visit_time DESC
            """)
            
            visit_id_map = {}
            for row in cursor.fetchall():
                visit_id, history_item_id, visit_time, title, redirect_source = row
                
                if history_item_id not in url_id_map:
                    continue
                
                url_idx = url_id_map[history_item_id]
                domain_idx = self.acset.subparts["domain_of"][url_idx] if url_idx < len(self.acset.subparts["domain_of"]) else None
                domain_trit = self.acset.get_attr("Domain", domain_idx, "trit") if domain_idx else 0
                
                # Safari visit_time is in Mac absolute time (seconds since 2001-01-01)
                visit_idx = self.acset.add_part("Visit",
                    visit_time=visit_time,
                    transition=0,  # Safari doesn't track transition type
                    duration=0,
                    trit=domain_trit
                )
                
                self.acset.set_subpart("url_of", visit_idx, url_idx)
                visit_id_map[visit_id] = visit_idx
                
                # Link redirect chains
                if redirect_source and redirect_source in visit_id_map:
                    self.acset.set_subpart("from_visit", visit_idx, visit_id_map[redirect_source])
            
            conn.close()
            return url_count
            
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
    
    def extract_firefox(self, db_path: str, browser_info: dict, browser_idx: int) -> int:
        """Extract history from Firefox."""
        with tempfile.NamedTemporaryFile(suffix='.db', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            shutil.copy2(db_path, tmp_path)
            conn = sqlite3.connect(tmp_path)
            cursor = conn.cursor()
            
            url_count = 0
            url_id_map = {}
            
            # Firefox schema: moz_places + moz_historyvisits
            cursor.execute("""
                SELECT id, url, title, visit_count, typed, last_visit_date, hidden
                FROM moz_places
                WHERE visit_count > 0
                ORDER BY visit_count DESC
            """)
            
            for row in cursor.fetchall():
                db_id, url, title, visit_count, typed, last_visit_date, hidden = row
                
                if not url:
                    continue
                
                parsed = urlparse(url)
                domain = parsed.netloc.lower()
                
                if domain not in self.domain_cache:
                    tld = ".".join(domain.split(".")[-2:]) if "." in domain else domain
                    domain_trit = DOMAIN_TRITS.get(domain, Trit.ERGODIC)
                    domain_idx = self.acset.add_part("Domain",
                        domain=domain,
                        tld=tld,
                        visit_total=0,
                        trit=domain_trit.value
                    )
                    self.domain_cache[domain] = domain_idx
                
                domain_idx = self.domain_cache[domain]
                
                url_idx = self.acset.add_part("URL",
                    url=url,
                    title=title or "",
                    visit_count=visit_count or 0,
                    typed_count=typed or 0,
                    last_visit_time=last_visit_date,
                    hidden=hidden or 0
                )
                
                self.acset.set_subpart("browser_of", url_idx, browser_idx)
                self.acset.set_subpart("domain_of", url_idx, domain_idx)
                
                url_id_map[db_id] = url_idx
                url_count += 1
            
            # Extract visits
            cursor.execute("""
                SELECT id, place_id, visit_date, visit_type, from_visit
                FROM moz_historyvisits
                ORDER BY visit_date DESC
            """)
            
            visit_id_map = {}
            for row in cursor.fetchall():
                visit_id, place_id, visit_date, visit_type, from_visit = row
                
                if place_id not in url_id_map:
                    continue
                
                url_idx = url_id_map[place_id]
                domain_idx = self.acset.subparts["domain_of"][url_idx] if url_idx < len(self.acset.subparts["domain_of"]) else None
                domain_trit = self.acset.get_attr("Domain", domain_idx, "trit") if domain_idx else 0
                
                visit_idx = self.acset.add_part("Visit",
                    visit_time=visit_date,  # Firefox uses microseconds since epoch
                    transition=visit_type or 0,
                    duration=0,
                    trit=domain_trit
                )
                
                self.acset.set_subpart("url_of", visit_idx, url_idx)
                visit_id_map[visit_id] = visit_idx
            
            # Link from_visit relationships
            cursor.execute("SELECT id, from_visit FROM moz_historyvisits WHERE from_visit > 0")
            for visit_id, from_visit_id in cursor.fetchall():
                if visit_id in visit_id_map and from_visit_id in visit_id_map:
                    self.acset.set_subpart("from_visit",
                        visit_id_map[visit_id],
                        visit_id_map[from_visit_id])
            
            conn.close()
            return url_count
            
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
    
    def extract_all(self) -> BrowserHistoryACSet:
        """Extract history from all available browsers."""
        browsers = self.find_browser_dbs()
        
        print(f"Found {len(browsers)} browser(s) with history")
        
        for browser_id, db_path in browsers.items():
            info = self.BROWSER_PATHS[browser_id]
            
            # Add browser
            browser_idx = self.acset.add_part("Browser",
                name=info["name"],
                path=db_path,
                browser_type=info["type"],
                trit=info["trit"].value
            )
            
            print(f"\nExtracting from {info['name']}...")
            
            try:
                if info["type"] == "chromium":
                    count = self.extract_chromium(db_path, info, browser_idx)
                    print(f"  Extracted {count} URLs")
                elif info["type"] == "safari":
                    count = self.extract_safari(db_path, info, browser_idx)
                    print(f"  Extracted {count} URLs")
                elif info["type"] == "firefox":
                    count = self.extract_firefox(db_path, info, browser_idx)
                    print(f"  Extracted {count} URLs")
                else:
                    print(f"  Skipping {info['type']} (unknown type)")
            except Exception as e:
                print(f"  Error: {e}")
        
        return self.acset

def classify_url_trit(url: str) -> Trit:
    """Classify a URL into GF(3) trit based on domain."""
    parsed = urlparse(url)
    domain = parsed.netloc.lower()
    return DOMAIN_TRITS.get(domain, Trit.ERGODIC)

def analyze_browsing_patterns(acset: BrowserHistoryACSet) -> Dict:
    """Analyze browsing patterns from the ACSet."""
    
    # Domain distribution by trit
    trit_counts = {-1: 0, 0: 0, 1: 0}
    trit_visits = {-1: 0, 0: 0, 1: 0}
    
    for i in range(acset.nparts("Domain")):
        trit = acset.get_attr("Domain", i, "trit")
        if trit is not None:
            trit_val = trit if isinstance(trit, int) else trit.value
            trit_counts[trit_val] = trit_counts.get(trit_val, 0) + 1
    
    for i in range(acset.nparts("Visit")):
        trit = acset.get_attr("Visit", i, "trit")
        if trit is not None:
            trit_val = trit if isinstance(trit, int) else trit.value
            trit_visits[trit_val] = trit_visits.get(trit_val, 0) + 1
    
    # Top domains by visit count
    domain_visits = {}
    for i in range(acset.nparts("URL")):
        domain_idx = acset.subparts["domain_of"][i] if i < len(acset.subparts["domain_of"]) else None
        if domain_idx is not None:
            domain = acset.get_attr("Domain", domain_idx, "domain")
            visit_count = acset.get_attr("URL", i, "visit_count") or 0
            domain_visits[domain] = domain_visits.get(domain, 0) + visit_count
    
    top_domains = sorted(domain_visits.items(), key=lambda x: -x[1])[:20]
    
    return {
        "browsers": acset.nparts("Browser"),
        "urls": acset.nparts("URL"),
        "visits": acset.nparts("Visit"),
        "domains": acset.nparts("Domain"),
        "searches": acset.nparts("SearchQuery"),
        "downloads": acset.nparts("Download"),
        "trit_distribution": {
            "domains": trit_counts,
            "visits": trit_visits
        },
        "top_domains": top_domains,
        "gf3_sum": acset.gf3_sum()
    }

def main():
    """Extract and analyze browser history as ACSet."""
    print("=" * 70)
    print("BROWSER HISTORY ACSET EXTRACTION")
    print("ChatGPT Atlas + All Browsers → Categorical Structure")
    print("=" * 70)
    
    extractor = BrowserHistoryExtractor()
    acset = extractor.extract_all()
    
    print("\n" + acset.summary())
    
    # Analyze patterns
    print("\n--- Browsing Pattern Analysis ---")
    analysis = analyze_browsing_patterns(acset)
    
    print(f"\nGF(3) Domain Distribution:")
    for trit_val, label in [(-1, "MINUS (consumption)"), (0, "ERGODIC (info)"), (1, "PLUS (creation)")]:
        count = analysis["trit_distribution"]["domains"].get(trit_val, 0)
        visits = analysis["trit_distribution"]["visits"].get(trit_val, 0)
        print(f"  [{trit_val:+d}] {label}: {count} domains, {visits} visits")
    
    print(f"\nTop Domains by Visit Count:")
    for domain, visits in analysis["top_domains"][:15]:
        trit = DOMAIN_TRITS.get(domain, Trit.ERGODIC)
        trit_sym = {Trit.PLUS: "[+]", Trit.ERGODIC: "[○]", Trit.MINUS: "[-]"}[trit]
        print(f"  {trit_sym} {domain:<35} : {visits:>6} visits")
    
    print(f"\nGF(3) Sum: {analysis['gf3_sum']}")
    
    # Export
    export_data = {
        "schema": SCHEMA_BROWSER_HISTORY,
        "counts": {
            "browsers": analysis["browsers"],
            "urls": analysis["urls"],
            "visits": analysis["visits"],
            "domains": analysis["domains"],
            "searches": analysis["searches"],
            "downloads": analysis["downloads"]
        },
        "gf3_sum": analysis["gf3_sum"],
        "trit_distribution": analysis["trit_distribution"],
        "top_domains": analysis["top_domains"][:50]
    }
    
    with open("browser_history_acset.json", "w") as f:
        json.dump(export_data, f, indent=2, default=str)
    
    print("\n✓ ACSet exported to browser_history_acset.json")
    
    return acset, analysis

if __name__ == "__main__":
    main()
