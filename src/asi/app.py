"""
ASI TUI Application - Textual-based skill browser with GF(3) visualization
"""

from textual.app import App, ComposeResult
from textual.containers import Container, Horizontal, Vertical, ScrollableContainer
from textual.widgets import Header, Footer, Static, DataTable, Input, Label, Button
from textual.binding import Binding
from textual.reactive import reactive
from rich.text import Text
from rich.panel import Panel
from pathlib import Path
import math


# GF(3) trit symbols and colors
TRIT_SYMBOLS = {1: "+", 0: "○", -1: "−"}
TRIT_COLORS = {1: "green", 0: "cyan", -1: "magenta"}
TRIT_NAMES = {1: "PLUS", 0: "ERGODIC", -1: "MINUS"}


def splitmix32(seed: int, index: int) -> tuple[float, float, float]:
    """Generate deterministic LCH color from seed and index"""
    state = abs(seed)
    for _ in range(index + 1):
        state = ((state * 1103515245 + 12345) % (2**31))
    
    # Generate L, C, H
    l_val = 10.0 + (state % 1000) / 1000.0 * 85.0
    state = ((state * 1103515245 + 12345) % (2**31))
    c_val = (state % 1000) / 1000.0 * 100.0
    state = ((state * 1103515245 + 12345) % (2**31))
    h_val = (state % 1000) / 1000.0 * 360.0
    
    return l_val, c_val, h_val


def hue_to_polarity(hue: float) -> str:
    """Map hue to Girard polarity"""
    if hue < 60 or hue >= 300:
        return "positive"
    elif 180 <= hue < 300:
        return "negative"
    else:
        return "neutral"


class GF3Meter(Static):
    """Visual GF(3) balance meter"""
    
    plus_count = reactive(0)
    ergodic_count = reactive(0)
    minus_count = reactive(0)
    
    def render(self) -> Text:
        total = self.plus_count - self.minus_count
        mod3 = total % 3
        balanced = mod3 == 0
        
        text = Text()
        text.append("GF(3) ", style="bold")
        text.append(f"+{self.plus_count}", style="green")
        text.append(" | ")
        text.append(f"○{self.ergodic_count}", style="cyan")
        text.append(" | ")
        text.append(f"−{self.minus_count}", style="magenta")
        text.append(f" = {total} ≡ {mod3} ")
        
        if balanced:
            text.append("✓", style="bold green")
        else:
            text.append("✗", style="bold red")
        
        return text


class ColorSwatch(Static):
    """Display SPI color for current selection"""
    
    seed = reactive(1069)
    index = reactive(0)
    
    def render(self) -> Text:
        l, c, h = splitmix32(self.seed, self.index)
        polarity = hue_to_polarity(h)
        pol_symbol = {"positive": "+", "negative": "−", "neutral": "○"}[polarity]
        
        text = Text()
        text.append("SPI Color ", style="bold")
        text.append(f"L:{l:.0f} C:{c:.0f} H:{h:.0f}° ", style="dim")
        text.append(f"[{pol_symbol}]", style=TRIT_COLORS.get(
            {"positive": 1, "negative": -1, "neutral": 0}[polarity], "white"
        ))
        
        return text


class SkillBrowser(DataTable):
    """Interactive skill browser with GF(3) annotations"""
    
    BINDINGS = [
        Binding("j", "cursor_down", "Down"),
        Binding("k", "cursor_up", "Up"),
        Binding("enter", "select_skill", "Select"),
    ]


class SkillDetail(Static):
    """Show details for selected skill"""
    
    skill_name = reactive("")
    skill_data = reactive({})
    
    def render(self) -> Text:
        if not self.skill_name:
            return Text("Select a skill to view details", style="dim italic")
        
        text = Text()
        text.append(f"Skill: {self.skill_name}\n", style="bold")
        
        trit = self.skill_data.get("trit", 0)
        text.append(f"Trit: {TRIT_SYMBOLS.get(trit, '?')} ({TRIT_NAMES.get(trit, '?')})\n", 
                   style=TRIT_COLORS.get(trit, "white"))
        
        if desc := self.skill_data.get("description"):
            text.append(f"\n{desc}\n", style="dim")
        
        return text


class ASIApp(App):
    """Algebraic Superintelligence TUI"""
    
    CSS = """
    Screen {
        layout: grid;
        grid-size: 2;
        grid-columns: 2fr 1fr;
    }
    
    #skill-list {
        height: 100%;
        border: solid $primary;
    }
    
    #sidebar {
        height: 100%;
        padding: 1;
    }
    
    #gf3-meter {
        height: 3;
        padding: 1;
        background: $surface;
        border: solid $secondary;
    }
    
    #color-swatch {
        height: 3;
        padding: 1;
        background: $surface;
        border: solid $secondary;
    }
    
    #skill-detail {
        height: 1fr;
        padding: 1;
        background: $surface;
        border: solid $secondary;
    }
    
    Header {
        dock: top;
    }
    
    Footer {
        dock: bottom;
    }
    """
    
    BINDINGS = [
        Binding("q", "quit", "Quit"),
        Binding("r", "refresh", "Refresh"),
        Binding("1", "filter_plus", "+1"),
        Binding("0", "filter_ergodic", "0"),
        Binding("9", "filter_minus", "-1"),
        Binding("a", "filter_all", "All"),
        Binding("t", "run_tests", "Tests"),
    ]
    
    TITLE = "Plurigrid ASI"
    SUB_TITLE = "Algebraic Superintelligence"
    
    skills: list[dict] = []
    filter_trit: int | None = None
    
    def compose(self) -> ComposeResult:
        yield Header()
        
        with Container(id="skill-list"):
            yield SkillBrowser(id="browser")
        
        with Vertical(id="sidebar"):
            yield GF3Meter(id="gf3-meter")
            yield ColorSwatch(id="color-swatch")
            yield SkillDetail(id="skill-detail")
        
        yield Footer()
    
    def on_mount(self) -> None:
        self.load_skills()
        self.populate_table()
    
    def load_skills(self) -> None:
        """Load skills from directory"""
        # Find ASI root
        asi_root = Path(__file__).parent.parent.parent
        skills_dir = asi_root / "skills"
        
        self.skills = []
        
        if not skills_dir.exists():
            return
        
        for i, skill_dir in enumerate(sorted(skills_dir.iterdir())):
            if skill_dir.is_dir() and not skill_dir.name.startswith('.'):
                skill = {
                    "name": skill_dir.name,
                    "path": str(skill_dir),
                    "index": i,
                    "trit": 0,  # Default
                    "description": "",
                }
                
                # Try to read manifest
                manifest = skill_dir / "manifest.toml"
                if manifest.exists():
                    try:
                        import tomllib
                        with open(manifest, "rb") as f:
                            data = tomllib.load(f)
                            skill["trit"] = data.get("trit", 0)
                            skill["description"] = data.get("description", "")
                    except Exception:
                        pass
                
                self.skills.append(skill)
        
        # Update GF(3) meter
        meter = self.query_one("#gf3-meter", GF3Meter)
        meter.plus_count = sum(1 for s in self.skills if s["trit"] == 1)
        meter.ergodic_count = sum(1 for s in self.skills if s["trit"] == 0)
        meter.minus_count = sum(1 for s in self.skills if s["trit"] == -1)
    
    def populate_table(self) -> None:
        """Populate the skill browser table"""
        browser = self.query_one("#browser", SkillBrowser)
        browser.clear(columns=True)
        
        browser.add_columns("Trit", "Skill", "Description")
        
        filtered = self.skills
        if self.filter_trit is not None:
            filtered = [s for s in self.skills if s["trit"] == self.filter_trit]
        
        for skill in filtered:
            trit = skill["trit"]
            symbol = TRIT_SYMBOLS.get(trit, "?")
            color = TRIT_COLORS.get(trit, "white")
            
            browser.add_row(
                Text(symbol, style=color),
                skill["name"],
                skill.get("description", "")[:40],
                key=skill["name"]
            )
    
    def on_data_table_row_selected(self, event: DataTable.RowSelected) -> None:
        """Handle skill selection"""
        skill_name = str(event.row_key.value)
        skill = next((s for s in self.skills if s["name"] == skill_name), None)
        
        if skill:
            detail = self.query_one("#skill-detail", SkillDetail)
            detail.skill_name = skill_name
            detail.skill_data = skill
            
            swatch = self.query_one("#color-swatch", ColorSwatch)
            swatch.index = skill.get("index", 0)
    
    def action_filter_plus(self) -> None:
        self.filter_trit = 1
        self.populate_table()
        self.sub_title = "Filter: PLUS (+1)"
    
    def action_filter_ergodic(self) -> None:
        self.filter_trit = 0
        self.populate_table()
        self.sub_title = "Filter: ERGODIC (0)"
    
    def action_filter_minus(self) -> None:
        self.filter_trit = -1
        self.populate_table()
        self.sub_title = "Filter: MINUS (-1)"
    
    def action_filter_all(self) -> None:
        self.filter_trit = None
        self.populate_table()
        self.sub_title = "Algebraic Superintelligence"
    
    def action_refresh(self) -> None:
        self.load_skills()
        self.populate_table()
    
    def action_run_tests(self) -> None:
        """Run jank/SCI tests"""
        import subprocess
        asi_root = Path(__file__).parent.parent.parent
        test_runner = asi_root.parent / "run_jank_sci_tests.clj"
        
        if test_runner.exists():
            self.exit(message="Running tests...")
            subprocess.run(["bb", str(test_runner)], cwd=asi_root.parent)


def main():
    app = ASIApp()
    app.run()


if __name__ == "__main__":
    main()
