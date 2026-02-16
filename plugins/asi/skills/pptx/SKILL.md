---
name: pptx
description: Presentation creation, editing, and analysis. When Claude needs to work
version: 1.0.0
---


# PowerPoint Processing

## Creating Presentations (Python)

```python
from pptx import Presentation
from pptx.util import Inches, Pt

prs = Presentation()

# Add title slide
title_slide_layout = prs.slide_layouts[0]
slide = prs.slides.add_slide(title_slide_layout)
title = slide.shapes.title
subtitle = slide.placeholders[1]
title.text = "Hello, World!"
subtitle.text = "python-pptx demo"

# Add content slide
bullet_slide_layout = prs.slide_layouts[1]
slide = prs.slides.add_slide(bullet_slide_layout)
shapes = slide.shapes
title_shape = shapes.title
body_shape = shapes.placeholders[1]
title_shape.text = "Key Points"
tf = body_shape.text_frame
tf.text = "First bullet point"
p = tf.add_paragraph()
p.text = "Second bullet point"
p.level = 1

prs.save('presentation.pptx')
```

## Adding Images

```python
from pptx.util import Inches

blank_layout = prs.slide_layouts[6]
slide = prs.slides.add_slide(blank_layout)

left = Inches(1)
top = Inches(1)
width = Inches(5)
slide.shapes.add_picture('image.png', left, top, width=width)
```

## Adding Tables

```python
rows, cols = 3, 4
left = Inches(1)
top = Inches(2)
width = Inches(6)
height = Inches(1.5)

table = slide.shapes.add_table(rows, cols, left, top, width, height).table

# Set column widths
table.columns[0].width = Inches(2)

# Add content
table.cell(0, 0).text = "Header 1"
table.cell(1, 0).text = "Data 1"
```

## Adding Charts

```python
from pptx.chart.data import CategoryChartData
from pptx.enum.chart import XL_CHART_TYPE

chart_data = CategoryChartData()
chart_data.categories = ['East', 'West', 'Midwest']
chart_data.add_series('Sales', (19.2, 21.4, 16.7))

x, y, cx, cy = Inches(2), Inches(2), Inches(6), Inches(4.5)
slide.shapes.add_chart(
    XL_CHART_TYPE.COLUMN_CLUSTERED, x, y, cx, cy, chart_data
)
```

## Editing Existing Presentations

```python
prs = Presentation('existing.pptx')

# Access slides
for slide in prs.slides:
    for shape in slide.shapes:
        if shape.has_text_frame:
            print(shape.text_frame.text)

# Modify text
slide = prs.slides[0]
slide.shapes.title.text = "New Title"

prs.save('modified.pptx')
```

## Best Practices

- Use slide layouts for consistency
- Keep text minimal, use visuals
- Use Inches() or Pt() for sizing
- Save frequently during creation



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.