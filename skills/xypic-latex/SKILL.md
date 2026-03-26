---
name: xypic-latex
description: "XY-pic commutative diagrams in LaTeX with Emacs/AUCTeX preview"
version: 1.0.0
---

# XY-pic LaTeX Diagrams

Typeset commutative diagrams, automata, and categorical constructions using XY-pic in LaTeX, with inline Emacs preview via AUCTeX.

## Setup

### Preamble

```latex
\usepackage[all,cmtip]{xy}
```

- `all` loads every XY-pic extension (matrix, arrow, curve, frame, etc.)
- `cmtip` uses Computer Modern arrowheads (cleaner than default)

### Emacs / AUCTeX preview

Add to init.el for inline `C-c C-p C-p` preview of xymatrix environments:

```elisp
(eval-after-load "preview"
  '(add-to-list 'preview-default-preamble "\\PreviewEnvironment{xymatrix}" t))
```

Ensure PDF mode is active: `C-c C-t C-p`.

## Core Syntax

Diagrams are matrices. `&` separates columns, `\\` separates rows. Arrows use `\ar[direction]` where direction combines: `u`(up), `d`(down), `l`(left), `r`(right).

### Commutative Square

```latex
\[
\xymatrix{
  A \ar[r]^f \ar[d]_g & B \ar[d]^h \\
  C \ar[r]_k           & D
}
\]
```

### Arrow Labels

| Syntax         | Position                    |
|----------------|-----------------------------|
| `\ar[r]^f`     | label above/right of arrow  |
| `\ar[r]_f`     | label below/left of arrow   |
| `\ar[r]\|f`    | label on arrow (breaks it)  |
| `\ar[r]|-{f}`  | label in gap on arrow       |

### Arrow Styles

```latex
\ar@{->}[r]        % normal (default)
\ar@{.>}[r]        % dotted
\ar@{=>}[r]        % double (natural transformation)
\ar@{-->}[r]       % dashed
\ar@{~>}[r]        % squiggly
\ar@{->>}[r]       % two-headed (epi)
\ar@{^{(}->}[r]    % hook (mono)
\ar@{=}[r]         % equals
\ar@{}[r]          % phantom (for label placement only)
```

### Curved Arrows

```latex
\ar@/^/[r]^f       % curve up/right
\ar@/_/[r]_g       % curve down/left
\ar@/^1pc/[r]      % curve with specific radius
\ar@(ur,dr)[r]     % loop from upper-right to down-right
```

### Spacing Control

```latex
\xymatrix@R=2pc@C=3pc{...}    % set row/column spacing
\xymatrix@C-1pc{...}           % reduce column spacing by 1pc
\xymatrix@1{...}               % entries are 1em wide
```

## Common Diagram Patterns

### Pullback / Fiber Product

```latex
\[
\xymatrix{
  U \ar@/_/[ddr]_y \ar@/^/[drr]^x \ar@{.>}[dr]|-{(x,y)} \\
  & X \times_Z Y \ar[d]^q \ar[r]_p & X \ar[d]_f \\
  & Y \ar[r]^g                      & Z
}
\]
```

### Short Exact Sequence

```latex
\[
\xymatrix{
  0 \ar[r] & A \ar[r]^i & B \ar[r]^p & C \ar[r] & 0
}
\]
```

### Adjunction

```latex
\[
\xymatrix@C=4pc{
  \mathcal{C} \ar@<1ex>[r]^{F} \ar@{}[r]|{\perp}
  & \mathcal{D} \ar@<1ex>[l]^{G}
}
\]
```

### Natural Transformation (2-cell)

```latex
\[
\xymatrix{
  \mathcal{C} \rtwocell^F_G{\alpha} & \mathcal{D}
}
\]
```

(Requires `\usepackage[all,2cell]{xy} \UseTwocells`)

### Long Exact Sequence (wrapping)

```latex
\[
\xymatrix{
  \cdots \ar[r] & H_n(A) \ar[r]^{i_*} & H_n(X) \ar[r]^{j_*}
  & H_n(X,A) \ar[dll]_{\partial} \\
  & H_{n-1}(A) \ar[r]^{i_*} & H_{n-1}(X) \ar[r] & \cdots
}
\]
```

### Cube Diagram

```latex
\[
\xymatrix{
  A \ar[rr] \ar[dd] \ar[dr] && B \ar[dd] \ar[dr] \\
  & C \ar[rr] \ar[dd]       && D \ar[dd]          \\
  E \ar[rr] \ar[dr]         && F \ar[dr]           \\
  & G \ar[rr]                && H
}
\]
```

### Automaton (DFA)

```latex
\[
\xymatrix{
  *+[o][F-]{q_0} \ar[r]^a \ar@(ul,dl)[]_b
  & *+[o][F=]{q_1} \ar@/^/[r]^a \ar@(ur,dr)[]^b
  & *+[o][F-]{q_2} \ar@/^/[l]^{a,b}
}
\]
```

- `*+[o][F-]` = circle, single border
- `*+[o][F=]` = circle, double border (accepting state)

## Tips

- **Diagonal arrows**: `\ar[dr]` goes down-right, `\ar[ull]` goes up-left-left (two columns)
- **Phantom arrows** `\ar@{}[r]|{\cong}` place a symbol between entries without drawing
- **Compile twice** if arrow positions look wrong on first pass
- **Debugging**: add `\entrymodifiers={+!!<0pt,\fontdimen22\textfont2>}` to baseline-align entries
- **2-cells**: load `\usepackage[all,2cell]{xy}` and `\UseTwocells` for natural transformations

## Alternative: tikz-cd

For simpler syntax with TikZ backend:

```latex
\usepackage{tikz-cd}
\[
\begin{tikzcd}
  A \arrow[r, "f"] \arrow[d, "g"'] & B \arrow[d, "h"] \\
  C \arrow[r, "k"']                & D
\end{tikzcd}
\]
```

Both are available in `texliveFull`.

## References

- [XY-pic User's Guide (PDF)](https://texdoc.org/serve/xyguide.pdf/0) — official reference
- [Alsani's examples (PDF)](https://sites.math.washington.edu/~reu/docs/xypic.pdf) — beginner walkthrough
- [Milne's CD package comparison](https://www.jmilne.org/not/CDGuide06.pdf) — xy-pic vs tikz-cd vs amscd
- [Debray's automata guide (PDF)](https://adebray.github.io/lecture_notes/using_xy.pdf) — XY-pic for DFA/NFA
- Run `texdoc xypic` locally for offline docs
