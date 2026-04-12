# Text Map Painter (map_editor5)

Text Map Painter is a Tkinter-based editor for building and editing ASCII maps.
It is designed for MUD/roguelike style map workflows where fast selection and
terrain stamping matter more than tile graphics.

## Run

```bash
python map_editor5.py
```

## Core Features

- Freeform brush selection with adjustable brush size (`1x1` through `10x10`)
- Space-only selection mode (only selects blank cells)
- Type-to-fill for selected regions
- Undo support (`Ctrl+Z`)
- Biome generation menus for:
  - Forest
  - Grasslands
  - Swamp
  - Sand
  - Dry Sand

## New/Updated Features

### 1. Smart Select (replaces Ocean Fill)

`Smart Select` is now used to capture large blank regions safely.

- Works by arming selection from the `Smart Select` menu, then clicking a blank cell
- Expands through contiguous blank areas using run/adjacency rules
- Helps avoid accidental spillover into narrow or isolated gaps
- Supports presets and `Custom...` options:
  - minimum run length
  - adjacency threshold
  - minimum region size
  - replace selection vs add to current selection

### 2. Extra Spaces Slider

The top controls now include two sliders side by side:

- `Randomness`
- `Extra Spaces`

`Extra Spaces` defaults to `0%`.

- At `25%`, each inserted cell has a 25% chance to become a space
- At `100%`, all inserted cells become spaces

This affects typed fills and biome insert output.

### 3. Default Map Creation

You can now create a blank map directly from the app:

- `File -> Default Map`
- Enter:
  - `X size (columns)`
  - `Y size (rows)`
- The current canvas is replaced with a new blank map of that size

### 4. Grasslands Tuning

Grasslands are tuned to be mostly `.` with some `,` and only rare `f`
(no dense `F` output).

### 5. Dry Sand Crack Logic

Dry Sand no longer includes dune shape options.

Dry Sand now focuses on cracked-ground behavior:

- `explosion` creates cracks that radiate away from center
- `implosion` creates cracks converging toward center
- `patchy`, `irregular`, and `spotty` remain available for variation

## Useful Controls

- `Left click / drag`: brush-select cells
- `Ctrl + Left click`: remove cells from selection
- `Tab`: toggle space-only selection
- `Alt + A`: toggle selection mode label/state
- `Escape`: clear selection
- `Ctrl + Z`: undo last edit

## Notes

- Saved maps are plain text (`.txt`)
- Rows are maintained as fixed-width in memory based on current map dimensions
