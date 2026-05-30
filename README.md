# Two Genie Game — proofs & figure code

[![Lean formalization](https://github.com/dlewissandy/two-genie-scripts/actions/workflows/lean.yml/badge.svg)](https://github.com/dlewissandy/two-genie-scripts/actions/workflows/lean.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Public reproducibility artifacts for the paper **_Accessibility and Favorability
of Cooperative Basins in the Two Genie Game_** (Darrell Lewis-Sandy):

- the **mechanically-checked Lean 4 proofs** of its theorems (`sorry`-free,
  verified by the Lean kernel against only the three standard mathlib axioms), and
- the **Python scripts** that generate its figures.

> This repository is the public, citable home of the proofs and figure code. It
> accompanies the manuscript (in preparation); a link to the paper will be added
> here on publication. Everything needed to *independently re-verify the proofs
> and regenerate the figures* is in this repo.

## Repository layout

| Path | What it is |
|---|---|
| [`formalization/`](formalization/) | Self-contained Lean 4 + [mathlib](https://github.com/leanprover-community/mathlib4) development (`TwoGenie`, a Lake package). |
| [`formalization/TwoGenie/README.md`](formalization/TwoGenie/README.md) | **Start here for the proofs** — a claim-by-claim map from each paper result to its Lean theorem, with mechanization status and honest caveats. |
| [`figures/`](figures/) | Standalone [matplotlib](https://matplotlib.org/) scripts that regenerate the paper's phase-diagram figures and the worked numeric "witness" examples. |

## Quick start

```sh
# Verify the proofs (needs `elan`; downloads the pinned mathlib cache)
cd formalization && ./setup.sh && ./b.sh

# Generate the figures (needs Python 3)
pip install -r figures/requirements.txt
python figures/phase_diagram_grid.py
```

## Verifying the Lean proofs

The development pins its toolchain and dependencies exactly
(`lean4:v4.29.0`, mathlib `v4.29.0 @ 8a178386`, recorded in
[`lake-manifest.json`](formalization/TwoGenie/lake-manifest.json)), so the build
is reproducible. You need [`elan`](https://github.com/leanprover/elan), the Lean
toolchain manager.

**Option A — isolated, repo-local (no global Lean needed):**

```sh
cd formalization
./setup.sh   # installs the pinned toolchain into ./formalization/.elan and fetches the mathlib cache
./b.sh       # lake build, against the pinned manifest
```

**Option B — with a global `elan` already installed:**

```sh
cd formalization/TwoGenie
lake exe cache get          # download compiled mathlib oleans for the pinned revision
lake build                  # build all modules — reports no `sorry` warnings
lake env lean Checks.lean   # print the axiom dependency of every headline result
```

Neither path runs `lake update` — that would re-resolve to newer dependencies and
break the pin. `Checks.lean` is the kernel-honesty evidence: every checked
declaration reports only `[propext, Classical.choice, Quot.sound]` and **none**
reports `sorryAx`. The same check runs in
[CI](.github/workflows/lean.yml) on every push and fails the build on any `sorryAx`.

## Generating the figures

Requires Python 3 and three packages (`numpy`, `scipy`, `matplotlib`):

```sh
pip install -r figures/requirements.txt
```

Each script is standalone and writes its PNG(s) next to itself. Generated images
are **not** committed — run a script to (re)produce its figure:

```sh
python figures/phase_diagram_grid.py
```

The witness scripts (`darker_side_witness.py`, `illegibility_witness.py`) print a
worked numeric example to the console rather than drawing a figure.

A few scripts can *additionally* write a copy into an external directory (e.g. to
refresh a figure embedded in a separate document) when `MANUSCRIPT_FIG_DIR` is set;
when it is unset they write only their local PNG:

```sh
MANUSCRIPT_FIG_DIR=/path/to/target python figures/phase_diagram_grid.py
```

### Figure → script map

| Script | Produces |
|---|---|
| **`phase_diagram_grid.py`** | The headline **4×3 cross-prior phase-diagram grid** (Hill, Pareto I, Lomax, Fréchet × favorable / worst-case / symmetric). Includes a self-check (normalized & antitone tails, maximizer vs. brute force) before drawing. |
| `phase_diagram_frechet.py`, `phase_diagram_lomax.py`, `phase_diagram_pareto.py` | Per-prior **robustness panels** for the Fréchet, Lomax, and Pareto Type I families — the per-family views the grid composes. |
| `phase_diagram_misalignment.py` | The darker-side extension's **(u_d, θ_λ) misalignment plane**. |
| `phase_diagram_sweep.py` | **Misalignment sweep**: u_d (columns) × θ_λ (rows), Hill family. |
| `phase_diagram_misalignment_grid.py` | **Misalignment basin grid** in adoption coordinates. |
| `phase_diagram_combined_contours.py`, `phase_diagram_ud_negative.py`, `phase_diagram_symmetric_ab.py` | Single-panel Hill plots (favorable u_d>0 / worst-case u_d<0 / symmetric a/b=1). Legacy reference views, superseded by the cross-prior grid. |
| `darker_side_witness.py` | Numeric **witness** (console): a single-step audit bound, then deliberation that drives community welfare down while the audit score rises. |
| `illegibility_witness.py` | Numeric **witness** (console): the minimal legibility-window race. |

The phase-diagram scripts evaluate the *same* basin-certificate formulas
(`π_low`, `π_high`, `π_bind` and the prior tails) that are kernel-checked in the
Lean development — see `formalization/TwoGenie/Priors/*.lean`. The Lean side
certifies the structure; the float evaluation lives in Python because mathlib's
`Real.rpow` is noncomputable.

## Provenance & reproducibility

- Lean toolchain `leanprover/lean4:v4.29.0`; mathlib `v4.29.0 @ 8a178386`
  (pinned in `lake-manifest.json`). No custom axioms; no `sorry`.
- The Lean proof terms were developed with AI assistance (Claude, Anthropic). The
  Lean **kernel**, not the assistant, certifies correctness — the disclosure is
  about provenance of effort, not of correctness.

## How to cite

If you use this work, please cite both the paper and this software. See
[`CITATION.cff`](CITATION.cff); a BibTeX entry for the software artifact:

```bibtex
@software{lewissandy_two_genie_scripts,
  author  = {Lewis-Sandy, Darrell},
  title   = {Two Genie Game --- Lean 4 formalization and figure scripts},
  year    = {2026},
  url     = {https://github.com/dlewissandy/two-genie-scripts},
  license = {MIT}
}
```

## License

[MIT](LICENSE) © 2026 Darrell Lewis-Sandy.
