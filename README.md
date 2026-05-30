# two-genie-scripts

Public reproducibility artifacts for the paper *Accessibility and Favorability
of Cooperative Basins in the Two Genie Game* (Darrell Lewis-Sandy): the
mechanically-checked Lean 4 proofs of its theorems, and the Python scripts that
generate its figures.

## Contents

- **`formalization/`** — a self-contained [Lean 4](https://lean-lang.org/) +
  [mathlib](https://github.com/leanprover-community/mathlib4) development
  (`TwoGenie`, a Lake package) that mechanically verifies the paper's
  mathematics. The development is `sorry`-free: every headline result is checked
  by the Lean kernel against only the three standard axioms
  `[propext, Classical.choice, Quot.sound]`. See
  [`formalization/TwoGenie/README.md`](formalization/TwoGenie/README.md) for the
  claim-by-claim map from paper results to Lean theorems.
- **`figures/`** — standalone [matplotlib](https://matplotlib.org/) scripts that
  generate the paper's phase-diagram figures and the worked "witness" examples.

## Building the Lean proofs

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager). From `formalization/`:

```sh
./setup.sh   # one-time: install the pinned toolchain + download the mathlib cache
./b.sh       # build (lake build) in an isolated, repo-local elan home
```

Or, with a global `elan` already installed:

```sh
cd formalization/TwoGenie
lake exe cache get
lake build
lake env lean Checks.lean   # prints the axiom dependency of every headline result
```

CI ([`.github/workflows/lean.yml`](.github/workflows/lean.yml)) builds the
development and fails if any checked declaration reports `sorryAx`.

## Running the figure scripts

Requires Python 3 with `numpy`, `scipy`, and `matplotlib`. Each script is
standalone and writes its PNG(s) next to itself:

```sh
cd figures
python phase_diagram_grid.py
```

Some scripts can additionally write a copy into an external directory (e.g. to
refresh a figure embedded elsewhere) when the `MANUSCRIPT_FIG_DIR` environment
variable is set:

```sh
MANUSCRIPT_FIG_DIR=/path/to/figures python phase_diagram_grid.py
```

Generated images are not committed — run the scripts to (re)produce them.

## License

[MIT](LICENSE) © 2026 Darrell Lewis-Sandy.
