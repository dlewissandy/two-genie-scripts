#!/bin/sh
# One-time setup: install the pinned Lean toolchain into a repo-local elan home
# and download the compiled mathlib cache. Paths are resolved relative to this
# file so the script works wherever the repo is checked out.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
export ELAN_HOME="$HERE/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
cd "$HERE/TwoGenie"
echo "[1/2] installing pinned toolchain leanprover/lean4:v4.29.0"
elan toolchain install leanprover/lean4:v4.29.0
# NOTE: deliberately no `lake update` — the committed lake-manifest.json pins the
# exact mathlib revision, and `lake update` would re-resolve to newer deps and
# break reproducibility. `lake exe cache get` materializes the pinned deps.
echo "[2/2] lake exe cache get (downloading compiled mathlib oleans for the pinned revision)"
lake exe cache get
echo "SETUP_DONE_OK — now run ./b.sh (or 'lake build') to build."
