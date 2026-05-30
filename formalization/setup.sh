#!/bin/sh
# One-time setup: install the pinned Lean toolchain into a repo-local elan home
# and download the compiled mathlib cache. Paths are resolved relative to this
# file so the script works wherever the repo is checked out.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
export ELAN_HOME="$HERE/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
cd "$HERE/TwoGenie"
echo "[1/3] installing pinned toolchain leanprover/lean4:v4.29.0"
elan toolchain install leanprover/lean4:v4.29.0
echo "[2/3] lake update (resolving mathlib + transitive deps)"
lake update
echo "[3/3] lake exe cache get (downloading compiled mathlib oleans)"
lake exe cache get
echo "SETUP_DONE_OK"
