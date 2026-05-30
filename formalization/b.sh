#!/bin/sh
# Build the TwoGenie Lean development using a repo-local, isolated elan install
# (created by setup.sh next to this script). Paths are resolved relative to this
# file so the script works wherever the repo is checked out.
HERE="$(cd "$(dirname "$0")" && pwd)"
export ELAN_HOME="$HERE/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
cd "$HERE/TwoGenie"
exec lake build "$@"
