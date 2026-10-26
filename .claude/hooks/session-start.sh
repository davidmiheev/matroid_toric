#!/bin/bash
# SessionStart hook for Claude Code cloud sessions: installs the matroid_toric toolchain.
#   - CAS / combinatorics: Macaulay2, gfan, polymake, Singular, nauty   (apt)
#   - typesetting: XeLaTeX + fonts for docs/thesis-v2, poppler-utils    (apt)
#   - Lean 4 (elan) + prebuilt Mathlib cache for formal/
#   - engine/.venv with mtengine installed, so the mtengine MCP server in .mcp.json starts
# Idempotent: every step is skipped when already done, so cached containers start fast.
# Runs asynchronously; see the echo below.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

# Async: the session starts at once and this script keeps running in the background
# (up to 30 min; a cold install takes ~10-15). Until it finishes, tools may be missing.
echo '{"async": true, "asyncTimeout": 1800000}'

ROOT="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "$0")/../.." && pwd)}"
log() { echo "[session-start] $*" >&2; }

# ---- 0. engine virtualenv (first: only needs python3, and the MCP server needs it)
if [ -f "$ROOT/engine/pyproject.toml" ]; then
  cd "$ROOT/engine"
  if [ ! -x .venv/bin/mtengine-mcp ]; then
    log "creating engine/.venv"
    python3 -m venv .venv
    .venv/bin/pip install -q --upgrade pip
    .venv/bin/pip install -q -e ".[test]"
  else
    log "engine/.venv present"
  fi
fi

# ---- 1. apt packages --------------------------------------------------------------
APT_PKGS=(macaulay2 gfan polymake singular nauty poppler-utils texlive-xetex texlive-fonts-extra)
missing=()
for p in "${APT_PKGS[@]}"; do
  dpkg -s "$p" >/dev/null 2>&1 || missing+=("$p")
done
if [ "${#missing[@]}" -gt 0 ]; then
  log "installing apt packages: ${missing[*]}"
  export DEBIAN_FRONTEND=noninteractive
  # a stale package index gives 404s on moved .debs, so always refresh first
  apt-get update -qq
  apt-get install -y -qq --no-install-recommends "${missing[@]}" >/dev/null \
    || { apt-get update -qq && apt-get install -y -qq --fix-missing --no-install-recommends "${missing[@]}" >/dev/null; }
else
  log "apt packages present"
fi

# ---- 2. Lean toolchain + Mathlib cache --------------------------------------------
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null 2>&1; then
  log "installing elan"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none >/dev/null
fi
if [ -n "${CLAUDE_ENV_FILE:-}" ] && ! grep -q '.elan/bin' "$CLAUDE_ENV_FILE" 2>/dev/null; then
  echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$CLAUDE_ENV_FILE"
fi
if [ -f "$ROOT/formal/lakefile.toml" ]; then
  cd "$ROOT/formal"
  if [ ! -d .lake/packages/mathlib/.lake/build ]; then
    log "fetching Mathlib cache (first run only; several minutes)"
    # quiet on success (its progress bar floods the log); on failure retry with output shown
    lake exe cache get >/dev/null 2>&1 || lake exe cache get
  fi
  log "building formal/"
  lake build >/dev/null
fi

log "done"
