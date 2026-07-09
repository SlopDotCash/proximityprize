#!/usr/bin/env bash

# Serialized lake wrapper for multi-agent checkouts.
#
# Problem this solves (observed 2026-06-11): N agents each run `lake build`
# concurrently in the same checkout. Each lake spawns ~#cores lean workers, so
# 7 builds -> 60+ lean.exe on 12 cores, olean writes race each other and with
# `lake exe cache get`, artifacts corrupt, builds die at code 143, and agents
# whose mathlib cache got clobbered silently fall back to compiling all of
# Mathlib from source. The box pegs at 100% CPU and nothing finishes.
#
# Usage: drop-in replacement for `lake`:
#   ./scripts/lake-locked.sh build ArkLib.Some.Target
#   ./scripts/lake-locked.sh exe cache get
#
# What it does before running lake:
#   1. Per-checkout exclusive lock (.lake/agent-build.lock) — at most one lake
#      invocation per checkout, ever. A second invocation waits, then gets a
#      warm incremental build instead of a corrupting race.
#   2. Machine-wide build slots (~/.cache/lake-build-slots, default 2) — caps
#      total concurrent lake invocations across ALL checkouts/worktrees.
#   3. Mathlib cache guard — if .lake/packages/mathlib exists but its root
#      olean is missing, runs `lake exe cache get` first (inside the lock) so
#      the build never recompiles Mathlib from source.
#
# Locks are directories (mkdir is atomic everywhere, incl. Git Bash on
# Windows) with a heartbeat file refreshed every 30s. A lock whose heartbeat
# is older than LAKE_LOCKED_STALE_SECS (default 300) is presumed dead (its
# holder was killed) and is stolen.
#
# Env knobs:
#   LAKE_LOCKED_SLOTS=N         max machine-wide concurrent builds (default 2)
#   LAKE_LOCKED_STALE_SECS=N    heartbeat age before a lock is stolen (default 300)
#   LAKE_LOCKED_TIMEOUT_SECS=N  max seconds to wait for locks (default 7200)
#   LAKE_LOCKED_DISABLE=1       bypass entirely (plain `lake "$@"`)

set -euo pipefail

if [[ "${LAKE_LOCKED_DISABLE:-0}" == "1" ]]; then
  exec lake "$@"
fi

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$REPO_ROOT"

SLOTS="${LAKE_LOCKED_SLOTS:-2}"
STALE="${LAKE_LOCKED_STALE_SECS:-300}"
TIMEOUT="${LAKE_LOCKED_TIMEOUT_SECS:-7200}"
SLOT_ROOT="${LAKE_LOCKED_SLOT_DIR:-$HOME/.cache/lake-build-slots}"
CHECKOUT_LOCK="$REPO_ROOT/.lake/agent-build.lock"

mkdir -p "$REPO_ROOT/.lake" "$SLOT_ROOT"

now_s() { date +%s; }

# Heartbeat age of a lock dir; prints a huge number if unreadable.
lock_age() {
  local hb
  hb="$(cat "$1/heartbeat" 2>/dev/null || true)"
  if [[ -z "$hb" ]]; then
    # mkdir happened but heartbeat not written yet (or holder died mid-setup):
    # fall back to the dir's own mtime so a fresh lock is not insta-stolen.
    hb="$(stat -c %Y "$1" 2>/dev/null || stat -f %m "$1" 2>/dev/null || echo 0)"
  fi
  echo $(( $(now_s) - hb ))
}

# acquire <lockdir> <label> — blocks until the lock is held.
acquire() {
  local lock="$1" label="$2" started waited age
  started="$(now_s)"
  while :; do
    if mkdir "$lock" 2>/dev/null; then
      now_s > "$lock/heartbeat"
      echo "$$ $label $(pwd)" > "$lock/owner" 2>/dev/null || true
      return 0
    fi
    # Holder may have released between our mkdir and now — retry immediately.
    [[ -d "$lock" ]] || continue
    age="$(lock_age "$lock")"
    if (( age > STALE )); then
      echo "lake-locked: stealing stale $label lock (heartbeat ${age}s old)" >&2
      rm -rf "$lock" 2>/dev/null || true
      continue
    fi
    waited=$(( $(now_s) - started ))
    if (( waited > TIMEOUT )); then
      echo "lake-locked: timed out after ${waited}s waiting for $label lock $lock" >&2
      exit 75
    fi
    if (( waited % 60 < 5 )); then
      echo "lake-locked: waiting for $label lock ($(cat "$lock/owner" 2>/dev/null || echo '?')), ${waited}s..." >&2
    fi
    sleep 5
  done
}

HELD_LOCKS=()
HB_PID=""

release_all() {
  [[ -n "$HB_PID" ]] && kill "$HB_PID" 2>/dev/null || true
  local l
  for l in "${HELD_LOCKS[@]:-}"; do
    [[ -n "$l" ]] && rm -rf "$l" 2>/dev/null || true
  done
}
trap release_all EXIT INT TERM

# 1. Per-checkout lock: serializes all lake invocations in this checkout.
acquire "$CHECKOUT_LOCK" "checkout"
HELD_LOCKS+=("$CHECKOUT_LOCK")

# 2. Machine-wide slot: caps concurrent builds across all checkouts.
SLOT_LOCK=""
while [[ -z "$SLOT_LOCK" ]]; do
  for i in $(seq 1 "$SLOTS"); do
    slot="$SLOT_ROOT/slot-$i"
    if mkdir "$slot" 2>/dev/null; then
      now_s > "$slot/heartbeat"
      echo "$$ $(pwd)" > "$slot/owner" 2>/dev/null || true
      SLOT_LOCK="$slot"
      break
    fi
    if [[ -d "$slot" ]] && (( $(lock_age "$slot") > STALE )); then
      echo "lake-locked: stealing stale build slot $slot" >&2
      rm -rf "$slot" 2>/dev/null || true
    fi
  done
  [[ -z "$SLOT_LOCK" ]] && sleep 5
done
HELD_LOCKS+=("$SLOT_LOCK")

# Refresh heartbeats on everything we hold while the build runs.
(
  while :; do
    for l in "${HELD_LOCKS[@]}"; do
      # Atomic via rename so a concurrent reader never sees a truncated file.
      { now_s > "$l/heartbeat.tmp" && mv -f "$l/heartbeat.tmp" "$l/heartbeat"; } 2>/dev/null || exit 0
    done
    sleep 30
  done
) &
HB_PID=$!

# 3. Mathlib cache guard: never let a build fall back to compiling Mathlib
#    from source because the olean cache is missing or was clobbered.
MATHLIB_PKG="$REPO_ROOT/.lake/packages/mathlib"
if [[ -d "$MATHLIB_PKG" ]] \
   && [[ ! -f "$MATHLIB_PKG/.lake/build/lib/lean/Mathlib.olean" ]] \
   && [[ ! -f "$MATHLIB_PKG/.lake/build/lib/Mathlib.olean" ]]; then
  echo "lake-locked: mathlib olean cache missing — running 'lake exe cache get' first" >&2
  lake exe cache get || echo "lake-locked: cache get failed; continuing (build may be slow)" >&2
fi

lake "$@"
