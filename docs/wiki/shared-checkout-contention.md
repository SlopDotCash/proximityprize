# Shared-checkout contention: build, git, and probe hygiene under concurrent agents

Learnings from multi-agent operation on one checkout (2026-07-10/11 session; see also
[quickstart](quickstart.md) for the base build rules).

## When `lake env lean` itself hangs (pg-iterate produces empty output)

A long-running `lake build` by another agent holds Lake's workspace lock, which blocks not
only builds but ALSO `lake env lean` — so `scripts/pg-iterate.sh` can hang indefinitely.
Symptoms: background pg-iterate jobs "complete" with EMPTY output, or a trivial
`lake env lean /tmp/sanity.lean` times out.

**Bypass** — construct `LEAN_PATH` manually and call `lean` directly (this is all
`lake env lean` does); elaboration-only, no oleans, no lock:

```bash
LP="$(cygpath -w "$PWD/.lake/build/lib/lean")"
for d in .lake/packages/*/.lake/build/lib/lean; do
  [ -d "$d" ] && LP="$LP;$(cygpath -w "$PWD/$d")"
done
LEAN_PATH="$LP" lean <file.lean>
```

(Windows separator is `;`; `cygpath -w` needed under Git Bash. To also produce an olean
for downstream imports, add `-o <path>.olean` — a later `lake build` will rebuild it
properly with traces.)

Per-checkout lock acquisition in `scripts/lake-locked.sh` times out after 7200s by default;
the machine-wide slot wait has no timeout. Before assuming the holder is hung, read
`.lake/agent-build.lock/owner` and verify that process with `ps`, then inspect the heartbeat.
A stale heartbeat alone does not prove the process has stopped. Healthy holders running
2–4 h have been observed.

Each acquired lock now gets its own heartbeat worker immediately. In particular, the
checkout heartbeat continues while all machine-wide slots are occupied. Starting heartbeats
only after acquiring both locks made a live waiter look stale after five minutes, allowing
another invocation to steal its checkout lock and defeat serialization. The default heartbeat
interval is 30s; if overriding `LAKE_LOCKED_HEARTBEAT_SECS`, keep it below
`LAKE_LOCKED_STALE_SECS`.

`python3 scripts/tests/test_lake_locked.py` exercises this case with two competing invocations,
a fake Lake executable, and isolated temporary lock directories. It verifies that a wait longer
than the stale threshold preserves checkout ownership, both invocations run serially, and their
locks are released. `scripts/validate.sh` runs the regression before invoking Lean.

## Git under concurrent agents

- `fatal: Unable to create .git/index.lock` — check `stat .git/index.lock` and
  `ps aux | grep git`. A zero-byte lock tens of minutes old with NO git process alive is
  stale (typically left by a killed/timed-out git command) and safe to remove. A fresh
  lock belongs to a live agent: wait.
- The local branch can be reset/rebased under you by another agent between your commit and
  your push. If your commit vanishes from `HEAD` (`git merge-base --is-ancestor <sha> HEAD`
  fails) it is NOT lost: push the sha to a side branch
  (`git push origin <sha>:refs/heads/<name>`) and merge server-side via a PR
  (`gh pr create` + `gh pr merge`) — this avoids fighting over the shared working tree.
- Expect non-fast-forward rejections routinely; loop `git pull --no-rebase` + `git push`
  until accepted, and re-verify afterwards that origin actually contains your sha
  (`git branch -r --contains <sha>`).

## Probe output discipline

GitHub rejects pushes containing any blob over 100 MB — and a crash-looping
multiprocessing probe can write GIGABYTES of repeated tracebacks into its log
(observed: 1.5 GB, which then required a history rewrite to un-commit). Rules:

- Never `git add` a probe output without checking its size.
- Truncate crash spam to the meaningful result record plus a short crash note before
  committing.
- On Windows, guard multiprocessing probes against the WinError-5 spawn crash-loop
  (fewer workers, spawn-safe `__main__`, and never run CPU-saturating probes while the
  machine is build-saturated).
