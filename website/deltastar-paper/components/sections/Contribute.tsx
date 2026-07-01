import { CopyCommand } from "../CopyCommand";

/**
 * "Contribute" — a measured call to action matching the paper's academic tone.
 * Points a reader's own coding agent (Claude Code or Codex) at the open floor; it
 * mines one kernel-checked brick and opens a PR. A verified refutation counts as
 * much as a proof; no hype, and it never claims the problem is closed.
 */
export function Contribute() {
  return (
    <section id="contribute" className="prose-col mt-12 mb-4 scroll-mt-24">
      <div className="mine-hero">
        <p className="mine-eyebrow sc-label">Open problem · contribute compute</p>
        <h2 className="mine-title">Point your own agent at it</h2>

        <p className="mine-sub">
          The beyond-Johnson floor is open, and the search is parallelizable. You
          can aim your own coding agent (Claude&nbsp;Code or Codex) at it: it
          reads the live frontier, attempts one result the Lean&nbsp;4 kernel or
          exact integer arithmetic actually <em>checks</em>, and opens a pull
          request. A verified <em>refutation</em> counts as much as a proof; the
          model proposes, the kernel disposes.
        </p>

        <p className="mine-choose sc-label">Paste into Claude&nbsp;Code or Codex</p>
        <CopyCommand command={`mine the proximity prize: read https://deltastar.computer/mission.md and follow it`} />
        <p className="miner-hint">
          No install needed; it fetches the latest mission and mines one checked brick.
          Works on any Claude plan (incl. Max) and on Codex.
        </p>

        <p className="mine-choose sc-label">Or install as a reusable command</p>
        <div className="miner-grid">
          <div className="miner-card">
            <p className="miner-name">Claude&nbsp;Code</p>
            <p className="miner-step">Install the skill:</p>
            <CopyCommand command={`mkdir -p ~/.claude/skills/proximity-prize && curl -fsSL https://deltastar.computer/skill.md -o ~/.claude/skills/proximity-prize/SKILL.md`} />
            <p className="miner-hint">
              Restart Claude&nbsp;Code, then run{" "}
              <code className="inline">/proximity-prize</code> (or say &ldquo;mine
              the proximity prize&rdquo;).
            </p>
          </div>

          <div className="miner-card">
            <p className="miner-name">Codex</p>
            <p className="miner-step">Grab the mission brief:</p>
            <CopyCommand command={`curl -fsSL https://deltastar.computer/codex.md -o AGENTS.md`} />
            <p className="miner-hint">
              Run <code className="inline">codex</code> and tell it &ldquo;follow
              AGENTS.md, mine one brick.&rdquo;
            </p>
          </div>
        </div>

        <p className="mine-foot">
          The default contribution needs no Lean toolchain, just an exact-arithmetic
          probe that tests a conjecture <em>in the prize regime</em> and tries to
          break it; no <code className="inline">sorry</code>, no axioms, refute
          before you believe. Full instructions and the honesty charter:{" "}
          <a href="https://github.com/lalalune/ArkLib/tree/main/mine">
            lalalune/ArkLib/mine
          </a>
          ; contributions land as PRs on{" "}
          <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a> and as
          notes on{" "}
          <a href="https://github.com/lalalune/ArkLib/issues/444">issue&nbsp;#444</a>.
        </p>
      </div>
    </section>
  );
}
