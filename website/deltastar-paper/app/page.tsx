import { CopyCommand } from "@/components/CopyCommand";
import research from "@/data/research.json";

const repo = "https://github.com/SlopDotCash/proximityprize";
const source = `${repo}/blob/${research.sourceCommit}`;
const researchRoot = `${source}/Research/ProximityPrize`;
const base = process.env.PAGES_BASE_PATH || "";

export default function Page() {
  return (
    <main id="main">
      <header>
        <p className="eyebrow">Independent research · Lean 4</p>
        <h1>Proximity Prize</h1>
        <p className="intro">How much error can Reed–Solomon codes tolerate?</p>
        <p>We study this question with formal proofs and exact computations.
          The prize conjecture remains open.</p>
        <nav aria-label="Main navigation">
          <a href="#research">Research</a>
          <a href="#open">Open work</a>
          <a href="#contribute">Contribute</a>
          <a href={repo}>GitHub ↗</a>
        </nav>
      </header>

      <section aria-labelledby="problem-title">
        <h2 id="problem-title">The problem</h2>
        <p>Reed–Solomon codes add redundancy to a message so it can be recovered
          after errors. They also help cryptographic systems check large computations.
          The <a href="https://proximityprize.org/">Ethereum Foundation’s Proximity Prize</a> asks
          for stronger guarantees about these codes.</p>
        <p>The Johnson bound is a known error threshold. The challenge is to go
          beyond it under the prize’s precise conditions, including its small bound
          on the number of possible messages. We also study mutual correlated
          agreement (MCA), which concerns agreement among related words.</p>
      </section>

      <section id="research" aria-labelledby="research-title">
        <h2 id="research-title">Latest research</h2>
        <p className="muted">Research snapshot: 6 September 2026</p>
        <h3>Hidden-derivative interpolation</h3>
        <p>The new approach uses derivatives inside an auxiliary polynomial to
          constrain possible messages. The repository contains Lean proofs of the
          interpolation core at every derivative order, plus exact integer
          certificates for selected parameters.</p>
        <div className="table-scroll" tabIndex={0} role="region" aria-label="Interpolation certificate comparison">
          <table>
            <caption>Selected certificates at code length 262,144. Radii are fractions of errors, rounded to five decimals.</caption>
            <thead><tr><th scope="col">Code rate</th><th scope="col">Johnson radius</th><th scope="col">Interpolation radius</th></tr></thead>
            <tbody>{research.records.map((r) => (
              <tr key={r.rate}><th scope="row">1/{r.rate}</th><td>{r.johnson}</td><td>{r.radius}</td></tr>
            ))}</tbody>
          </table>
        </div>
        <p>These certificates support the interpolation step. They do not meet the
          prize’s list-size budget or prove its MCA claim. The rate-1/16 entry is
          feasible; its exact threshold is not asserted. A full list-decoding
          conclusion also uses an external theorem and is not yet an end-to-end
          Lean proof.</p>
        <p className="sources"><a href={`${source}/scripts/probes/hdd_certificates.py`}>Integer certificates</a>
          <a href={`${researchRoot}/Frontier/_HDdInterpolationCore.lean`}>Lean core</a>
          <a href={`${source}/docs/kb/deltastar-hdd-cap-design-2026-09-06.md`}>Research note</a></p>

        <h3>A correction to the strip approach</h3>
        <p>A Lean refutation shows that the master hypothesis used by the SYZ46
          conditional lower bound is false. That lower bound needs a new,
          satisfiable hypothesis. The separately proved upper bound is unaffected.</p>
        <p className="sources"><a href={`${researchRoot}/Frontier/_SW1_F3_MasterHypothesisVacuous.lean`}>Refutation and theorem statements</a></p>

        <h3>Earlier results</h3>
        <p>The project contains exact thresholds for finite examples, general
          reductions, energy lower bounds, and counterexamples to proposed proof
          methods. Each result has a stated scope; finite examples do not establish
          the production theorem.</p>
        <p className="sources"><a href={`${researchRoot}/DOSSIER.md`}>Research dossier</a>
          <a href={`${researchRoot}/DISPROOF_LOG.md`}>Counterexamples and corrections</a></p>
      </section>

      <section id="open" aria-labelledby="open-title">
        <h2 id="open-title">What remains open</h2>
        <p>The current production proof needs both a worst-case character-sum
          bound (the BGK input) and an incidence bound. A character-sum estimate
          alone is not enough.</p>
        <p>The final argument must also reconcile the maximum and supremum
          definitions of the threshold, prove matching bounds at the sponsor’s
          parameters, and pass an independent audit with no unproved assumptions.</p>
        <p><a href={`${repo}/issues/164`}>Current proof and completion tracker →</a></p>
      </section>

      <section id="contribute" aria-labelledby="contribute-title">
        <h2 id="contribute-title">Contribute</h2>
        <p>Start with the current research and open pull requests. Choose one
          precise claim, check it, and report the result with its assumptions and
          reproduction steps. A verified counterexample is useful too.</p>
        <p>To work with a coding agent, give it this instruction:</p>
        <CopyCommand command="Read https://proximityprize.pages.dev/mission.md and work on one verifiable research result." />
        <p className="sources"><a href={`${base}/mission.md`}>Mission</a>
          <a href={`${base}/skill.md`}>Claude Code skill</a>
          <a href={`${base}/codex.md`}>Codex guide</a>
          <a href={`${repo}/pulls`}>Open pull requests</a></p>
      </section>

      <footer>
        <p>An independent project built on <a href="https://github.com/Verified-zkEVM/ArkLib">ArkLib</a> and Mathlib.
          Research and authorship are recorded in the <a href={`${repo}/graphs/contributors`}>repository</a>.</p>
        <p><a href={`${repo}/commit/${research.sourceCommit}`}>Source {research.sourceCommit.slice(0, 7)}</a></p>
      </footer>
    </main>
  );
}
