import { CopyCommand } from "@/components/CopyCommand";
import { ProblemVisual } from "@/components/ProblemVisual";
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
          <a href="#problem">The problem</a>
          <a href="#research">Our progress</a>
          <a href="#open">Open work</a>
          <a href="#contribute">Contribute</a>
          <a href={repo}>GitHub ↗</a>
        </nav>
      </header>

      <section id="problem" aria-labelledby="problem-title">
        <h2 id="problem-title">The problem, in plain terms</h2>
        <p>A Reed–Solomon code turns a short message into a longer sequence of
          symbols. The extra symbols let us recover the message when some values
          are wrong. With more errors, several messages may fit. <em>List decoding</em>
          asks how many candidates can remain.</p>
        <ProblemVisual />
        <h3>What the prize asks</h3>
        <p>Find the exact error threshold, δ*, for the codes used in these
          cryptographic checks. One challenge bounds the list of possible
          interleaved messages. The other, mutual correlated agreement (MCA),
          asks when agreement in mixtures of words must have a common explanation
          in the original words.</p>
        <p>The target failure budget can be as small as 2⁻¹²⁸. A useful threshold
          must work for the specified codes and all required inputs, with a proof
          of its limit.</p>
        <figure className="threshold-visual">
          <figcaption>Why researchers look beyond Johnson</figcaption>
          <div className="threshold-labels"><span>0% errors</span><span>50%</span></div>
          <div className="threshold-track" role="img" aria-label="At rate one half, the Johnson list-decoding benchmark is about 29.3 percent errors; the asymptotic list-decoding capacity benchmark is 50 percent. The region between them motivates research; it is not a proved prize guarantee.">
            <div className="johnson-zone">Johnson benchmark</div><div className="research-zone">Beyond Johnson</div>
          </div>
          <div className="threshold-legend"><span><b>29.3%</b> Johnson radius</span><span><b>50%</b> capacity benchmark</span></div>
          <p className="visual-note">Rate 1/2: half the encoded symbols carry message information.
            These are list-decoding benchmarks, not a claimed solution to the prize’s extra conditions.</p>
        </figure>
        <p className="sources"><a href="https://proximityprize.org/">Official challenges</a>
          <a href="https://eprint.iacr.org/2026/680">Definitions and background</a></p>
      </section>

      <section id="research" aria-labelledby="research-title">
        <h2 id="research-title">What we have established</h2>
        <p className="muted">Research snapshot: 6 September 2026</p>
        <h3>Exact thresholds for two finite codes <span className="evidence">Lean proofs</span></h3>
        <p>We proved both sides of the MCA threshold for two small Reed–Solomon
          codes: δ* = 1/4. These give exact reference cases for checking general
          arguments, rather than only upper or lower estimates.</p>
        <div className="table-scroll" tabIndex={0} role="region" aria-label="Exact finite MCA thresholds">
          <table>
            <caption>Both codes have rate 1/2. The field size, code size, and allowed failure budget are part of each result.</caption>
            <thead><tr><th scope="col">Code</th><th scope="col">Failure budget ε*</th><th scope="col">Exact δ*</th></tr></thead>
            <tbody>
              <tr><th scope="row">4 symbols over F₅ · degree &lt; 2</th><td>2/5</td><td>1/4</td></tr>
              <tr><th scope="row">8 symbols over F₁₇ · degree &lt; 4</th><td>2/17 ≤ ε* &lt; 7/17</td><td>1/4</td></tr>
            </tbody>
          </table>
        </div>
        <p>These pins use the repository’s supremum definition: the boundary itself
          is not an allowed radius at these budgets. They are finite results,
          not a pin at the prize’s 2⁻¹²⁸ budget.</p>
        <p className="sources"><a href={`${source}/ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean`}>F₅ proof</a>
          <a href={`${source}/ArkLib/Data/CodingTheory/ProximityGap/DeltaStarSecondPinF17Maximal.lean`}>F₁₇ proof and budget range</a></p>

        <h3>Stronger bounds on additive collisions <span className="evidence">Lean proof</span></h3>
        <p>We extended a stronger lower bound on equal-sum tuple pairs to every
          depth r ≥ 3. It strictly improves the earlier adjacent-swap bound for
          sets with at least two elements, over any finite field. These collision
          counts are ingredients in character-sum analysis.</p>
        <details><summary>The bound and its scope</summary>
          <p>For a set of N elements, Eᵣ counts pairs of r-tuples with the same sum.
            We proved Eᵣ ≥ 3Nʳ − 2Nʳ⁻², improving 2Nʳ − Nʳ⁻¹.
            This is a lower bound on collisions; the production argument still needs
            an upper bound controlling cancellation.</p>
        </details>
        <p className="sources"><a href={`${researchRoot}/Frontier/REnergyCyclicFloorAllDepth.lean`}>All-depth theorem and comparison</a></p>

        <h3>Interpolation certificates beyond Johnson <span className="evidence">Exact computation + Lean core</span></h3>
        <p>The new approach uses derivatives inside an auxiliary polynomial to
          constrain possible messages. Our contribution formalizes and quantifies
          this part of the <a href="https://eccc.weizmann.ac.il/report/2026/164/">Brakensiek–Chen–Putterman–Zhang–Zheng approach</a>.
          The repository contains Lean proofs of the
          interpolation core at every derivative order, plus exact integer
          certificates for selected parameters. At rate 1/2, the best registered
          certificate reaches about {(Number(research.records[0].radius) * 100).toFixed(2)}% errors,
          compared with the 29.29% Johnson benchmark.</p>
        <div className="table-scroll" tabIndex={0} role="region" aria-label="Interpolation certificate comparison">
          <table>
            <caption>Best registered certificates at code length 262,144. Radii are fractions of errors, rounded to five decimals.</caption>
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

        <p className="sources"><a href={`${researchRoot}/DOSSIER.md`}>Research dossier</a>
          <a href={`${researchRoot}/DISPROOF_LOG.md`}>Counterexamples and corrections</a></p>
      </section>

      <section id="open" aria-labelledby="open-title">
        <h2 id="open-title">What remains open</h2>
        <h3>Have we beaten di Benedetto? <span className="evidence conditional">Conditional comparison</span></h3>
        <p>Not unconditionally. Di Benedetto and coauthors proved a character-sum
          estimate with leading exponent 2849/2880 ≈ 0.98924. Our proposed
          recalibration targets 23/24 ≈ 0.95833. Smaller is better, but this still
          assumes stronger energy bounds and a specialized analytic estimate
          that we have not proved for the prize fields.</p>
        <details><summary>Compare the same quantities</summary>
          <p>Here H is the subgroup size and p the prime field size.
            Their Theorem 3.1, for p^(1/4) &lt; H &lt; p^(1/2), gives a bound with powers
            H^(2689/2880) p^(1/72). The proposed energy substitution targets
            H^(65/72) p^(1/72). Near the p ≈ H⁴ boundary these correspond to the
            two leading exponents above. Constants and subpower losses are suppressed;
            these are not finite numerical guarantees.</p>
          <p>The current Lean consumer assumes the specialized analytic estimate,
            and the finite-field energy transfer remains open. The arithmetic
            comparison is formalized; a stronger unconditional character-sum
            theorem is not. Interpolation radii measure something different and
            do not establish a win over this result.</p>
        </details>
        <p className="sources"><a href="https://arxiv.org/html/2003.06165v1#S3">Di Benedetto et al., Theorem 3.1</a>
          <a href={`${researchRoot}/Frontier/_AvCR_DiBenedettoWired.lean`}>Our conditional comparison</a></p>
        <h3>The production proof</h3>
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
