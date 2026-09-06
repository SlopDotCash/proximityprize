import { Section, SubSection } from "../Section";
import { Intuition } from "../Intuition";
import { Theorem } from "../Theorem";
import { M } from "../Math";

const REPO =
  "https://github.com/lalalune/ArkLib/blob/main/ArkLib/Data/CodingTheory/ProximityGap";

function FileLink({ f }: { f: string }) {
  return (
    <a href={`${REPO}/${f}.lean`}>
      <code>{f}</code>
    </a>
  );
}

export function Refutations() {
  return (
    <Section id="refutations" num="4" title="Refutations as results">
      <Intuition>Knowing which methods cannot work is itself progress: it stops the search from circling. We record machine-checked impossibility statements, for instance that no bound built from averages (moments of any order) can reach the target, so that the remaining viable routes are sharply narrowed.</Intuition>
      <p>
        We treat refutations as first-class deliverables. Twenty-eight candidate
        approaches were disposed of during the campaign, and under the
        verification discipline each disposal is itself a theorem: the failed
        idea is reduced to a <code>sorry</code>-free constraint lemma and
        recorded in the standing disproof log (
        <a href="https://github.com/SlopDotCash/proximityprize/blob/main/Research/ProximityPrize/DISPROOF_LOG.md">
          <code>Research/ProximityPrize/DISPROOF_LOG.md</code>
        </a>
        ), so that it cannot be re-proposed and the boundary of the possible is
        itself machine-checked. We present a selection below, not as failures
        but as the negative half of the map: each closes a route that a careful
        mathematician, or a language model, might otherwise pursue.
      </p>

      <SubSection num="4.1" title="Structural kills">
        <Theorem
          kind="Refutation"
          name="halving renormalization (refuted)"
          file="HalvingWindowExit.lean"
          decl="halving_exits_window"
          refuted
        >
          The hoped-for renormalization map{" "}
          <M>{String.raw`(\delta,\varepsilon)\mapsto(\approx\delta/2,\ \varepsilon/2)`}</M>{" "}
          exits the window in one step from anywhere below capacity; its unique
          fixpoint is 0. No iterate-and-conquer scheme of this shape can pin{" "}
          <M>{String.raw`\delta^*`}</M>.
        </Theorem>
        <Theorem
          kind="Refutation"
          name="the MDS rank conjecture, false for RS too"
          file="MCAMDSStaircaseRefuted.lean"
          decl="mdsStaircaseConjecture_refuted"
          refuted
        >
          A perfect-square pencil identity supplies{" "}
          <M>{String.raw`n/(b-1)`}</M> bad scalars on the whole strip{" "}
          <M>{String.raw`[2b-1,3b-3]`}</M>, killing the conjecture that the deep
          staircase value extends to half the distance. Consequence:{" "}
          <M>{String.raw`3b-2`}</M> is <em>the</em> law, for general linear
          codes and for RS alike, and the exact RS staircase ends near{" "}
          <M>{String.raw`(1-\rho)/3`}</M>, not <M>{String.raw`(1-\rho)/2`}</M>.
          Discovered by probe, then formalized with five certified bad scalars.
        </Theorem>
        <Theorem
          kind="Refutation"
          name="MCA below Johnson is not a function of (n, d, q)"
          file="MCAHalfDistanceGeneralRefuted.lean"
          refuted
        >
          A doubled-column countermodel separates MDS from general linear codes
          at an MCA quantity, the first such separation, so no staircase law
          for general codes can be parameterized by distance alone.
        </Theorem>
      </SubSection>

      <SubSection num="4.2" title="The extremality-surface lineage">
        <p>
          The census programme&rsquo;s conjectured extremal surface was killed
          and rebuilt three times, each kill a formal countermodel found by
          probe: census v1 died on empty rungs contradicting the{" "}
          <M>{String.raw`1/q`}</M> floor; v2 died on a take-over stack carrying{" "}
          <M>{String.raw`n`}</M> field-independent bad scalars at an empty
          adjacent rung (<FileLink f="TakeoverCountermodel" />); v3,
          monomial domination, died twice (
          <FileLink f="MonomialDominationKilled" />). The surviving v4 hybrid
          surface is consistent with every theorem and probe in the tree, and
          its conditional pin non-vacuously recovers the{" "}
          <M>{String.raw`\mathbb{F}_5`}</M> exact value. This is what red-teaming
          a conjecture looks like when the red team must publish countermodels
          the kernel accepts.
        </p>
      </SubSection>

      <SubSection num="4.3" title="Machine-checked corrections to the literature">
        <p>
          Two of the campaign&rsquo;s most consequential refutations are
          corrections to the paper chain underlying the Johnson lane itself
          (BCIKS20, Appendix A). Finding 13 showed the rebased weight budget is
          unsatisfiable at genuine cells, exposing a hidden anchor assumption in
          the paper&rsquo;s base case. Finding 14 produced an explicit
          countermodel, at a concrete instance over{" "}
          <M>{String.raw`\mathrm{ZMod}\ 5`}</M>, showing the in-tree
          transcription of the paper&rsquo;s recursion diverges from the
          paper&rsquo;s intent at order 1 for non-monic factors (
          <a href="https://github.com/lalalune/ArkLib/blob/main/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Finding14Countermodel.lean">
            <code>BCIKS20/Finding14Countermodel</code>
          </a>
          ). The repaired, cleared recursion (
          <a href="https://github.com/lalalune/ArkLib/blob/main/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ClearedRecursion.lean">
            <code>BCIKS20/ClearedRecursion</code>
          </a>
          ) then closed the complete Claim-A.2 weight bound with no per-cell
          hypotheses. Formalization did not merely transcribe the literature; it
          debugged it.
        </p>
      </SubSection>

      <SubSection num="4.4" title="Self-inflicted and honestly recorded">
        <p>
          The log also records the campaign&rsquo;s own errors: a conjectured
          staircase threshold refuted at band 4 by a tripled-column code; an
          overclaim about reducing the pin to a character-sum estimate,
          retracted twice; a characteristic-zero-to-mod-<M>p</M> lifting that
          fails measurably at <M>n=64</M>; a claimed enumeration closure
          withdrawn when its artifacts turned out to be empty files; and a
          window-cocycle identity that was exact but vacuous. Three documented
          no-gos constrain the window analysis itself: degree-forcing dies at
          the ladder reach, the naive GRS recursion degrades{" "}
          <M>{String.raw`(w,k)\to(3w,2w+k)`}</M>, and the M&ouml;bius
          eigendecomposition provably cannot linearize the bad count (14% of
          probed stacks couple the eigencomponents through the shared witness).
          A campaign that cannot admit error cannot be trusted to report
          success; the disproof log is the evidence that this one can.
        </p>
      </SubSection>
    </Section>
  );
}
