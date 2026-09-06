import { Section } from "../Section";
import { Intuition } from "../Intuition";

export function Method() {
  return (
    <Section id="method" num="2" title="Methodology and labelling discipline">
      <Intuition>Because the claims here touch a long-open problem, we let a proof checker, not the authors, certify what is true. Each statement is one of three kinds, always labelled: proven (a Lean kernel theorem, with its axioms listed), computational (an exact finite calculation anyone can rerun), or open (a conjecture we do not resolve). Nothing in between.</Intuition>
      <p>
        We are deliberate about the epistemic status of every statement, using
        three disjoint labels throughout. The value of a formal-verification
        effort is precisely that the boundary between them is sharp and
        third-partyly checkable.
      </p>

      <div className="mt-6 space-y-4">
        <div className="flex gap-4">
          <span
            className="mono text-[0.8rem] font-semibold shrink-0 mt-1"
            style={{ color: "var(--accent)" }}
          >
            (P)
          </span>
          <p className="m-0">
            <strong>Proven.</strong> A Lean&nbsp;4 theorem on the{" "}
            <code className="inline">main</code> branch of{" "}
            <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>,{" "}
            <code className="inline">sorry</code>-free, whose printed axiom
            census we have inspected and which lies inside the standard budget{" "}
            <code className="inline">
              propext, Classical.choice, Quot.sound
            </code>
            . The correctness of every (P) statement rests on the soundness of
            the Lean&nbsp;4 kernel and these three axioms, not on a human&rsquo;s
            reading of a proof.
          </p>
        </div>
        <div className="flex gap-4">
          <span
            className="mono text-[0.8rem] font-semibold shrink-0 mt-1"
            style={{ color: "var(--accent)" }}
          >
            (C)
          </span>
          <p className="m-0">
            <strong>Computational.</strong> A statement established by exact
            enumeration or exact FFT over a stated finite range of parameters
            (never by floating-point sampling). Reproducible, but not on its own
            a theorem for all <code className="inline">n</code>. We never promote
            a (C) statement to (P) without a Lean proof.
          </p>
        </div>
        <div className="flex gap-4">
          <span
            className="mono text-[0.8rem] font-semibold shrink-0 mt-1"
            style={{ color: "var(--accent)" }}
          >
            (O)
          </span>
          <p className="m-0">
            <strong>Open / conjectural.</strong> A statement we believe but have
            not proven, or a precisely posed open problem. We never present these
            as proven.
          </p>
        </div>
      </div>

      <h3 className="text-[1.13rem] font-semibold mt-10 mb-4">
        Refutation as a deliverable
      </h3>
      <p>
        A countermodel that kills a candidate route is recorded in{" "}
        <code className="inline">Research/ProximityPrize/DISPROOF_LOG.md</code> and, where it sharpens a
        constraint, formalized as a refutation theorem (the impossibility
        results of Section&nbsp;6). This discipline is what kept the effort from
        drifting into wishful closure. We record one instance in
        Section&nbsp;6: an in-tree energy bound used at one point as if valid at
        prize moment depth was shown by an exact probe to be false, the claim
        retracted, and the corrected bound installed. We present such
        self-corrections in the open, because the kernel honesty contract exists
        to catch exactly this kind of error.
      </p>
    </Section>
  );
}
