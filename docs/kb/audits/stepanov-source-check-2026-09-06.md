# Stepanov extraction: partial primary-source check

The [Cochrane–Pinner manuscript](https://www.math.ksu.edu/~cochrane/research/binsum7.pdf), pages 4–5, was checked against `_research_357/hbk-stepanov-extraction.md` on 2026-09-06. Lemma 2.3 has the displayed positive-parameter, dimension, ab<=t and tb<p hypotheses. Lemma 2.4 uses b=floor((4ts)^(1/3))+1 and bounds the sum of the s largest nonzero-coset counts by b². Its preceding definitions separate the zero contribution. The extraction's s=1 specialization therefore requires a nonzero shift, now stated explicitly.

The exact p=769, t=64, b=7 zero-shift counterexample was independently checked by trial division and enumeration of all 64 roots modulo p. It verifies the need for that hypothesis, not the positive-shift theorem.

This checks the CP parameter target only. The extraction's HBK, Konyagin, Mattarei, derivative, and deployment assertions still need individual review. The artifact remains outside the completed retention count (56/92). No Lean proof was compiled for this check.
