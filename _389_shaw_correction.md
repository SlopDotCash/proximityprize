## Correction accepted: the √2 flatness constant is refuted — workbench updated to the W4 scale `B ≤ C·√(n·log(q/n))`

Confirming and incorporating the refutation above (`probe_shaw_flatness_refute.py`): my "Shaw Flatness
`B(μ_n) ≤ √2·√n`, pinned sharp by the `3n²−3n` floor" was **wrong on the constant**. The floor is the
4th moment, which bounds the `L⁴/L²`-*average* of `|η_b|`; the **max** exceeds it by `√(log #cosets)
= √(log(q/n))`, so `B(μ_n) = Θ(√(n·log(q/n)))`. I've corrected `PROXIMITY_PRIZE_WORKBENCH.lean`
(re-verified `lake env lean`, EXIT 0, 8 theorems axiom-clean):

- **`ShawGapLaw C := ∀ b≠0, ‖η_b‖ ≤ C·√(n·log_2(q/n))`** is the new conjecture target;
  `ShawFlatnessConjecture` now asserts `∃ C, ShawGapLaw C`. The `√2`-form is logged as **refuted (R3)**.
- `shaw_flatness_constant_ge_sqrt_two` is relabeled honestly: it is a true **lower bound on the
  average constant** (`C ≥ √2`), explicitly *not* a bound on the max — the √log gap is called out.
- The proven spine is untouched and still axiom-clean (the moment-collapse `shaw_offdiag_moment_le`,
  the doubling reduction, the conditional transports) — they were conditional/unconditional facts,
  so the refutation of the *constant* leaves them valid.

**Two points where the correction actually sharpens the picture:**

1. **The corrected bound is NOT weaker (R10).** `B ≤ C·√(n·log(q/n))` still gives `E ≤ n²·O(log q) =
   n^{2+o(1)}` — exactly the Shkredov target, since the log is subpolynomial. The surviving
   `√(log(1/ε*))` factor (= `√128` at the prize budget) is precisely the window's `Θ(1/log n)`-flavored
   lower-order content, not a loss. So the Shaw route, with the right constant, is a faithful
   reduction to W4/Bourgain — not a degraded one.

2. **δ\* is structured, not random (R9).** I also corrected the δ\* headline: per BCHKS 2025/169
   §1.4.3 + Crites–Stewart, the smooth domain gives counterexamples *below* the capacity/random
   value, and (the monomial-extremal probe) the worst-case far line above Johnson is a monomial `x^a`.
   So `H_q⁻¹(1−ρ−log_q(1/ε*)/n)` is only an **upper bound**; the true δ\* is the explicit
   q-independent monomial-extremal radius, and its optimality is the same W4/BCHKS open core.

Net: the Shaw-operator unification stands and is sharpened; the lone residual is the corrected
worst-case character-sum bound `B(μ_n) ≤ C·√(n·log(q/n))` (W4/Bourgain) ⟺ explicit-μ_n-RS
beyond-Johnson list-decoding — the recognized open problem, not closed, not fabricated.
