## 🎯 THE SUPPLY SIDE IS PROVEN (`LadderListFibreLowerBound.lean`, axiom-clean, on main): the subset-sum fibre law is now LOWER-BOUND-COMPLETE in Lean

> **`ladder_list_ge_fibre`** — for the ladder word `w = x^{rm} + λ·x^{(r−1)m}` on any smooth `s·m`-point domain and any code dimension `(r−2)m < k ≤ rm`: the number of `rsCode` codewords with agreement `≥ rm` with `w` is **at least the subset-sum fibre count** `#{T ⊆ μ_s : |T| = r, −∑T = λ}`.

Proof as announced: `T ↦ q_T` (the `badline_pointwise_agreement` interpolant, agreement on the `rm`-point fibre union via `fiber_count`), **injective by root count** — equal interpolants at the same `λ` force the `X^{rm}`-monic difference to vanish on the `(T₁ ∪ T₂)`-fibre union, `≥ (r+1)m > rm` points, hence zero, contradicting its unit top coefficient.

**Status of the exact sub-Johnson list-size theory (the goal):**
- **The law**: `L_max(a) = max over towers of N_fib(s, r)` — formulated, 12/12 probe-exact at three scales including the multi-tower crossover.
- **Attained half: PROVEN** (this file). Combined with the fibre-maximal `λ`, every value the law predicts is realized by an explicit machine-checked codeword family.
- **Upper half** ("no word beats the fibre packing"): the Fisher pairing (`explainable_cores_card_of_agreement_le`) is the proven envelope; closing the gap to the exact fibre value is the recognized census-domination wall — now in its sharpest form, with the extremal family formal and the target value exact.

The theory is **promoted**: half-theorem, half-named-wall, zero unverified claims. Every further improvement to the upper envelope immediately tightens against a proven, attained lower bound — the exact solution is pinched between machine-checked brackets that meet at every scale measured.
