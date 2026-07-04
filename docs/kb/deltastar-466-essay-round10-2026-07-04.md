# #466 Round 10 — Essay: two new machineries on the wall, and a literature freshness sweep

**Date:** 2026-07-04. **Round:** 10 (Opus, three lanes, each adversarially verified).
**Bottom line:** the wall stands. Both new machineries (automatic-sequence Fourier analysis;
transfer-operator / dynamical-zeta spectral gap) are refuted with an axiom-clean no-go record; the
2024–2026 literature does not touch the object. After ten rounds the surviving open surface is still
**exactly one object** — the analytic BGK/Paley wall — and it is carried as a named open `Prop`. No
fabricated closure.

---

## 1. The wall as it now stands (for a working analyst)

Fix `μ = 30`, `n = 2^μ = 2^{30}`, a prime `p ≡ 1 (mod n)` with `p ≈ n^4` (so `β ≈ 4`), and let
`ζ ∈ F_p^×` be a primitive `n`-th root of unity. The subgroup `μ_n = ⟨ζ⟩` is a **proper, thin**
multiplicative subgroup: `μ_n ⊊ F_p^×` of index `m = (p−1)/n ≈ 2^{128}`. Index `μ_n` by
`k ∈ ℤ/2^μ` via `x = ζ^k`.

**The wraparound count.** For depth `r`, let

> `W_r := E_r^{(p)} − E_∞`

where `E_r^{(p)}` is the number of solutions `(k_1,…,k_{2r}) ∈ (ℤ/n)^{2r}` of the char-`p` relation

> `ζ^{k_1} + ⋯ + ζ^{k_r} ≡ ζ^{k_{r+1}} + ⋯ + ζ^{k_{2r}}  (mod p)`,

and `E_∞` is the char-0 (over-ℤ, i.e. cyclotomic) solution count of the *same* balanced relation.
`W_r ≥ 0` is a **nonnegative count** — the extra collisions that appear only because we reduce mod
`p` (signed cancellation is refuted, `_WallBetaPlusOneLocalization.lean`: there is nothing to
cancel; the wall is the *unsigned* inequality).

**The wall (open core).** At `r = β + 1`,

> **(WALL)   `W_r ≤ n^{2r}/p`.**

Equivalently, in DC-subtracted energy form, `A_r := E_r^{(p)} − n^{2r}/p ≤ K^r (2r−1)‼ · n^r` for a
constant `K = O(1)`, uniformly to depth `r ≈ ln p ≈ 89` (dossier §2.3–2.4, forms A–D). The raw
`E_r ≤ (2r−1)‼·n^r` is **false** past the DC crossover; only the DC-subtracted statement is
non-vacuous. Equivalently again, the worst-frequency sup bound
`M(μ_n) = max_{b≠0} ‖η_b‖ ≲ √(n·log m)`, where `η_b = Σ_{x∈μ_n} e_p(bx)` is the `b`-th Gauss period
(the nontrivial spectrum of the generalized Paley graph `Cay(F_p, μ_n)`). `n^{2r}/p` is the
**digit-uniform DC mean** of the count; the wall says the true count does not exceed that mean by
more than the Wick fluctuation.

This is the ≈25-year-open thin-2-power square-root-cancellation problem. Best *proven* bound at
`β = 4` is BGK `n^{1−o(1)}` (the `o(1)` ineffective); the target `√n` is the Paley Graph
Conjecture, open everywhere. Every second-order method provably caps at Johnson/√p
(`MetaTheoremSecondOrderCap`); a winning method must be simultaneously **b-sensitive**,
**deterministic-archimedean**, and **genuinely L∞** (dossier §4.1, the Meta-Theorem). Round 10
tested two candidate machineries that each *promised* to be b-sensitive.

---

## 2. Machinery I — automatic-sequence / substitutive Fourier analysis (Lane A)

**What was genuinely new.** The exponent index `k ∈ ℤ/2^μ` is a 2-adic object, and the map
`k ↦ ζ^k` satisfies the squaring recursion `a(2k) = a(k)^2`. Lane A asked: is the phase sequence
`k ↦ e_p(b·ζ^k)` **2-automatic**, so that an Allouche–Shallit / Byszewski–Konieczny–Müllner (BKM)
Gowers-norm uniformity bound applies? If the wraparound solution set had exploitable 2-adic digit
structure and a per-frequency uniformity bound could see it, that bound would be **b-sensitive** —
the exact property the Meta-Theorem demands — and could push `W_r` below its digit-uniform DC mean.
This is a genuinely new attack surface: no prior round applied automatic-sequence machinery, and the
probe found **real structure to exploit** — the pairwise-exponent valuation statistic `v_2(k_i−k_j)`
on the solution set deviates from the digit-uniform null with `χ²/dof` in the hundreds-to-thousands,
and the set is **not** closed under the odd-unit dilation `k ↦ u·k` (a previously-unrecorded fact).
So the angle is not a strawman: the digit structure is real and robust.

**Exact death — three independent mechanisms, one formalized.** The structure is real but
unreachable, for three reasons (probe `probe_466r10_automatic.py`, ≥2 primes of distinct `v_2(p−1)`,
two octaves `n = 8,16`, validated tuple-for-tuple against the level engine):

1. **Count-neutral.** `W_r` already sits *at or below* its digit-uniform DC mean:
   `W_r / DC ∈ [0.13, 0.68]`, all `≤ 1`. A uniformity bound can only push the total toward a null it
   already matches — there is no total left to save.
2. **Sign-unstable.** The deviation *direction* flips with `p` (independently reproduced: `−0.6%` at
   `p=17` vs `+3.5…4.9%` at `p=41,73,89,97`). No fixed Gowers direction survives across primes, so
   there is no single biased character to bound.
3. **b-blind (the load-bearing one, formalized).** The wraparound solution set is *exactly* the
   equal-sum (collision) locus `{(x,y) : S x = S y}`, and on that locus the per-frequency character
   weight is `χ_b(S x − S y) = χ_b(0) = 1` for **every** `b`. So the indicator of the solution set —
   and hence *any statistic of it*, including its 2-adic digit structure — carries no `b`-dependence
   whatsoever. The set count is a function of the `b`-**summed** moment `Σ_b η_b·conj(η_b)`, never of
   a single `η_b`. Any automatic-sequence uniformity bound therefore bounds only the b-summed
   `2r`-th moment `W_r`, and the Meta-Theorem's second-order cap applies verbatim.

The novel structural observation refines this: the 2-adic structure is **joint, not marginal** — the
S2 popcount marginal is *exactly* uniform (0.000% deviation, χ²=0) while the joint pairwise-valuation
field is strongly structured, with dilation-closure = 1/4. The exploitable content lives in a joint
distribution that the b-summed count integrates away.

**The tool does not even apply per-frequency.** One might hope to apply BKM to a *single* frequency
`η_b` (which would be b-sensitive), sidestepping the b-summed collapse. Task 1 kills this too:
`k ↦ ζ^k mod p` obeys `a(2k)=a(k)^2`, but its 2-kernel base root `ζ^{2^i}` has order `n/2^i`
(**shrinking** to 1) while the output alphabet size `2^μ` **grows** — so there is **no `μ`-uniform
finite automaton**. The automatic-sequence asymptotics require a fixed automaton across scales; this
sequence has none. The tool is inapplicable even before the b-blindness bites.

**Formal record (axiom-clean, `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`):**
`_LaneAAutomaticBBlind.lean` proves (i) `char_weight_trivial_on_solset`: `χ_b(S x − S y) = 1` on the
collision locus, for every `b`; and (ii) `solset_count_is_b_summed`: the solution count equals the
b-summed moment `Σ_b η_b·conj(η_b)` (the #444 master identity `collision_count_eq_moment` reused
verbatim). These are honest but *deliberately weak*: (i) is `χ_b(0)=1` and (ii) is a restatement of
the #444 identity. Their purpose is a **no-go placement**, not a bound — they pin Lane A inside the
dead Meta-Theorem cone. This is the correct, expected outcome: **Lane A is refuted, the wall is left
OPEN.**

---

## 3. Machinery II — transfer-operator / dynamical-zeta spectral gap (Lane B)

**What was genuinely new.** There is an *exact linear tower recursion*
`η_b(μ_{2N}) = η_b(μ_N) + η_{ζb}(μ_N)` (the doubling map `x ↦ x²` on the tower;
`_AvW16_CosetTowerRecursion.lean`, axiom-clean), and the triangle bound gives the lossy factor 2,
with the `√2` saving localized to the *joint two-frequency distribution* of `(η_b, η_{ζb})`. Lane B
asked whether a **transfer operator / dynamical zeta** on this recursion has a **spectral gap**
controlling `W_r` asymptotically — and, critically, whether that operator's spectrum sees anything
the raw moments `E_r = (1/p)Σ_b ‖η_b‖^{2r}` do not. A genuine spectral gap independent of the moment
ladder would be a new invariant, potentially b-sensitive. This too is a real new surface: no prior
round built a transfer operator on the tower step.

**Exact death — gauge on one side, a regime-degenerate transient on the other.**

1. **GAUGE (the invariant side).** Any functional the transfer operator produces is built from the
   eta-vector `{η_b}`; by the coset symmetry its magnitude data is the **multiset** `{‖η_b‖}`, whose
   only invariants are the power sums = the moment ladder `(E_1, E_2, …)`. The operator's spectral
   invariants (leading eigenvalue, gap, traces of powers) factor through this multiset, so they
   *cannot* distinguish two primes with the same magnitude multiset — they are a reparameterization
   of the raw energies. This is the Toda/isospectral gauge shape
   (`todaTurnover_not_determined_by_invariants`). It is, at bottom, *tautological*:
   `E_r = (1/p)Σ_b ‖η_b‖^{2r}` is by definition a symmetric function of the `‖η_b‖` multiset, so
   "operator symmetric-invariants ⊆ moments" is forced. The Lean brick records exactly this.

2. **TRANSIENT (the dynamical side).** The per-level sup ratio `M(μ_{2n})/M(μ_n)` descends toward
   `√2` (2.00 → 2.00 → 1.96 → 1.75 → 1.43 → 1.40 at a deep prime `p=268437889`), with `M/√n`
   plateauing (~4.8–4.9). One might read this as a bounded transient converging to the mean-field
   rate, i.e. "wall true, spectral gap → 0, method mute." **But this reading is regime-degenerate,
   not informative.** `ratio → √2` is mathematically *equivalent* to `M/√n → const` (because
   `M = c√n ⟹ M(2n)/M(n) = √2` identically). In a **single-prime tower** `log m` is held fixed, so
   `M ~ √(n·log m)` *forces* `M/√n → const → ratio → √2` automatically — for **both** the prize-true
   and the BGK-tight hypotheses. The experiment therefore *cannot distinguish* them; it is exactly
   dossier §10's "data consistent with both." (The top-level ratio even dips *below* √2 — finite-size
   saturation noise — so it is not the clean monotone-from-above descent the first reading suggested.)
   The honest bottom line survives: **no super-rate ⇒ the floor is NOT refuted, but the method is
   mute; it observes the wall, it does not bound it.**

**The one crack probed and closed.** The tower step consumes the *joint* `(η_b, η_{ζb})`
distribution, so a marginal-multiset argument could in principle miss phase information. The
adversarial probe tested the joint cross-coset second moment `C = ⟨‖η_b‖²‖η_{ζb}‖²⟩` across 8 primes
at `n=32`: `C/(mean‖η‖²)² = 0.999083…0.999084`, pinned to 1 and essentially constant across primes —
adjacent cosets are uncorrelated and, at `r=2`, the joint *is* fixed by the marginals, supporting
gauge. This does not rule out phase structure at the prize depth `r ≈ 89`, but no surviving crack is
exposed here.

**Formal record (axiom-clean).** `_B_TransferOperatorGauge.lean` proves `momentPow_eq_ofMultiset`
(the moment is a genuine multiset invariant), `powerSum_eq_of_multiset_eq` (equal magnitude
multisets ⇒ equal moments at every order), `transfer_functional_perm_invariant` (any multiset
functional is relabeling-invariant), and the packaged `transfer_gauge` (same `‖η‖`-multiset ⇒ every
transfer-operator invariant AND every moment agrees; operator ⊆ moments). As with Lane A, these are
honest but *weak by design*: they prove the gauge *containment* by restricting to functionals of the
magnitude multiset — a no-go record, not a wall bound. **Lane B is refuted; the wall is left OPEN.**

---

## 4. Literature freshness — does 2024–2026 touch the wall? (Lane C)

**No.** A fresh 2024–2026 sweep (Lane C, verified independently against the arXiv abstracts) finds
**zero survivors** against the foreclosure ledger. Every genuinely-new square-root-cancellation
result of the period lives on a structure the prize object provably lacks:

- **Kunisky** (2303.16475, Exp. Math. 2024) — the *closest hit*, on the eigenvalue side — is
  **index-2** (the full Paley graph / induced subgraphs on independent-set extensions), and its
  min-eigenvalue → Kesten–McKay-edge claim is a **conjecture** (numerics only); only the `a=1`
  character-sum estimate is proven. No transfer to thin `μ_n` at index `2^{128}`.
- **Ma** (2606.26440) — square-root cancellation over the **function field** `F_q[t]` — is exactly
  the D0/EVW "function-field side untouched" note; the `F_p` transfer is airtight-killed (Jacobi
  self-braiding non-torsion).
- **Chattopadhyay** (2505.19654) and **Mangerel–You** (2405.00544) — Burgess-type **interval/box**
  cancellation; multiplicative subgroups are excluded verbatim by the interval hypothesis.
- **Yip** (clique numbers), **Kalmynin** (2504.10202), **Kim–Yip–Yoo** (2602.20919), **Hegyvári**
  (2602.01781) — pure additive/multiplicative-structure or clique results: **no magnitude bound**,
  b-blind, off the wall.
- **di Benedetto et al.** (2003.06165) remains SOTA for the sum-product route with **no 2024–2026
  exponent successor**; its saving `→ 0` at the boundary `n = p^{1/4}`.

The three structural walls the whole crop hits: the `p^{1/3}` energy floor (HBK/Shkredov/Stepanov);
Bourgain–Gamburd is non-abelian-only (a cyclic `μ_n` is abelian); and interval-vs-subgroup /
function-field-vs-prime-field mismatch. **No 2024–2026 paper crosses `n^{0.989…} → n^{1/2}` at β=4
for thin 2-power subgroups.** The missing analytic input does not exist in the literature — consistent
with the prior 67-/29-/26-/35-paper sweeps.

---

## 5. Honest state after Round 10

**The surface is still exactly one object.** Both new machineries died; each died *cleanly* and for a
reason now formally recorded:

- **Automatic-sequence (Lane A):** the wraparound set is the equal-sum locus, on which the character
  weight is `χ_b(0)=1` for all `b` — so its (real, robust) 2-adic structure is **b-blind**
  (count-neutral, sign-unstable), and the exponent sequence has **no μ-uniform automaton**, so the
  tool is inapplicable even per-frequency.
- **Transfer-operator (Lane B):** the operator's invariants factor through the `‖η_b‖`-multiset,
  which are exactly the moments — **gauge**; and its transient `→ √2` rate is **regime-degenerate**
  (forced by `M ~ √(n log m)` at fixed `log m`), so it observes the wall without bounding it.
- **Literature (Lane C):** untouched by 2024–2026.

This confirms the Round-9 final state: the prize is a single, precisely-stated open inequality
`W_r ≤ n^{2r}/p` at `r = β+1`, with a completely mapped no-go landscape. Both Round-10 candidates
were the strongest remaining "b-sensitive-looking" surfaces, and both collapse to the same b-summed /
gauge cause. **CORE OPEN, ON-BGK.**

**Is there a new named sub-thread worth a Round 11?** Only one honest candidate emerges, and it is a
*sub-question of the wall*, not an escape from it:

> **`JointPhaseFieldStructure` (open).** Round 10 established that the exploitable 2-adic content is
> **joint, not marginal** (Lane A: S2 popcount marginal exactly uniform, joint pairwise-valuation
> field strongly structured, dilation-closure 1/4) and that the tower step consumes the *joint*
> `(η_b, η_{ζb})` distribution, which is gauge-fixed by the marginals *only up to `r=2`*
> (Lane B: `C/(mean)² ≈ 0.9991` at `n=32`, `r=2`). **Open:** does the joint two-frequency phase
> field carry b-sensitive information at prize depth `r ≈ 89` that is invisible to every marginal
> (multiset / moment) functional? A method that reads the joint field — not the marginal magnitudes —
> is the *only* structural direction Round 10 did not foreclose.

This is genuinely open, but it must be stated honestly: it is a **candidate escape from the
Meta-Theorem's second-order cap**, not a proof strategy. Both Round-10 lanes probed adjacent-coset
joints and found them marginal-determined at `r=2`; the sub-thread is worth a round *only* if a
statistic of the joint field at deep `r` can be exhibited that is (a) not a function of the moment
ladder and (b) b-sensitive. If Round 11 finds the joint field also collapses to the marginals at
depth, that is another clean refutation — which is the expected outcome for this wall, and a win.

---

## 6. Honesty contract

No closure is claimed. The wall `W_r ≤ n^{2r}/p` at `r = β+1` remains a **named open `Prop`**,
carried as the single open surface of #466. The two Lean bricks landed this round
(`_LaneAAutomaticBBlind.lean`, `_B_TransferOperatorGauge.lean`) are **no-go records**: axiom-clean
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`, verified by
`pg-iterate.sh`), but each proves a *placement/gauge* fact, not a wall bound — and both files say so
in their own docstrings. The probe verdicts are labeled probe verdicts; the literature verdict is a
sweep, not a theorem. A refutation of the round's own two proposed angles is the expected, valuable
product, reported here with the exact collapse mechanism. The core is **OPEN, ON-BGK.**

<sub>🤖 Round 10 essay, #466, 2026-07-04. Synthesized from the three adversarially-verified lanes
(A: automatic-sequence; B: transfer-operator; C: literature). No fabricated closure.</sub>
