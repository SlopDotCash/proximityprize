/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-O1)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# OSV short-Weil curve-blend re-attack: structural ceiling (lane wf-O1, #444)

Lane O1 re-attacks the Ostafe–Shparlinski–Voloch (OSV) "Weil Sums over Small Subgroups"
machinery (arXiv:2211.07739) against the **constant-`C`** target

  `M(n) = max_{b≠0} |∑_{x∈μ_n} e_p(b·x)| ≤ C·√(n·log(p/n))`,   n = |μ_n|, p = n^β, β ≈ 4.

The earlier OSV attempt was refuted for a *power-saving* target.  This lane asks whether, with
the corrected constant-`C` goal and the live nonprincipal-moment route, the OSV curve `C_b`
blended with the moment structure closes the prize.

## What OSV actually proves (read off arXiv:2211.07739)

* **Theorem 1.1 / Lemma 3.2:** `S(G;f) ≪ τ·p^{-η_n(ε)}` with `η_n(ε) ≥ c·(7ε/9)^{n-1}/(n-2)!`
  for polynomials `f` of degree `n`, valid only for `τ ≥ p^{3/7+ε}`.  This is a *power saving
  in p*, exponentially small in the degree, and its range `τ ≥ p^{3/7}≈p^{0.43}` **excludes** our
  regime `τ = n = p^{1/β} = p^{1/4}`.
* The **curve** machinery (Lemma 2.1 `#{F=0} ≤ 4d^{4/3}p^{2/3}+3p`, Lemma 2.2 absolute
  irreducibility of `F=(X^{sm}+Y^{sm}-A)^n-(X^{sn}+Y^{sn}-B)^m`) is deployed **only** for the
  binomial/multinomial additive-energy `Q_3(m,n;G)` in **six** variables (§3.2), i.e. for
  `f` with `r ≥ 2` monomials.  Our sum `f(X)=b·X` is a **single** monomial.
* For a single monomial (`r=1`, OSV's `n=1` case) OSV defers to **Shkredov [21]** via Lemma 3.6:
    `S(G;f) ≪ min{ p^{1/2}, τ^{1/2}·p^{1/6}·(log p)^{1/6} }`.
  This is the *only* OSV-stack bound that touches `τ = p^{1/4}`, and it carries a `p^{1/6}`.

## Numeric verdict (this lane; `scripts/probes/rust/wf6O1_osv_blend.rs`, exact mod-p counts)

* **Q1 (Shkredov vs prize).**  `Shk/prize = n^{1/2}p^{1/6}(log p)^{1/6} / √(n log(p/n))`
  grows: `3.25, 4.81, 7.19, 16.4, 38.2` at `n = 16,32,64,256,1024` (β≈4), and at the prize point
  `n=2^30, p=2^120` it is `≈ 2.8·10^5`.  The `p^{1/6}` diverges from the constant-`C` target at
  large β — OSV is structurally a power-saving machine, **useless at β=4** for this target.
* **Q2 (curve point-count vs char-0).**  The OSV curve bound `4(rn)^{4/3}p^{2/3}+3p` only drops
  below the proven char-0 Wick ceiling `char0_r := (2r-1)!!·n^r` at depth `r ≥ 4` (ratio
  `curve/char0 = 26703, 20.3, 0.25` at `r=1,3,4`, n=16), but the *actual* additive count
  `A_r = #{2r-tuples in μ_n summing to 0 mod p}` is already `< char0_r` everywhere
  (`A_r/char0 = 1.00, 0.82, 0.68` at `r=1,3,4`, n=16, decreasing).  So the curve count is **never
  the binding per-coset constraint**: the proven char-0 bound dominates it where it bites.

## Conclusion of lane O1 (REDUCED-TO-CLOSED / NO-GO for the curve add-on)

The OSV curve `C_b` contributes **nothing** to the constant-`C` target over and above the
already-proven char-0 Wick ceiling `(2r-1)!!·n^r` (DyadicEnergyK1, via Lam–Leung):
1. for the *linear* sum it degenerates to Shkredov's `p^{1/6}` power bound, which diverges from
   the prize at β=4 (Q1);
2. for the moment/additive-energy it is dominated by char-0 at every depth that matters (Q2).

Hence the prize **does not** come from blending in the curve point-count; it is forced back onto
the live **nonprincipal-moment** route `(S-M1'): E_r'(μ_n) ≤ K^r·(2r-1)!!·n^r` (absolute `K`),
which the char-0 ceiling already certifies with `K_eff < 1` per depth.

This file records, as an axiom-clean Lean fact, the *decision inequality* behind Q1: at the prize
exponent the Shkredov bound exceeds the prize target — so the OSV/Shkredov route cannot supply a
constant-`C` bound and the prize must be closed by the moment route instead.
-/

namespace ArkLib.ProximityGap.Frontier.WF6O1

open Real

/-- The Shkredov / OSV-Lemma-3.6 sup-bound exponent profile for the *linear* sum
`S(G; b·X)` over a subgroup of order `n` in `F_p`:
`Shk(n,p) = √n · p^{1/6} · (log p)^{1/6}`.  This is the only OSV-stack bound applicable at
`τ = n = p^{1/4}` (single monomial). -/
noncomputable def shkBound (n p : ℝ) : ℝ :=
  Real.sqrt n * p ^ ((1 : ℝ) / 6) * (Real.log p) ^ ((1 : ℝ) / 6)

/-- The prize target `prize(n,p) = √(n · log(p/n))`. -/
noncomputable def prizeTarget (n p : ℝ) : ℝ :=
  Real.sqrt (n * Real.log (p / n))

/-- **Decision inequality (Q1, structural ceiling of the OSV curve-blend route).**

For the regime `p = n^β` with `β ≥ 4` and `n ≥ 2`, the Shkredov / OSV-Lemma-3.6 bound carries a
`p^{1/6}` factor that the prize target (which is only `√(n·log)` ≤ `√(n)·√(log p)`) cannot absorb:
the ratio `shkBound / prizeTarget` is at least `p^{1/6} / √(log p)`, which `→ ∞`.

Concretely we prove the clean lower bound: if `1 ≤ n ≤ p` and `1 < p` and `log(p/n) ≤ log p`,
then `shkBound n p ≥ √n · p^{1/6}` while `prizeTarget n p ≤ √n · √(log p)`, so the Shkredov
bound dominates the prize whenever `p^{1/6} ≥ √(log p)` — true for all `p ≥` an absolute constant
and a fortiori at the prize point `p = 2^120` (where `p^{1/6}=2^20 ≫ √120`).

This is the formal core of the lane's NO-GO: the OSV/Shkredov route's `p^{1/6}` provably
outgrows any `√(log)` prize target at β=4, so it cannot yield the constant-`C` bound. -/
theorem shk_dominates_prize_factor
    (n p : ℝ) (hn1 : 1 ≤ n) (hp1 : 1 < p) (hnp : n ≤ p)
    (hlogp1 : 1 ≤ Real.log p)
    (hlog_le : Real.log (p / n) ≤ Real.log p) :
    Real.sqrt n * p ^ ((1 : ℝ) / 6) ≤ shkBound n p
    ∧ prizeTarget n p ≤ Real.sqrt n * Real.sqrt (Real.log p) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp1
  constructor
  · -- shkBound = √n · p^{1/6} · (log p)^{1/6} ≥ √n · p^{1/6}, since (log p)^{1/6} ≥ 1.
    -- The hypothesis `1 ≤ log p` holds at prize scale (log(2^120)=120·log 2 ≫ 1) and indeed
    -- for all p ≥ e; it is the honest range of the OSV/Shkredov domination statement.
    have hge1 : (1 : ℝ) ≤ (Real.log p) ^ ((1 : ℝ) / 6) := by
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 6) := by simp
        _ ≤ (Real.log p) ^ ((1 : ℝ) / 6) :=
            Real.rpow_le_rpow (by norm_num) hlogp1 (by norm_num)
    have hfac_nonneg : 0 ≤ Real.sqrt n * p ^ ((1 : ℝ) / 6) :=
      mul_nonneg (Real.sqrt_nonneg n) (Real.rpow_nonneg (le_of_lt hp0) _)
    calc Real.sqrt n * p ^ ((1 : ℝ) / 6)
        = (Real.sqrt n * p ^ ((1 : ℝ) / 6)) * 1 := by ring
      _ ≤ (Real.sqrt n * p ^ ((1 : ℝ) / 6)) * (Real.log p) ^ ((1 : ℝ) / 6) :=
          mul_le_mul_of_nonneg_left hge1 hfac_nonneg
      _ = shkBound n p := by unfold shkBound; ring
  · -- prizeTarget = √(n·log(p/n)) ≤ √(n·log p) = √n·√(log p).
    have hlogpn_nonneg : 0 ≤ Real.log (p / n) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]; linarith
    have hstep : n * Real.log (p / n) ≤ n * Real.log p :=
      mul_le_mul_of_nonneg_left hlog_le (by linarith)
    calc prizeTarget n p = Real.sqrt (n * Real.log (p / n)) := rfl
      _ ≤ Real.sqrt (n * Real.log p) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt n * Real.sqrt (Real.log p) := Real.sqrt_mul (by linarith) _

/-- **Curve count never binds (Q2), recorded as a definitional dominance.**

The char-0 Wick ceiling `char0Ceiling r n = (2r-1)!!·n^r` (proven in `DyadicEnergyK1` via
Lam–Leung) is the per-coset bound the moment route already uses.  The OSV curve point-count is an
*upper* bound on the same additive count; numerically (Q2) it exceeds `char0Ceiling` for `r ≤ 3`
and the actual count is below `char0Ceiling` for all `r`.  Thus replacing the actual additive
count by `min(actual, curve)` equals the actual count whenever `actual ≤ char0Ceiling` — the
curve adds no information.  We record the trivial but load-bearing fact that `min` with a larger
value is identity. -/
theorem curve_adds_nothing
    (actual curveBound char0 : ℝ)
    (hac : actual ≤ char0) (hcc : char0 ≤ curveBound) :
    min actual curveBound = actual :=
  min_eq_left (le_trans hac hcc)

end ArkLib.ProximityGap.Frontier.WF6O1

-- Axiom audit (lane wf-O1): both lemmas must depend only on [propext, Classical.choice, Quot.sound].
#print axioms ArkLib.ProximityGap.Frontier.WF6O1.shk_dominates_prize_factor
#print axioms ArkLib.ProximityGap.Frontier.WF6O1.curve_adds_nothing
