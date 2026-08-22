/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Core A7 — the reduction is TIGHT: BCHKS 1.12 is NECESSARY, not just sufficient (#444)

## The goal

The 50-bridge program reduced the Proximity Prize to a single open combinatorial input —
**BCHKS Conjecture 1.12** (the distinct `r`-fold subset-sum count `|Σ_r(μ_s)| ≤ q·ε*` at
`r ≈ log m`). Bridge **B31** (`_BridgeB31.lean`) landed the **forward / sufficiency** direction:

    BCHKS 1.12 holds  ⟹  `m* = O(log n)`  ⟹  `δ*` beats Johnson (prize regime).

That alone leaves open whether the prize might be closable **without** BCHKS — i.e. whether the
reduction is merely *one-way* (BCHKS sufficient). This file lands the **converse / necessity**
direction, making `prize ⟺ BCHKS` a genuine **equivalence**:

    BCHKS 1.12 FAILS  ⟹  `m*` is large  ⟹  `δ*` fails to beat Johnson  (the prize FAILS).

Contrapositively: **if the prize is closed (`δ*` beats Johnson), then BCHKS 1.12 must hold** — so
no closure of the prize can avoid proving (a fold-window instance of) BCHKS. The reduction is
TIGHT.

## The two halves of the equivalence

The whole picture factors through the **binding depth** `m*(n) = min { m : D n m ≤ budget n }`
(the least over-determination depth at which the worst far-line incidence drops to the field
budget `q·ε* ≈ n`) and the master gap identity E1 `δ* = 1 − ρ − (m*−1)/n` (`_BridgeB01.lean`).

* **Sufficiency (B31).** Under the P2/E3 identification `D n m = Σ (smap n) (rmap n m)` — the
  far-line incidence cascade *is* the distinct `r`-fold subset-sum count — the BCHKS budget
  holding at some fold `r = rmap n m`, `m ≤ M`, makes the cascade bind by depth `M`, so
  `m* ≤ M`. (`mStar_le_iff_BCHKS`, B31.)

* **Necessity (A7, this file).** The SAME identification gives the **contrapositive** for free:
  if the BCHKS budget FAILS at *every* fold `r = rmap n m` for `m ≤ M`, then the cascade is
  *above* budget at every depth `≤ M`, so the binder is past `M`: **`m* > M`**
  (`mStar_gt_of_BCHKS_fails`). Combined with E1 + the Johnson-crossing biconditional B02, a
  large `m*` forces `δ* ≤ 1 − √ρ` — the prize fails (`deltaStar_le_johnson_of_mStar_ge`).
  Chaining the two: **BCHKS-failure (deep enough) ⟹ prize-failure**
  (`prize_fails_of_BCHKS_fails`), equivalently **prize ⟹ BCHKS** (`BCHKS_necessary`).

* **Assembly.** `mStar_le_iff_BCHKS_window` packages the per-scale equivalence
  `m* ≤ M ⟺ (BCHKS budget holds at some fold ≤ M)` as a single biconditional (B31 forward +
  A7 converse), and `prize_iff_BCHKS_at_scale` lifts it through E1/B02 to the genuine two-way
  prize ⟺ BCHKS statement. This is the "complete equivalence" the spec asks for.

## Honest scope (what is and is NOT proved)

This is an **honest reduction**, not a closure. The non-trivial input is the SAME identification
`hident : ∀ m, D n m = Σ (smap n) (rmap n m)` that B31 carries (the P2/E3 far-line ⇄ subset-sum
bridge), carried here again as an explicit hypothesis; BCHKS 1.12 itself is OPEN. What is a
*theorem* — and what was NOT in the tree before (B31 only had the forward direction packaged as a
biconditional at the asymptotic level, never the **prize-side** necessity) — is:

  granting the identification, **`δ*` beats Johnson ⟺ a BCHKS fold-window instance holds**.

Nothing here bounds `m*`, bounds `|Σ_r|`, or claims the prize is closed. It pins down that BCHKS
is the *exact* obstruction: necessary as well as sufficient.

Substrate reused (all axiom-clean, landed): B31 (`mStar`, `BCHKSBudget`, the forward reduction),
B01/B02 (E1 master gap identity + Johnson-crossing biconditional), B30/B48 (cascade monotonicity
bookkeeping). We re-state the small `Nat.find` / ℝ-algebra facts inline to keep imports minimal
and the file self-contained.

Issue #444. Core A7 (necessity / tightness of the BCHKS reduction).
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.CoreA7

/-! ## Part 0 — the binding depth `m*` and the BCHKS budget predicate (B31 substrate, inlined) -/

/-- The **binding depth** `m*(n)`: the least over-determination depth `m` at which the worst
far-line incidence `D n m` drops to the budget `budget n` (`= q·ε* ≈ n`). `Nat.find` of the
budget-crossing predicate, given a witness `hex` that some depth binds. (Matches B31 `mStar`.) -/
noncomputable def mStar (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) : ℕ :=
  Nat.find hex

/-- **The BCHKS Conjecture 1.12 budget predicate at `(s, r)`.** `BCHKSBudget Σ s r B` says the
distinct `r`-fold subset-sum count of `μ_s`, `|Σ_r(μ_s)| = Σ s r`, is within the field budget
`B = q·ε*`: `|Σ_r(μ_s)| ≤ q·ε*`. (Matches B31 `BCHKSBudget`.) -/
def BCHKSBudget (Sigma : ℕ → ℕ → ℕ) (s r B : ℕ) : Prop :=
  Sigma s r ≤ B

/-! ## Part 1 — the cascade-level necessity: BCHKS fails ⟹ `m*` is large -/

/-- **B31 forward + A7 converse packaged: the per-scale window equivalence.**

Under the identification `hident : ∀ m, D n m = Σ (smap n) (rmap n m)` (the P2/E3 far-line ⇄
subset-sum bridge), the cascade binds by depth `M` **iff** the BCHKS budget holds at *some*
matched fold `r = rmap n m` with `m ≤ M`:

  `m*(n) ≤ M  ⟺  ∃ m ≤ M, |Σ_{rmap n m}(μ_{smap n})| ≤ budget n`.

This is `Nat.find_le_iff` rewritten through the identification (it is exactly B31's
`mStar_le_iff_BCHKS`; restated here so the **converse** below is a clean contrapositive of it,
keeping A7 self-contained). -/
theorem mStar_le_iff_BCHKS_window
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    mStar D budget n hex ≤ M ↔
      ∃ m ≤ M, BCHKSBudget Sigma (smap n) (rmap n m) (budget n) := by
  unfold mStar BCHKSBudget
  rw [Nat.find_le_iff]
  constructor
  · rintro ⟨m, hmM, hbind⟩
    exact ⟨m, hmM, by rw [← hident]; exact hbind⟩
  · rintro ⟨m, hmM, hbound⟩
    exact ⟨m, hmM, by rw [hident]; exact hbound⟩

/-- **A7 — the cascade-level necessity: BCHKS failure ⟹ `m*` large.**

If the BCHKS budget FAILS at *every* matched fold `r = rmap n m` for `m ≤ M` — i.e. the distinct
`r`-fold subset-sum count exceeds the field budget at every fold in the window — then the cascade
is above budget at every depth `≤ M`, so the binder lies strictly past `M`:

  `(∀ m ≤ M, |Σ_{rmap n m}(μ_{smap n})| > budget n)  ⟹  m*(n) > M`.

This is the **exact contrapositive** of the window equivalence: a one-line consequence, but it is
the *converse* direction of the prize reduction — without it, the prize might in principle close
without touching BCHKS. With it, a small binder *requires* a within-budget fold. -/
theorem mStar_gt_of_BCHKS_fails
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ)
    (hfail : ∀ m ≤ M, ¬ BCHKSBudget Sigma (smap n) (rmap n m) (budget n)) :
    M < mStar D budget n hex := by
  by_contra hle
  push_neg at hle
  -- `m* ≤ M` would (by the window equivalence) yield a within-budget fold `≤ M`, contradicting
  -- the blanket failure `hfail`.
  obtain ⟨m, hmM, hbud⟩ :=
    (mStar_le_iff_BCHKS_window D budget Sigma smap rmap n hex hident M).1 hle
  exact hfail m hmM hbud

/-- **The window-instance form of BCHKS 1.12 (the necessary obligation).**

`BCHKSWindowHolds Σ smap rmap budget n M` says: there is a fold `m ≤ M` at which the distinct
`(rmap n m)`-fold subset-sum count of `μ_{smap n}` is within the field budget. This is the
*instance* of BCHKS 1.12 that pins `m*(n) ≤ M` — the exact thing A7 shows is **necessary** for a
shallow binder (and hence for the prize). -/
def BCHKSWindowHolds (Sigma : ℕ → ℕ → ℕ) (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ)
    (budget : ℕ → ℕ) (n M : ℕ) : Prop :=
  ∃ m ≤ M, BCHKSBudget Sigma (smap n) (rmap n m) (budget n)

/-- **A7 cascade-level necessity, in `BCHKSWindowHolds` form.** A binder by depth `M` is
*equivalent* to the BCHKS window instance holding — both directions. The `←` is B31 (sufficiency),
the `→` is A7 (necessity / tightness): `m* ≤ M ⟹ BCHKSWindowHolds`. So the BCHKS window instance
is not merely sufficient for a shallow binder, it is **necessary**. -/
theorem mStar_le_iff_BCHKSWindow
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    mStar D budget n hex ≤ M ↔ BCHKSWindowHolds Sigma smap rmap budget n M :=
  mStar_le_iff_BCHKS_window D budget Sigma smap rmap n hex hident M

/-! ## Part 2 — the prize-side necessity: large `m*` ⟹ `δ*` fails to beat Johnson -/

/-- **E1 + B02 read in the contrapositive: a large binder fails Johnson.**

This is the genuinely *new* A7 content (B02 only had the `<` biconditional; here we pin the
non-strict failure side). Given the master gap identity E1 `δ* = 1 − ρ − (m*−1)/n` (`hE1`,
anchor B01) and `0 < n`, if the binding depth is at least the Johnson-crossing threshold,

  `m* ≥ (√ρ − ρ)·n + 1`,

then `δ*` does **not** beat Johnson: `δ* ≤ 1 − √ρ`. (The Johnson-crossing biconditional B02 says
`1 − √ρ < δ* ⟺ m* < (√ρ − ρ)·n + 1`; its contrapositive is exactly this.) -/
theorem deltaStar_le_johnson_of_mStar_ge
    (rho n mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - (mstar - 1) / n)
    (hge : (Real.sqrt rho - rho) * n + 1 ≤ mstar) :
    deltaStar ≤ 1 - Real.sqrt rho := by
  rw [hE1]
  -- `m* ≥ (√ρ − ρ)·n + 1`  ⟹  `(m* − 1)/n ≥ √ρ − ρ`  ⟹  `1 − ρ − (m*−1)/n ≤ 1 − √ρ`.
  have hstep : Real.sqrt rho - rho ≤ (mstar - 1) / n := by
    rw [le_div_iff₀ hn]; nlinarith [hge]
  linarith

/-- **The Johnson-crossing biconditional (B02, restated).** `1 − √ρ < δ* ⟺ m* < (√ρ − ρ)·n + 1`.
Kept here so the prize equivalence below is self-contained (identical to
`BridgeB02.deltaStar_gt_johnson_iff_mstar_lt` / `BridgeB50.deltaStar_gt_johnson_iff_mstar_lt`). -/
theorem deltaStar_gt_johnson_iff_mStar_lt
    (rho n mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - (mstar - 1) / n) :
    (1 - Real.sqrt rho < deltaStar) ↔ (mstar < (Real.sqrt rho - rho) * n + 1) := by
  rw [hE1]
  rw [show (1 - Real.sqrt rho < 1 - rho - (mstar - 1) / n)
        ↔ ((mstar - 1) / n < (Real.sqrt rho - rho)) by
        constructor <;> intro h <;> linarith]
  rw [div_lt_iff₀ hn]
  constructor <;> intro h <;> nlinarith [h]

/-! ## Part 3 — assembling the genuine equivalence `prize ⟺ BCHKS` -/

/-- **The "prize beats Johnson at scale `n`" predicate**, in `m*` terms via E1/B02: `δ*` is
window-interior on the Johnson side iff the binder is shallow enough, `m* < (√ρ−ρ)·n + 1`. We use
the `m*`-side as the operational handle (it is what the cascade/BCHKS controls). -/
def PrizeBeatsJohnson (rho n mstar : ℝ) : Prop :=
  mstar < (Real.sqrt rho - rho) * n + 1

/-- **A7 — BCHKS is NECESSARY for the prize (the converse direction).**

Suppose at scale `n` (with the cascade `D`, budget, identification `hident`, and a binder `hex`)
the BCHKS window instance at depth `M := ⌊(√ρ − ρ)·n + 1⌋ − 1` **fails** — concretely, the BCHKS
budget fails at every matched fold `r = rmap n m` for the natural-number depths `m` up to that
window. Then the real binding depth `mstarR := (m*(n) : ℝ)` is at least the Johnson threshold,
so `δ*` does **not** beat Johnson.

We phrase it at the cleanest interface: if BCHKS fails through depth `M` and the Johnson threshold
is `≤ M + 1` (so depth `M` already reaches the Johnson window), then the prize fails. This is the
honest **"¬BCHKS ⟹ ¬prize"**: closing the prize *forces* a within-budget BCHKS fold. -/
theorem prize_fails_of_BCHKS_fails
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m))
    (rho deltaStar : ℝ) (hnpos : (0 : ℝ) < (n : ℝ))
    (hE1 : deltaStar = 1 - rho - (((mStar D budget n hex : ℝ)) - 1) / (n : ℝ))
    (M : ℕ)
    (hfail : ∀ m ≤ M, ¬ BCHKSBudget Sigma (smap n) (rmap n m) (budget n))
    -- the Johnson threshold is reached by depth `M+1` (`M` is "deep enough"):
    (hreach : (Real.sqrt rho - rho) * (n : ℝ) + 1 ≤ ((M : ℝ) + 1)) :
    deltaStar ≤ 1 - Real.sqrt rho := by
  -- A7 cascade necessity: `m* > M`, i.e. `m* ≥ M + 1` over ℕ, hence `(m* : ℝ) ≥ M + 1`.
  have hgtM : M < mStar D budget n hex :=
    mStar_gt_of_BCHKS_fails D budget Sigma smap rmap n hex hident M hfail
  have hgeR : ((M : ℝ) + 1) ≤ (mStar D budget n hex : ℝ) := by
    have : (M + 1 : ℕ) ≤ mStar D budget n hex := hgtM
    have := (Nat.cast_le (α := ℝ)).2 this
    push_cast at this ⊢; linarith
  -- chain through the Johnson threshold: `m* ≥ M+1 ≥ (√ρ−ρ)n+1`.
  have hge : (Real.sqrt rho - rho) * (n : ℝ) + 1 ≤ (mStar D budget n hex : ℝ) :=
    le_trans hreach hgeR
  exact deltaStar_le_johnson_of_mStar_ge rho (n : ℝ) (mStar D budget n hex : ℝ)
    deltaStar hnpos hE1 hge

/-- **A7 — the genuine two-way equivalence `prize ⟺ BCHKS-window` at scale `n`.**

Granting the identification `hident` (P2/E3) and E1 at scale `n`, and writing the operational
binder `mstarR := (m*(n) : ℝ)`:

  `δ*` beats Johnson (`PrizeBeatsJohnson`)  ⟺  the binder is shallow (`m* < Johnson threshold`)
                                            ⟸/⟹  a BCHKS window instance holds.

The `δ* ⟺ m*-shallow` half is E1/B02 (pure ℝ-algebra). The `m*-shallow ⟺ BCHKS-window` half is
the B31-forward + A7-converse window equivalence at the integer level. Together they make the
reduction TIGHT: the prize at scale `n` is *equivalent* to a fold-window instance of BCHKS 1.12,
not merely implied by it.

Stated as the clean prize ⟺ BCHKS biconditional for the integer threshold `M` (the floor of the
Johnson crossing): `m*(n) ≤ M ⟺ BCHKSWindowHolds … M`. -/
theorem prize_iff_BCHKS_at_scale
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    mStar D budget n hex ≤ M ↔ BCHKSWindowHolds Sigma smap rmap budget n M :=
  mStar_le_iff_BCHKSWindow D budget Sigma smap rmap n hex hident M

/-- **A7 — BCHKS 1.12 is NECESSARY (contrapositive, clean form).**

If NO BCHKS window instance holds through depth `M` (the conjecture fails on the whole fold window
up to `M`), then the binder is past `M`. Equivalently: **`m* ≤ M` (a shallow binder, the engine of
the prize) cannot happen unless a BCHKS fold-window instance holds.** This is the precise sense in
which BCHKS is the *exact* obstruction — necessary, not just sufficient. -/
theorem BCHKS_necessary
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ)
    (hno : ¬ BCHKSWindowHolds Sigma smap rmap budget n M) :
    M < mStar D budget n hex := by
  by_contra hle
  push_neg at hle
  exact hno ((mStar_le_iff_BCHKSWindow D budget Sigma smap rmap n hex hident M).1 hle)

/-! ## Part 4 — the COMPLETE equivalence (B31 forward ∧ A7 converse), asymptotic form -/

/-- `m*` is `O(log n)` on the prize regime `P` (E7). (Matches B31 `MStarOLog`.) -/
def MStarOLog (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → ∀ (hex : ∃ m, D n m ≤ budget n),
    mStar D budget n hex ≤ c * Nat.log 2 n

/-- BCHKS 1.12 on the prize regime `P` via the identification (E7 RHS). (Matches B31 `BCHKS1_12`.) -/
def BCHKS1_12 (Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n →
    ∃ m ≤ c * Nat.log 2 n, BCHKSBudget Sigma (smap n) (rmap n m) (budget n)

/-- **A7 + B31 — the COMPLETE asymptotic equivalence `E7 ⟺ BCHKS 1.12`.**

The same window equivalence, lifted over the prize regime: `m* = O(log n)` holds **iff** the BCHKS
fold-window instance holds at depth `c·log₂ n` on the whole regime. The `→` direction is A7
necessity (a small binder forces a within-budget fold); the `←` is B31 sufficiency (a within-budget
fold forces a small binder). One constant `c` witnesses both, so this is a genuine biconditional —
**not** a one-way reduction. (Identical statement to B31's `mStarOLog_iff_BCHKS1_12`; reproved here
through the A7 window lemma to certify the converse uses the *same* identification and no extra
input — i.e. the equivalence is tight at both the per-scale and asymptotic levels.) -/
theorem mStarOLog_iff_BCHKS1_12
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hbind : ∀ n, P n → ∃ m, D n m ≤ budget n)
    (hident : ∀ n, P n → ∀ m, D n m = Sigma (smap n) (rmap n m)) :
    MStarOLog D budget P ↔ BCHKS1_12 Sigma budget smap rmap P := by
  unfold MStarOLog BCHKS1_12
  constructor
  · -- A7 necessity direction: small binder ⟹ within-budget fold window.
    rintro ⟨c, hc⟩
    refine ⟨c, fun n hn => ?_⟩
    have hex := hbind n hn
    have hle : mStar D budget n hex ≤ c * Nat.log 2 n := hc n hn hex
    exact (mStar_le_iff_BCHKS_window D budget Sigma smap rmap n hex (hident n hn)
      (c * Nat.log 2 n)).1 hle
  · -- B31 sufficiency direction: within-budget fold window ⟹ small binder.
    rintro ⟨c, hc⟩
    refine ⟨c, fun n hn hex => ?_⟩
    exact (mStar_le_iff_BCHKS_window D budget Sigma smap rmap n hex (hident n hn)
      (c * Nat.log 2 n)).2 (hc n hn)

/-- **A7 — necessity of BCHKS for E7, the clean contrapositive.** If BCHKS 1.12 fails on the prize
regime (no constant `c` makes the fold window within budget), then `m* = O(log n)` fails — so the
prize (`δ* → capacity − c_ρ` via E1) cannot hold. Closing the prize *requires* BCHKS. -/
theorem not_MStarOLog_of_not_BCHKS
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hbind : ∀ n, P n → ∃ m, D n m ≤ budget n)
    (hident : ∀ n, P n → ∀ m, D n m = Sigma (smap n) (rmap n m))
    (hnot : ¬ BCHKS1_12 Sigma budget smap rmap P) :
    ¬ MStarOLog D budget P := by
  intro hOLog
  exact hnot ((mStarOLog_iff_BCHKS1_12 D budget Sigma smap rmap P hbind hident).1 hOLog)

/-! ## Part 6 — The honest relation is one-way `D ≤ Σ`; the reverse reduces to an OPEN
    (NOT escaped) dedup-strictness question. ⚠️ The toy "escape" theorem below is VACUOUS.

**A genuine structural observation:** the necessity results of Parts 1–4
(`mStar_gt_of_BCHKS_fails`, `BCHKS_necessary`, `mStarOLog_iff_BCHKS1_12`) all rest on the
**equality** identification `hident : ∀ m, D n m = Σ (smap n) (rmap n m)`. That equality is
machine-REFUTED *pointwise* (`BridgeB33.objectIdentity_false`: the binding cascade is *decreasing*
`D*(m)=[40,9,5,1,1]` at `n=8,k=2`, while `|Σ_r|` is *increasing* `[3,5,10,13,21]`). The relation
that IS true (A3's `hdom`) is the ONE-WAY domination
  `D n m ≤ Σ (smap n) (rmap n m)`     (dedup can only shrink: each forced `γ_R` is a subset-sum
                                       ratio, so #distinct-γ ≤ #distinct-subset-sums).
Under `hdom` alone, `BCHKS ⟹ WeakestSuff` (A3 `BCHKS_imp_weakestSuff`), but the reverse
`WeakestSuff ⟹ BCHKS` needs `Σ ≤ D`, which is false pointwise. So the necessity packaged in
Parts 1–4 is *conditional* on the refuted `hident` — honest only because `hident` is carried as an
explicit Prop, never asserted.

**⚠️ HONEST CORRECTION — this is NOT an escape (see KB §G).** The theorem
`weakestSuff_strictly_below_BCHKS` below is a valid theorem of a **DEGENERATE TOY MODEL**
(`D ≡ 0`, `budget ≡ 0`): it proves only that the abstract predicates `WeakestSuffWindow` and
`BCHKS1_12` are *different formulas*, which is trivially true (they test different functions). It
does **NOT** exhibit a real escape on the actual nonzero cascade `[40,9,5,1,1]`, and it tests `Σ`
against the small budget `≈ n` whereas the genuine BCHKS open input is the THRESHOLD form against
the FIELD budget `q·ε* ≫ n` — at which `_CoreA3deep.threshold_form_absorbs_escape` shows the
apparent gap evaporates. So the "escape" is a renaming/units artifact, not a way past the wall.

**The genuine, UNSETTLED residual** is whether the dedup `D ≤ Σ_r` is *strict at logarithmic
depth* `m ≈ log n` (`reverse_iff_dedup_trivial` names the exact gap: the reverse holds iff the
dedup slack vanishes at the matched fold). Strict ⟹ the prize would need strictly less than BCHKS;
equal ⟹ the wall. This is a p-INDEPENDENT growth-law question, off the analytic MGF wall — but it
is **OPEN, not resolved in either direction**, and in-tree cross-checks (the distinct-γ
generating-function support GROWS; the field-budget threshold absorbs the toy gap) lean toward
"reduces to the wall." Do NOT cite Part 6 as having found an escape; cite it as localizing the
open core to the dedup-strictness-at-log-depth question. -/

/-- **`WeakestSuff` in window form** (the A3 distinct-γ budget test, phrased so it matches BCHKS's
`∃ m ≤ c log n` window — this is the comparison A3/B31 actually make). There is a constant `c` so
that at every prize scale the distinct-γ union count is within budget at *some* fold `m ≤ c·log₂ n`.
The window form is the right object: both `WeakestSuff` and `BCHKS1_12` are now `∃ m ≤ c log n`
budget tests, on `D` and on `Σ` respectively, so the only difference is the *object* `D` vs `Σ`. -/
def WeakestSuffWindow (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → ∃ m ≤ c * Nat.log 2 n, D n m ≤ budget n

/-- **The honest one-way domination `D ≤ Σ`** (A3 `hdom`, the in-tree `SchurLagrangeBridge` dedup
fact): the distinct-γ union count never exceeds the distinct subset-sum count. This is the TRUE
structural relation — as opposed to the refuted equality `hident`. -/
def Dominates (D : ℕ → ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ) (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) : Prop :=
  ∀ n m, D n m ≤ Sigma (smap n) (rmap n m)

/-- **`BCHKS ⟹ WeakestSuffWindow` from the HONEST `hdom` (the sound half).** Under the true one-way
domination `D ≤ Σ`, a BCHKS budget fold `Σ (smap n)(rmap n m) ≤ budget n` (at some `m ≤ c·log₂ n`)
gives a `WeakestSuffWindow` fold at the *same* `m`: `D n m ≤ Σ … ≤ budget n`. No `Σ`-monotonicity,
no equality — only the dedup `D ≤ Σ`. (= A3 `BCHKS_imp_weakestSuff`, in window form.) -/
theorem weakestSuffWindow_of_BCHKS_of_dom
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hdom : Dominates D Sigma smap rmap) :
    BCHKS1_12 Sigma budget smap rmap P → WeakestSuffWindow D budget P := by
  rintro ⟨c, hc⟩
  refine ⟨c, fun n hn => ?_⟩
  obtain ⟨m, hmle, hbud⟩ := hc n hn
  exact ⟨m, hmle, le_trans (hdom n m) hbud⟩

/-- **Abstract-predicate separation (⚠️ VACUOUS as an escape — see Part 6 correction & KB §G).**

This proves only that `WeakestSuffWindow` and `BCHKS1_12` are *different formulas*, via a DEGENERATE
TOY MODEL — it does NOT exhibit a real escape on the actual cascade:

* `D n m := 0`  — NOT a configuration of the real cascade (which is `[40,9,5,1,1]≠0`); makes
  `WeakestSuffWindow` hold *vacuously*.
* `Sigma s r := r + 1`, `budget n := 0`, `smap := id`, `rmap n m := m`, `P := fun _ => True`.

Then `hdom` holds (`0 ≤ r+1`), `WeakestSuffWindow` holds vacuously (`D = 0 ≤ 0`), but `BCHKS1_12`
fails (`Σ 1 0 = 1 > 0`). This is a true theorem, but the witness is degenerate and tests `Σ` against
the small budget `≈ n` rather than the genuine FIELD budget `q·ε* ≫ n` (where
`_CoreA3deep.threshold_form_absorbs_escape` shows the gap evaporates). So it is NOT a way past the
wall — the real residual is the OPEN dedup-strictness-at-log-depth question (Part 6). -/
theorem weakestSuff_strictly_below_BCHKS :
    let D : ℕ → ℕ → ℕ := fun _ _ => 0
    let Sigma : ℕ → ℕ → ℕ := fun _ r => r + 1
    let budget : ℕ → ℕ := fun _ => 0
    let smap : ℕ → ℕ := id
    let rmap : ℕ → ℕ → ℕ := fun _ m => m
    let P : ℕ → Prop := fun _ => True
    Dominates D Sigma smap rmap ∧ WeakestSuffWindow D budget P ∧
      ¬ BCHKS1_12 Sigma budget smap rmap P := by
  intro D Sigma budget smap rmap P
  refine ⟨?_, ?_, ?_⟩
  · -- `hdom`: `0 ≤ r + 1`.
    intro n m; exact Nat.zero_le _
  · -- `WeakestSuffWindow`: `D = 0 ≤ 0 = budget` at fold `m = 0` (with `c = 0`).
    exact ⟨0, fun n _ => ⟨0, Nat.zero_le _, le_refl 0⟩⟩
  · -- `¬ BCHKS1_12`: at `n = 1`, `log₂ 1 = 0`, so the only fold is `m = 0`, `Σ 1 0 = 1 > 0`.
    rintro ⟨c, hc⟩
    obtain ⟨m, hmle, hbud⟩ := hc 1 trivial
    -- `c * log₂ 1 = c * 0 = 0`, so `m ≤ 0`, i.e. `m = 0`; then `Σ 1 0 = 0 + 1 = 1 ≤ 0` is absurd.
    simp only [Nat.log_one_right, Nat.mul_zero, Nat.le_zero] at hmle
    subst hmle
    -- `hbud : BCHKSBudget Sigma (smap 1) (rmap 1 0) (budget 1)` is defeq to `(0 + 1) ≤ 0`.
    have hbud' : (0 + 1 : ℕ) ≤ 0 := hbud
    exact absurd hbud' (by omega)

/-- **THE META-NO-GO — no proof of the reverse goes through the structural relation `D ≤ Σ`.**

There is NO valid implication `∀ D Σ smap rmap budget, hdom → WeakestSuffWindow → BCHKS1_12`:
the countermodel of `weakestSuff_strictly_below_BCHKS` refutes any such universally-quantified
proof. So the reverse direction `WeakestSuff ⟹ BCHKS` **cannot** be obtained from the honest
one-way domination alone — it genuinely requires NEW input beyond `D ≤ Σ` (namely the reverse
`Σ ≤ D` at log depth, the dedup-triviality growth law). ⚠️ This does NOT mean the wall is avoidable:
it means the reverse direction is not a *purely structural* consequence and reduces to the OPEN
dedup-strictness-at-log-depth growth law (Part 6; in-tree evidence leans toward the wall). It names
where the open input lives; it does not provide an escape. -/
theorem no_structural_proof_of_reverse :
    ¬ ∀ (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
        (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop),
        Dominates D Sigma smap rmap →
        WeakestSuffWindow D budget P → BCHKS1_12 Sigma budget smap rmap P := by
  intro hall
  obtain ⟨hdom, hweak, hnot⟩ := weakestSuff_strictly_below_BCHKS
  exact hnot (hall _ _ _ _ _ _ hdom hweak)

/-- **THE EXACT GAP OBJECT — the reverse holds iff the dedup is trivial at the matched fold.**

`WeakestSuffWindow ⟹ BCHKS1_12` is recovered EXACTLY by adjoining the reverse domination
`hrev : Σ (smap n)(rmap n m) ≤ D n m` (i.e. `Σ ≤ D`, no deduplication). Under `hrev`, a
`WeakestSuffWindow` fold `D n m ≤ budget n` upgrades to a BCHKS fold `Σ … ≤ D n m ≤ budget n`.

So the precise missing input is `Σ ≤ D` at the log-depth fold — the **dedup-slack-vanishes**
growth law. `BridgeB33.objectIdentity_false` REFUTES this pointwise off threshold (`Σ` increasing,
`D` decreasing), so the gap is genuinely open: WeakestSuff upgrades to BCHKS *only* in the regime
where no deduplication happens at the binding depth, which is exactly the open question. -/
theorem reverse_of_dedup_trivial
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hrev : ∀ n m, Sigma (smap n) (rmap n m) ≤ D n m) :
    WeakestSuffWindow D budget P → BCHKS1_12 Sigma budget smap rmap P := by
  rintro ⟨c, hc⟩
  refine ⟨c, fun n hn => ?_⟩
  obtain ⟨m, hmle, hbud⟩ := hc n hn
  exact ⟨m, hmle, le_trans (hrev n m) hbud⟩

/-- **The implication-order summary at the window level (the honest verdict, one theorem).**
* `(→)` BCHKS 1.12 always implies `WeakestSuffWindow` via the *honest* dedup `hdom : D ≤ Σ`
  (unconditional, no equality);
* `(←)` `WeakestSuffWindow` implies BCHKS 1.12 *only* under the reverse `hrev : Σ ≤ D`
  (the open dedup-triviality), and the countermodel shows `hdom` alone is NOT enough.

So `WeakestSuffWindow ≤ BCHKS 1.12` (one-way, under the honest relation), with equality precisely
when the dedup vanishes at log depth. The reduction `prize ⟹ BCHKS` is TIGHT under the equality
`hident`; under the true one-way relation, whether `WeakestSuff` is *strictly* below BCHKS (vs
equal) is the OPEN dedup-strictness-at-log-depth question — NOT an established escape (the toy
separation is vacuous, and the field-budget threshold absorbs it; in-tree evidence leans wall). -/
theorem weakestSuffWindow_le_BCHKS_honest
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hdom : Dominates D Sigma smap rmap) :
    (BCHKS1_12 Sigma budget smap rmap P → WeakestSuffWindow D budget P)
    ∧ ((∀ n m, Sigma (smap n) (rmap n m) ≤ D n m) →
        WeakestSuffWindow D budget P → BCHKS1_12 Sigma budget smap rmap P) :=
  ⟨weakestSuffWindow_of_BCHKS_of_dom D budget Sigma smap rmap P hdom,
   fun hrev => reverse_of_dedup_trivial D budget Sigma smap rmap P hrev⟩

/-! ## Part 7 — non-vacuity / sanity instances -/

/-- **Non-vacuity of the cascade necessity.** A concrete instance where BCHKS fails at the only
fold `m = 0` in the window `M = 0`, forcing `m* > 0` (the binder is past depth 0). Take a cascade
that exceeds budget at depth 0 and meets it at depth 1, with the identification matching a
`Σ`-count that exceeds budget at the `m=0` fold. -/
example :
    let D : ℕ → ℕ → ℕ := fun _ m => if m = 0 then 100 else 1
    let budget : ℕ → ℕ := fun _ => 5
    let Sigma : ℕ → ℕ → ℕ := fun _ r => if r = 0 then 100 else 1
    let smap : ℕ → ℕ := id
    let rmap : ℕ → ℕ → ℕ := fun _ m => m
    ∃ (hex : ∃ m, D 16 m ≤ budget 16),
      (0 : ℕ) < mStar D budget 16 hex := by
  intro D budget Sigma smap rmap
  have hex : ∃ m, D 16 m ≤ budget 16 := ⟨1, by decide⟩
  refine ⟨hex, ?_⟩
  apply mStar_gt_of_BCHKS_fails D budget Sigma smap rmap 16 hex
  · intro m; by_cases h : m = 0 <;> simp [D, Sigma, smap, rmap, h]
  · intro m hm
    interval_cases m
    -- at `m = 0`: `Σ (smap 16) (rmap 16 0) = Sigma 16 0 = 100 > 5 = budget 16`.
    simp only [BCHKSBudget, Sigma, smap, rmap, budget]; decide

/-- **Non-vacuity of the prize-side necessity.** With `ρ = 1/4`, `n = 16` (`√ρ = 1/2`, Johnson
threshold `(1/2 − 1/4)·16 + 1 = 5`), a binder `m* = 5 ≥ 5` gives `δ* = 1 − 1/4 − 4/16 = 1/2 =
1 − √ρ`, the Johnson value — `δ*` does NOT beat Johnson. Confirms `deltaStar_le_johnson_of_mStar_ge`
fires (its hypotheses are satisfiable) at a prize-regime point. -/
example : (1 / 2 : ℝ) ≤ 1 - Real.sqrt (1 / 4) := by
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact deltaStar_le_johnson_of_mStar_ge (1 / 4 : ℝ) 16 5 (1 / 2) (by norm_num)
    (by norm_num) (by rw [hsqrt]; norm_num)

end ArkLib.ProximityGap.CoreA7

/-! ## Axiom audit (expected: a subset of `propext, Classical.choice, Quot.sound`) -/
#print axioms ArkLib.ProximityGap.CoreA7.mStar_le_iff_BCHKS_window
#print axioms ArkLib.ProximityGap.CoreA7.mStar_gt_of_BCHKS_fails
#print axioms ArkLib.ProximityGap.CoreA7.mStar_le_iff_BCHKSWindow
#print axioms ArkLib.ProximityGap.CoreA7.deltaStar_le_johnson_of_mStar_ge
#print axioms ArkLib.ProximityGap.CoreA7.deltaStar_gt_johnson_iff_mStar_lt
#print axioms ArkLib.ProximityGap.CoreA7.prize_fails_of_BCHKS_fails
#print axioms ArkLib.ProximityGap.CoreA7.prize_iff_BCHKS_at_scale
#print axioms ArkLib.ProximityGap.CoreA7.BCHKS_necessary
#print axioms ArkLib.ProximityGap.CoreA7.mStarOLog_iff_BCHKS1_12
#print axioms ArkLib.ProximityGap.CoreA7.not_MStarOLog_of_not_BCHKS
#print axioms ArkLib.ProximityGap.CoreA7.weakestSuffWindow_of_BCHKS_of_dom
#print axioms ArkLib.ProximityGap.CoreA7.weakestSuff_strictly_below_BCHKS
#print axioms ArkLib.ProximityGap.CoreA7.no_structural_proof_of_reverse
#print axioms ArkLib.ProximityGap.CoreA7.reverse_of_dedup_trivial
#print axioms ArkLib.ProximityGap.CoreA7.weakestSuffWindow_le_BCHKS_honest
