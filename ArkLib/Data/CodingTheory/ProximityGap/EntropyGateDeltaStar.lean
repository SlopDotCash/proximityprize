/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandCeilingWindow
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The entropy-gate δ* ceiling, wired to the in-tree window consumer (#389)

`mcaDeltaStar_le_of_ceiling_window` (DeepBandCeilingWindow.lean) fires the per-band ceiling
from the integer window `ε*·q·(C'+2)² + 1 ≤ ⌊P·(C'+2)/q^m⌋` and `P < q^{m+1}`.  This file
discharges those two integer hypotheses from the **entropy gate** — i.e. the binomial-tail
inequalities that the probe `probe_ceiling_constant.py` validates as
`δ* ≤ 1 − ρ − H(ρ)/(β log₂n − H'(ρ))`:

* lower wall `a!·(2·q^m) ≤ (n+1−a)^a` is the integer form of `log₂C(n,a) ≥ … + log₂(2q^m)`
  (i.e. `H(a/n)·n ≳ (a−k)·β log₂n`), placing enough witness mass;
* upper wall `n^a < a!·q^{m+1}` is the truncation-collapse `C(n,a) < q^{m+1}`.

Result: `mcaDeltaStar_le_of_entropy_gate` — one-binomial-sandwich-in, δ*-ceiling-out, with
the onset radius `a = k+m+1` placed by the entropy condition.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal
open Nat

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code
open ProximityGap.MCAThresholdLedger

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- `(univ : Finset (Fin n)).powersetCard a).card = C(n,a)`. -/
private theorem powCard_eq_choose (a : ℕ) :
    ((Finset.univ : Finset (Fin n)).powersetCard a).card = n.choose a := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Binomial two-sided sandwich.** `(n+1-a)^a ≤ a!·C(n,a) ≤ n^a`. -/
private theorem choose_sandwich (N a : ℕ) :
    (N + 1 - a) ^ a ≤ a ! * N.choose a ∧ a ! * N.choose a ≤ N ^ a := by
  have hdf : N.descFactorial a = a ! * N.choose a :=
    Nat.descFactorial_eq_factorial_mul_choose N a
  exact ⟨hdf ▸ Nat.pow_sub_le_descFactorial N a, hdf ▸ Nat.descFactorial_le_pow N a⟩

/-- **The log₂ (entropy) form of the lower wall.**  The integer lower wall
`a!·(2·q^m) ≤ (n+1−a)^a` is implied by the real `log₂`-domain inequality
`log₂(a!·2·q^m) ≤ a·log₂(n+1−a)`.  Spelling out the left side with Stirling
`log₂ a! = a log₂ a − a/ln2 + O(log a)` and `log₂ q^m = β m log₂ n` (for `q = n^β`),
and the right with `a·log₂(n+1−a) = a·log₂ n + a·log₂((n+1−a)/n)`, this is exactly the
entropy condition `H(a/n)·n ≳ β m log₂ n` that the probe `probe_ceiling_constant.py`
validates — the analytic frontier `δ* ≤ 1−ρ−H(ρ)/(β log₂ n − H'(ρ))`.  Here we prove the
clean monotone-exponential half (log-domain ⟹ integer-domain); the Stirling/entropy
identification of the left side is the remaining `Nat.choose ↔ Real.binEntropy` bridge. -/
theorem lower_wall_of_logb {N a M : ℕ} (hNa : a ≤ N)
    (hlog : Real.logb 2 ((a ! * M : ℕ) : ℝ) ≤ (a : ℝ) * Real.logb 2 ((N + 1 - a : ℕ) : ℝ)) :
    a ! * M ≤ (N + 1 - a) ^ a := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · simp [hM]
  -- both sides positive; pull through logb (base 2 > 1, monotone)
  have hNa1 : 1 ≤ N + 1 - a := by omega
  have hbasepos : (0 : ℝ) < ((N + 1 - a : ℕ) : ℝ) := by exact_mod_cast hNa1
  have hLpos : (0 : ℝ) < ((a ! * M : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos a) hM
  have hRpos : (0 : ℝ) < (((N + 1 - a) ^ a : ℕ) : ℝ) := by
    have : 0 < (N + 1 - a) ^ a := Nat.pow_pos hNa1
    exact_mod_cast this
  -- rewrite RHS log as a·logb(base)
  have hlog2 : (a : ℝ) * Real.logb 2 ((N + 1 - a : ℕ) : ℝ)
      = Real.logb 2 (((N + 1 - a) ^ a : ℕ) : ℝ) := by
    push_cast
    rw [Real.logb_pow]
  rw [hlog2] at hlog
  -- logb base 2 is monotone on positives ⟹ cast inequality
  have hcast : ((a ! * M : ℕ) : ℝ) ≤ (((N + 1 - a) ^ a : ℕ) : ℝ) := by
    rwa [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hLpos hRpos] at hlog
  exact_mod_cast hcast

open Classical in
/-- **The deep-band δ\* ceiling from the entropy gate** (#389).  Write `a := k+m+1`,
`q := |F|`, `P := C(n,a)`, `C' := C(a,k+1)·C(n−(k+1),m)`.  Under

* the **lower entropy wall**  `a!·(2·q^m) ≤ (n+1−a)^a`  (witness mass clears the budget:
  `H(a/n)·n ≳ (a−k)·log₂q`, i.e. `P ≥ 2q^m`),
* the **upper truncation wall**  `n^a < a!·q^{m+1}`  (`P < q^{m+1}`, the `Λ`-collapse),
* the threshold smallness  `ε*·(q·(C'+2)²) ≤ 1`  (true at `ε* = 2^-128` for any
  polynomial `q,C'`),

the MCA threshold obeys `mcaDeltaStar (rsCode dom k) ε* ≤ δ` at every band radius
`(1−δ)n ≤ a`.  The two walls are discharged from the binomial sandwich
`(n+1−a)^a ≤ a!·C(n,a) ≤ n^a`; the δ* content is the in-tree
`mcaDeltaStar_le_of_ceiling_window`. -/
theorem mcaDeltaStar_le_of_entropy_gate (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (εstar : ℝ≥0∞) (hε : εstar ≠ ⊤)
    -- the entropy gate, integer form (binomial-tail walls):
    (hlo : (k + m + 1)! * (2 * (Fintype.card F) ^ m)
        ≤ (n + 1 - (k + m + 1)) ^ (k + m + 1))
    (hhiwall : n ^ (k + m + 1) < (k + m + 1)! * (Fintype.card F) ^ (m + 1))
    -- threshold smallness (ε*=2^-128 makes this trivially true for polynomial q, C'):
    (hsmall : εstar * ((Fintype.card F : ℝ≥0∞)
          * (↑((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2) ≤ 1) :
    mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ := by
  classical
  set a : ℕ := k + m + 1 with ha
  set q : ℕ := Fintype.card F with hq
  set Cc : ℕ := (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m with hCc
  -- the two integer window walls from the binomial sandwich
  have hsw := choose_sandwich n a
  -- upper wall : P < q^{m+1}
  have hPhi : ((Finset.univ : Finset (Fin n)).powersetCard a).card < q ^ (m + 1) := by
    rw [powCard_eq_choose]
    have : a ! * n.choose a < a ! * q ^ (m + 1) := lt_of_le_of_lt hsw.2 hhiwall
    exact Nat.lt_of_mul_lt_mul_left this
  -- lower wall : 2·q^m ≤ P
  have hPlo : 2 * q ^ m ≤ n.choose a := by
    have h1 : a ! * (2 * q ^ m) ≤ a ! * n.choose a := le_trans hlo hsw.1
    exact Nat.le_of_mul_le_mul_left h1 (Nat.factorial_pos a)
  -- ⌊P·(C'+2)/q^m⌋ ≥ 2 : from 2·q^m ≤ P ≤ P·(C'+2)/2 (since C'+2 ≥ 2)... do it directly
  have hCc2 : 2 ≤ Cc + 2 := Nat.le_add_left 2 Cc
  -- P·(C'+2) ≥ 2·q^m·(C'+2) ≥ 2·q^m·2 ≥ q^m·4; want ⌊P·(C'+2)/q^m⌋ ≥ 2 ⟺ 2·q^m ≤ P·(C'+2)
  have hqm_pos : 0 < q ^ m := Nat.pow_pos (by rw [hq]; exact Fintype.card_pos)
  have hnum_ge : 2 * q ^ m ≤ n.choose a * (Cc + 2) := by
    calc 2 * q ^ m ≤ n.choose a := hPlo
      _ = n.choose a * 1 := (Nat.mul_one _).symm
      _ ≤ n.choose a * (Cc + 2) := by
            exact Nat.mul_le_mul_left _ (by omega)
  have hfloor2 : 2 ≤ n.choose a * (Cc + 2) / q ^ m := by
    rw [Nat.le_div_iff_mul_le hqm_pos]
    calc 2 * q ^ m ≤ n.choose a * (Cc + 2) := hnum_ge
      _ = n.choose a * (Cc + 2) := rfl
  -- now assemble hwin in ℝ≥0∞
  have hwin : εstar * ((q : ℝ≥0∞)
        * (↑(Cc + 2) : ℝ≥0∞) ^ 2) + 1
      ≤ (↑(((Finset.univ : Finset (Fin n)).powersetCard a).card * (Cc + 2) / q ^ m) : ℝ≥0∞) := by
    rw [powCard_eq_choose]
    calc εstar * ((q : ℝ≥0∞) * (↑(Cc + 2) : ℝ≥0∞) ^ 2) + 1
        ≤ 1 + 1 := by
          gcongr
      _ = ((2 : ℕ) : ℝ≥0∞) := by norm_num
      _ ≤ (↑(n.choose a * (Cc + 2) / q ^ m) : ℝ≥0∞) := by
          exact_mod_cast hfloor2
  -- fire the in-tree window consumer
  exact mcaDeltaStar_le_of_ceiling_window dom hk hhi εstar hε hPhi hwin

instance primeFact_EntropyGateDeltaStar_1 : Fact (Nat.Prime 31) := ⟨by decide⟩

/-- **Non-vacuity of the entropy gate.**  `RS[F₃₁, 10 pts, k=2]`, band `m=1` (agreement
`a = 4`, radius `δ = 3/5`).  The entropy gate is satisfied by exact integer arithmetic:
lower wall `4!·(2·31) = 1488 ≤ 7⁴ = 2401`; upper wall `10⁴ = 10000 < 4!·31² = 23064`;
smallness `2⁻¹²⁸·(31·30²) ≤ 1`.  So `mcaDeltaStar ≤ 3/5` fires from the entropy gate
theorem — the same in-window point as `mcaDeltaStar_F31_window`, reached through the
binomial-tail walls. -/
theorem mcaDeltaStar_F31_entropy_gate (dom : Fin 10 ↪ ZMod 31) :
    mcaDeltaStar (F := ZMod 31) (A := ZMod 31)
        ((rsCode dom 2 : Submodule (ZMod 31) (Fin 10 → ZMod 31)) :
          Set (Fin 10 → ZMod 31)) ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ (3 / 5 : ℝ≥0) := by
  have hcard : Fintype.card (ZMod 31) = 31 := by simp [ZMod.card]
  refine mcaDeltaStar_le_of_entropy_gate (m := 1) dom (by norm_num) ?_
    ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ (by simp) ?_ ?_ ?_
  · -- hhi : (1 − 3/5)·10 ≤ 4
    have hle : (3 : ℝ≥0) / 5 ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
    rw [Fintype.card_fin, ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hle]
    push_cast; norm_num
  · -- lower wall : 4!·(2·31^1) ≤ (10+1−4)^4 = 7^4
    rw [hcard]; norm_num [Nat.factorial]
  · -- upper wall : 10^4 < 4!·31^2
    rw [hcard]; norm_num [Nat.factorial]
  · -- smallness : 2^-128·(31·(C'+2)^2) ≤ 1 with C'+2 = 30
    rw [hcard]
    have hchoose : (2 + 1 + 1).choose (2 + 1) * (10 - (2 + 1)).choose 1 + 2 = 30 := by decide
    rw [hchoose]
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp), mul_one]
    norm_num

end ProximityGap.PairRank

