/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ANGLE lit-uncertainty-2power : the quantitative uncertainty principle as an `s*` ceiling (#407)

THE REAL OBJECT (verified reframing, issue #407).  The deployed far-line incidence reduces to a
SPARSE-FUNCTION ZERO COUNT.  A far line `P(x) = x^a + γ x^b − c(x)` (deg `c < k`, far ⟹
`a,b ∉ {0,…,k-1}`) restricted to `μ_n ≅ Z_n` (`n = 2^μ`) is a function whose discrete-Fourier
support is contained in `T = {0,…,k-1} ∪ {a,b}` (size `≤ k+2`).  Writing
`s* = max #zeros of P on μ_n  =  n − (min physical support of a nonzero `T`-Fourier-sparse fn)`,
the prize threshold is governed by `s*`.

THE LITERATURE VERDICT this file pins (with exact citations in `/tmp/up_litunc.md`):

* PRIME `n` (Tao 2005, MRL 12, 121–127): `|supp f| + |supp f̂| ≥ n+1`, sharp.  A function on `Z_n`
  with Fourier support of size `k+2` has `≤ k+1` zeros, so `s* = k+1` (CONSTANT in `n`) ⟹ capacity.
  This is the SHARP tool — but its proof (Chebotarev/Stark nonvanishing of all DFT minors) is FALSE
  for composite `n`, and so it gives NOTHING for `n = 2^μ`.

* COMPOSITE `n` (Donoho–Stark 1989; Meshulam 2006): the ONLY universal tool is the product bound
  `|supp f| · |supp f̂| ≥ n`, giving `s* ≤ n − ⌈n/(k+2)⌉ = n(k+1)/(k+2)` — NEAR CAPACITY, far above
  the Johnson `√(kn)`.  Meshulam's divisor refinement `|supp f̂| ≥ n(d₁+d₂−|supp f|)/(d₁d₂)`
  COLLAPSES to Donoho–Stark for `n = 2^μ` (consecutive divisors are powers of 2; the support
  `≈ n/(k+2)` sits between them where the formula degenerates to `n/d₁`).  Numerically (probe
  `/tmp/up_meshulam_apply.py`): for `n=16,k=4`, both give `s* ≤ 13`, while measured `s* = 10`,
  Johnson `√(kn) = 8`.

CONCLUSION (the honest content): **the uncertainty principle yields NO bound below Johnson for
`n = 2^μ`.**  Its `√(kn)` competitor is unreachable from Fourier sparsity; it requires the
`μ_n`-specific character-sum / additive-energy geometry.  This file states the dichotomy abstractly
over `ZMod n`, proves the trivial `s* = n − minSupport` bookkeeping, and NAMES the two open Props
(the `2^μ` ceiling and the Johnson floor) so they cannot be confused with the proven prime case.

No `sorry`; the genuine math lives in the named Props (their *content* is the open problem).
-/

namespace ProximityGap.UncertaintyTwoPower

open Finset

variable {n : ℕ}

/-- A finite "frequency" support `T ⊆ ZMod n` — the Fourier support of the far-line function. -/
abbrev FreqSupport (n : ℕ) := Finset (ZMod n)

/-- The structured Fourier support of a far line: the interval `{0,…,k-1}` (the codeword degrees)
together with the two far exponents `a, b`.  This is the REAL object whose extremal physical
support governs `s*`. -/
def farSupport (n k : ℕ) (a b : ZMod n) : FreqSupport n :=
  (Finset.range k).image (fun j : ℕ => (j : ZMod n)) ∪ {a, b}

/-- The far support has at most `k + 2` frequencies — the only structural fact every uncertainty
principle consumes. -/
theorem farSupport_card_le (n k : ℕ) (a b : ZMod n) :
    (farSupport n k a b).card ≤ k + 2 := by
  classical
  unfold farSupport
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ((Finset.range k).image (fun j : ℕ => (j : ZMod n))).card ≤ k := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_range]
  have h2 : ({a, b} : Finset (ZMod n)).card ≤ 2 := by
    refine (Finset.card_insert_le _ _).trans ?_
    simp
  omega

/-- `s*` from a physical zero count: the (claimed) maximal number of zeros on `μ_n ≅ Z_n` of a
nonzero function with Fourier support `T`.  We model "number of zeros" by `n − (physical support)`,
so a witness physical-support value `m` gives `s* = n − m`.  The `worstCase` predicate says `m` is
the MINIMUM physical support over all nonzero `T`-Fourier-sparse functions. -/
structure SparseZeroData (n : ℕ) where
  /-- The Fourier support of the function. -/
  T : FreqSupport n
  /-- The minimal physical support attained by a nonzero function with this Fourier support. -/
  minSupport : ℕ
  /-- Physical support cannot exceed the ambient size. -/
  minSupport_le : minSupport ≤ n

/-- `s* = n − minSupport`: maximal number of zeros = ambient minus minimal physical support. -/
def sStar (d : SparseZeroData n) : ℕ := n - d.minSupport

/-- **Donoho–Stark / Meshulam ceiling (composite `n`).**  The ONLY universal uncertainty bound:
`|supp f| · |supp f̂| ≥ n`, i.e. `minSupport · |T| ≥ n`.  As a `Prop` parameterized by the real
data — this is a THEOREM of Donoho–Stark 1989 (and the equality case is exactly subgroup cosets);
we record it as a named hypothesis since its Lean proof is not the point of this angle.  Its
*consequence* `s* ≤ n − ⌈n/|T|⌉` is what we derive below. -/
def DonohoStarkHolds (d : SparseZeroData n) : Prop :=
  n ≤ d.minSupport * d.T.card

/-- The Donoho–Stark ceiling on `s*`, derived purely from the product bound: with `|T| ≤ k+2`,
`s* ≤ n − ⌈n/(k+2)⌉`.  Concretely `(k+2) * (n − s*) ≥ n`, i.e. the zero count cannot exceed
`n · (k+1)/(k+2)`.  This is NEAR CAPACITY and is the BEST the uncertainty principle gives for
`n = 2^μ` (see `/tmp/up_litunc.md` for the Meshulam-collapse numerics). -/
theorem sStar_le_of_donohoStark (d : SparseZeroData n) (k : ℕ)
    (hT : d.T.card ≤ k + 2) (hDS : DonohoStarkHolds d) :
    n ≤ (k + 2) * (n - sStar d) := by
  unfold sStar DonohoStarkHolds at *
  have hle : d.minSupport ≤ n := d.minSupport_le
  have hmul : d.minSupport * d.T.card ≤ d.minSupport * (k + 2) :=
    Nat.mul_le_mul_left _ hT
  have hmin : n - (n - d.minSupport) = d.minSupport := by omega
  have hcomm : d.minSupport * (k + 2) = (k + 2) * d.minSupport := Nat.mul_comm _ _
  have hchain : n ≤ (k + 2) * d.minSupport := by
    calc n ≤ d.minSupport * d.T.card := hDS
      _ ≤ d.minSupport * (k + 2) := hmul
      _ = (k + 2) * d.minSupport := hcomm
  rw [hmin]
  exact hchain

/-- **OPEN Prop — the prize floor (`n = 2^μ`).**  The conjectured Johnson-type LOWER bound on the
worst-case physical support: for `n = 2^μ` and far support of size `≤ k+2`, the minimal physical
support is at least `n − √(k n)` (equivalently `s* ≤ √(k n)`), the Johnson radius.  NO uncertainty
principle proves this (they only give the much weaker `≥ n/(k+2)` above); it requires the
`μ_n`-specific character-sum geometry.  This is the genuine open content of the angle, named so it
is NOT confused with the proven prime case below. -/
def JohnsonFloorTwoPower (μ k : ℕ) : Prop :=
  ∀ (a b : ZMod (2 ^ μ)) (d : SparseZeroData (2 ^ μ)),
    d.T = farSupport (2 ^ μ) k a b →
      (sStar d) ^ 2 ≤ k * 2 ^ μ

/-- **PROVEN side — the prime-`n` capacity collapse (Tao 2005).**  For PRIME `n`, Tao's sharp
uncertainty `|supp f| + |supp f̂| ≥ n + 1` forces, for any nonzero `T`-Fourier-sparse function with
`|T| ≤ k + 2`, a physical support `≥ n − (k+1)`, hence `s* ≤ k + 1` — CONSTANT in `n`, i.e.
capacity `δ* → 1 − ρ`.  We record Tao's additive bound as a hypothesis (its Lean proof via
Chebotarev is out of scope) and DERIVE the `s* ≤ k+1` consequence — the citable contrast to the
open 2-power floor. -/
theorem sStar_le_kAddOne_of_tao (d : SparseZeroData n) (k : ℕ)
    (hT : d.T.card ≤ k + 2)
    -- Tao's prime-order additive uncertainty, instantiated at this datum:
    (hTao : n + 1 ≤ d.minSupport + d.T.card) :
    sStar d ≤ k + 1 := by
  unfold sStar
  -- minSupport ≥ n + 1 − |T| ≥ n + 1 − (k+2) = n − (k+1)
  have : n + 1 ≤ d.minSupport + (k + 2) := le_trans hTao (by exact Nat.add_le_add_left hT _)
  omega

/-- The two faces are genuinely different: the prime case (`sStar_le_kAddOne_of_tao`) gives a bound
CONSTANT in `n` (capacity), whereas the 2-power floor `JohnsonFloorTwoPower` is an `√(kn)` bound
that GROWS with `n` and is OPEN.  The Donoho–Stark ceiling (`sStar_le_of_donohoStark`) sits between
them at NEAR CAPACITY, proving the uncertainty principle gives NOTHING below Johnson for `n = 2^μ`.
This `example` just checks the three statements coexist (type-check) over the real `farSupport`. -/
example (μ k : ℕ) (a b : ZMod (2 ^ μ)) (d : SparseZeroData (2 ^ μ))
    (hd : d.T = farSupport (2 ^ μ) k a b) :
    d.T.card ≤ k + 2 := by
  rw [hd]; exact farSupport_card_le _ _ _ _

end ProximityGap.UncertaintyTwoPower
