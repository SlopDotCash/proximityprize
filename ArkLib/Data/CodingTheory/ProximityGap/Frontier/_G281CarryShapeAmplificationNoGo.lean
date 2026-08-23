/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G281: a perfect Eulerian carry-shape theorem cannot reach the CORE gate (#466)

## Frontier context

G278 decomposed the sponsor covariance mass by integer carry and isolated the **lawful
antipodal / zero-carry floor** `L := J_r^{lawful}` as the only *unconditional* mass anchor, with the
remaining characteristic-`p` wraparound residual load-bearing.  G279 (Fable) then asked the tempting
follow-up: could a rigorous **Eulerian carry-shape** theorem — an equidistribution statement bounding
the zero-carry slab share `J_0 ≤ π_{r,0}·J` for the exact Eulerian zero-carry probability
`π_{r,0}` (`π_{5,0} = 0.393925…`, `π_{6,0} = 0.365370…`) — *amplify* the lawful floor into the
production positivity gate `J ≥ B_r/p`?

The two available hypotheses are exactly

```text
H_floor : J_0 ≥ L            (G278, proved: the lawful antipodal floor)
H_shape : J_0 ≤ π_{r,0}·J    (the useful direction of a perfect Eulerian slab theorem, ε = 0)
```

Chaining them gives the strongest possible amplified lower bound on the total mass,

```text
J ≥ L / π_{r,0}.
```

This file proves, in exact integer/rational arithmetic, that **even this best-possible amplified
floor still undershoots the gate** `B_r/p` at both sponsor ranks `r = 5, 6` and both sponsor primes
`P1, P2` (`n = 2^30`, `P1 = n(2^128+192)+1`, `P2 = n(2^129+13)+1`).  Concretely the amplified floor
misses by factors `271×`–`543×` at rank five and `>2·10^{10}×` at rank six.  Hence **no** carry-shape
/ slab-equidistribution theorem, however sharp, is a positivity mechanism.

## Why this is genuinely new (deconfliction)

This is orthogonal to the landed neighbours:
- **G278** decomposes the carry and proves the *floor* `J_0 ≥ L`; it does **not** address whether
  shaping the total mass by the Eulerian law suffices.  G281 quantifies exactly that sufficiency and
  refutes it.
- **G280** pins the surviving certificate's *shape* (odd real-sign alignment; every even/PSD
  certificate is polarity-blind).  That is a shape no-go on the *sign* mechanism; G281 is a
  *magnitude* no-go on the *carry-shape amplification* mechanism.  A carry-shape bound is
  polarity-invariant (it constrains `|J_0|`-style slab proportions), so it is orthogonal to G280 and
  killed here on size grounds, not sign grounds.

## The mechanism, made kernel-checkable

`H_shape` only ever bounds the *normalized* slab proportion `J_0/J`; it carries **no** information
about the absolute total mass `J` whose excess over `B_r/p` is the gate.  The best it yields with
`H_floor` is `J ≥ L/π_{r,0}`.  Writing `π_{r,0} = num/den` with `num/den` a safe rational **lower
bound** on the exact Eulerian probability (`393/1000 ≤ π_{5,0} = 0.393925…`, `365/1000 ≤ π_{6,0} =
0.365370…`), the amplified floor `L·den/num` is an **over-estimate** of the true floor `L/π_{r,0}`
(a *smaller* `π` gives a *larger* `L/π`), so if even this over-estimate misses the gate then the
true floor does too.  The over-estimate `L·den/num` fails to reach the gate `B_r/p` exactly when

```text
L · den / num  <  B_r / p        ⟺        L · p · den  <  B_r · num.
```

The four recorded sponsor cells satisfy this exact integer inequality.  `365/1000` reduces so the
recorded `(num, den)` pairs are `(393, 1000)` at `r=5` and `(73, 200)` at `r=6`.

## Honest scope

Abstract statement + four exact recorded certificates.  This is a magnitude no-go that retires
carry-shape / slab-equidistribution as a certification route (it survives only as *calibration*, per
G278).  It does **not** bound `B` at production primes and is **not** prize closure.  The surviving
admissible route is unchanged: an **absolute**, sponsor-specific, signed full-family Jacobi /
Gross–Koblitz correction proved directly against the row label — not a normalized carry-shape,
interval-discrepancy, or slab-proportion statement, all of which are refuted here on size.  CORE
remains **OPEN / ON-BGK**.

## Formal payload

- `amplified_floor_lt_gate` — the abstract engine, a genuine theorem: from the exact integer
  certificate `L·p·den < B·num` (with `0 < num`, `0 < p`), the perfect-shape amplified floor
  `L·den/num` is `< B/p` as rationals.
- `amplified_floor_undershoots` — the packaged integer consumer: from the certificate,
  the amplified-floor mass `Jmin := den·L/num` (the largest total mass forced by `H_floor` +
  `H_shape`) satisfies `p · (den · L) < num · B`, i.e. `p·Jmin < B`; so the best carry-shape-amplified
  mass provably falls short of the gate `B/p`.  Hence carry shape + the lawful floor cannot certify
  `p·J ≥ B`.
- Four `decide` certificates `L·p·den < B·num` at `(P1,P2) × (r=5,6)` from the exact probe.
-/

set_option linter.style.longLine false


set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G281

/-! ### The abstract carry-shape amplification no-go (genuine theorems) -/

/-- **Amplified-floor engine.**  Suppose the exact integer certificate `L·p·den < B·num` holds with
`0 < num` and `0 < p`.  Then the amplified-floor over-estimate `L·den/num` is strictly below the
production gate `B/p`, as rationals.  With `num/den` a **lower** bound on the exact Eulerian
probability `π_{r,0}`, we have `L·den/num = L/(num/den) ≥ L/π_{r,0}`, so this over-estimate dominates
the true perfect-shape amplified floor `L/π_{r,0}`; hence `L/π_{r,0} ≤ L·den/num < B/p` and the true
floor undershoots the gate too.  This is the whole content of G279: shaping cannot reach the gate. -/
theorem amplified_floor_lt_gate (L p B num den : ℤ)
    (hnum : 0 < num) (hp : 0 < p)
    (hcert : L * p * den < B * num) :
    (L * den : ℚ) / num < (B : ℚ) / p := by
  have hnum' : (0 : ℚ) < num := by exact_mod_cast hnum
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  rw [div_lt_div_iff₀ hnum' hp']
  have hint : (L * den * p : ℤ) < B * num := by nlinarith [hcert]
  have : ((L * den * p : ℤ) : ℚ) < ((B * num : ℤ) : ℚ) := by exact_mod_cast hint
  push_cast at this ⊢
  linarith

/-- **Carry-shape insufficiency (packaged integer consumer).**  Fix the gate integers
`L, p, B, num, den` with the exact certificate `L·p·den < B·num`, where `num/den` is a **lower** bound
on the exact Eulerian probability `π_{r,0}`.  The true perfect-shape amplified floor `L/π_{r,0}`
satisfies `π_{r,0} · (L/π_{r,0}) = L`, and `num/den ≤ π_{r,0}` gives the integer over-estimate
`den·L / num ≥ L/π_{r,0}`.  This theorem certifies that even the over-estimate, gated by `p`,
undershoots the gate mass `B`:

```text
p · (den · L)  <  num · B,
```

i.e. `p·(den·L/num) < B` so the over-estimate mass `den·L/num < B/p`; a fortiori the true amplified
floor `L/π_{r,0} ≤ den·L/num < B/p`.  Hence carry shape plus the lawful floor is quantitatively
insufficient to certify `J ≥ B/p`.  (Pure reassociation of `L·p·den < B·num`.) -/
theorem amplified_floor_undershoots (L p B num den : ℤ)
    (hcert : L * p * den < B * num) :
    p * (den * L) < num * B := by
  linarith [hcert, (by ring : p * (den * L) = L * p * den), (by ring : num * B = B * num)]

/-! ### Recorded sponsor certificates (exact integers, `decide`)

Sponsor cells: `n = 2^30`, `P1 = n(2^128+192)+1`, `P2 = n(2^129+13)+1`.
`L = J_r^{lawful}` is the exact lawful antipodal floor (G278 closed form),
`B = n^2 · C(n,r) · C(n,r-1)` is the covariance mass (gate `J ≥ B/p`), and
`(num, den)` is a safe rational **lower** bound on the exact Eulerian zero-carry probability
`π_{r,0}` (`(393, 1000) ≤ π_{5,0}`, `(73, 200) ≤ π_{6,0}`), so `L·den/num ≥ L/π_{r,0}` over-estimates
the true floor.  Each theorem certifies `L·p·den < B·num`, i.e. even the over-estimate `L·den/num`
undershoots the gate `B/p`; a fortiori the true amplified floor `L/π_{r,0}` does.
Probe of record: `scripts/probes/g281_carry_shape_amplification_nogo.py`. -/

/-- Sponsor gate-certificate cell. -/
structure Cert where
  L : ℤ
  p : ℤ
  B : ℤ
  num : ℤ
  den : ℤ

/-- The exact amplification certificate `L·p·den < B·num` for a cell:
the perfect Eulerian carry-shape amplified floor `L·den/num` is strictly below the gate `B/p`. -/
def CertHolds (c : Cert) : Prop := c.L * c.p * c.den < c.B * c.num

instance (c : Cert) : Decidable (CertHolds c) := by unfold CertHolds; infer_instance

/-- `P1 = 2^30(2^128+192)+1`, `r = 5`.  `393/1000 ≤ π_{5,0}`. -/
def certP1r5 : Cert :=
  { L := 1509017068118057542686618908588550028630425600,
    p := 365375409332725729550921208179070755120141565953,
    B := 759462045899457119485176642115271220979527108996409881324408340022138203322385625838453746827264,
    num := 393, den := 1000 }

/-- `P1`, `r = 6`.  `73/200 ≤ π_{6,0}`. -/
def certP1r6 : Cert :=
  { L := 687228452827503190486247830024011584625525962808754176,
    p := 365375409332725729550921208179070755120141565953,
    B := 29186670577033364476825465271713505708441110742207015751025556257695231755481263381784249138256812583688658223104,
    num := 73, den := 200 }

/-- `P2 = 2^30(2^129+13)+1`, `r = 5`.  `393/1000 ≤ π_{5,0}`. -/
def certP2r5 : Cert :=
  { L := 1509017068118057542686618908588550028630425600,
    p := 730750818665451459101842416358141509841924915201,
    B := 759462045899457119485176642115271220979527108996409881324408340022138203322385625838453746827264,
    num := 393, den := 1000 }

/-- `P2`, `r = 6`.  `73/200 ≤ π_{6,0}`. -/
def certP2r6 : Cert :=
  { L := 687228452827503190486247830024011584625525962808754176,
    p := 730750818665451459101842416358141509841924915201,
    B := 29186670577033364476825465271713505708441110742207015751025556257695231755481263381784249138256812583688658223104,
    num := 73, den := 200 }

/-- `P1`, `r = 5`: amplified floor undershoots the gate (`541×`). -/
theorem cert_P1r5 : CertHolds certP1r5 := by decide

/-- `P1`, `r = 6`: amplified floor undershoots the gate (`>4·10^{10}×`). -/
theorem cert_P1r6 : CertHolds certP1r6 := by decide

/-- `P2`, `r = 5`: amplified floor undershoots the gate (`271×`). -/
theorem cert_P2r5 : CertHolds certP2r5 := by decide

/-- `P2`, `r = 6`: amplified floor undershoots the gate (`>2·10^{10}×`). -/
theorem cert_P2r6 : CertHolds certP2r6 := by decide

/-- **Packaged G281 no-go.**  At every sponsor cell the exact certificate `CertHolds` holds, hence
(feeding each into `amplified_floor_undershoots`) the perfect-shape amplified floor `den·L` scaled by
the gate obeys `p·(den·L) < num·B`: carry-shape amplification is quantitatively insufficient at both
ranks and both sponsor primes.  CORE OPEN / ON-BGK. -/
theorem g281_carry_shape_insufficient_all :
    CertHolds certP1r5 ∧ CertHolds certP1r6 ∧ CertHolds certP2r5 ∧ CertHolds certP2r6 :=
  ⟨cert_P1r5, cert_P1r6, cert_P2r5, cert_P2r6⟩

end ArkLib.ProximityGap.Frontier.G281
