/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# G285: low-order kernel-domain characters do not carry the CORE sign (#466)

Write the weighted relation row as

```text
W_G(t) = sum_{u in G} 1_{(2-u)G}(t).
```

For the adjacent-rank row `R_r`, let `H_j` be its mass on `(2-zeta^j)G`, with multiplicity at
zero. Then the exact CORE gate and the first two canonical real Fourier normals on the *kernel
input* `u=zeta^j` are

```text
A_r = p * sum_j H_j - n^2 * total,
K_2 = p * sum_j (-1)^j H_j,
K_4 = p * sum_j cos(pi*j/2) H_j.
```

Unlike the carry Ramanujan normals closed by G282, these are row-labelled through `u -> (2-u)G`.
They are invariant under inversion of the subgroup generator: the order-two character is
unique, and the real part of the order-four pair is fixed by conjugation.

Exact genuine subgroup cells refute both possible one-sided transfers. At `(n,p,r)=(16,97,5)`,
`K_2,K_4>0` while `A_5<0`; at `(16,113,5)`, both normals are negative while `A_5>0`.
At the injective-kernel cell `p=2593`, both normals remain positive while the CORE gate changes from
positive at rank five to negative at rank six. Thus neither low-order kernel character supplies the
predeclared odd separator sought after G280/G284, separately or jointly across the two live ranks.

The accompanying exact-integer probe derives each `H_j` from the canonical subgroup and verifies
`W_G`'s class decomposition before computing 96 rank-cells. The literature interpretation is a
G228 quotient-Jacobi fanout twisted by the input character. Extending that character to `F_p^*`
writes each kernel normal as a full average of `m=(p-1)/n` Jacobi sums. Weil controls every term by
`sqrt p`, but supplies no comparison between this twisted character coset and the untwisted CORE
factor. G233 already bars bounded-mass reconstruction of the untwisted factor. A transfer from the
twisted average would instead require a new full-family cross-coset phase correlation. The new
coordinate system therefore does not weaken the binding inequality.

This is a certificate-shape no-go, not a sponsor covariance estimate. CORE remains open / on-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G285KernelDomainCharacterNoGo

/-- Alternating sum, the unique real order-two character on a dyadic kernel input. -/
def alternatingSum : List ℤ -> ℤ
  | [] => 0
  | x :: xs => x - alternatingSum xs

/-- Real part of the order-four character, with weights `(1,0,-1,0)` on each block. -/
def quarterTurnSum : List ℤ -> ℤ
  | a :: _b :: c :: _d :: xs => a - c + quarterTurnSum xs
  | _ => 0

/-- The centered CORE gate derived from the row-class masses. -/
def kernelGate (p n total : ℤ) (H : List ℤ) : ℤ :=
  p * H.sum - n ^ 2 * total

/-- The order-two kernel-character normal. -/
def orderTwoNormal (p : ℤ) (H : List ℤ) : ℤ := p * alternatingSum H

/-- The real order-four kernel-character normal. -/
def orderFourRealNormal (p : ℤ) (H : List ℤ) : ℤ := p * quarterTurnSum H

/-- Exact row-class masses at `(n,p,r)=(16,97,5)`. -/
def h97 : List ℤ :=
  [1341248, 1295776, 1295776, 1295776, 1299712, 1299712, 1295776, 1300000,
    1319120, 1300000, 1319120, 1316048, 1319120, 1319120, 1299712, 1300000]

/-- Exact row-class masses at `(n,p,r)=(16,113,5)`. -/
def h113 : List ℤ :=
  [1129312, 1125808, 1125808, 1129312, 1123536, 1126624, 1126624, 1126624,
    1125648, 1129312, 1125424, 1129312, 1125648, 1123536, 1129312, 1123520]

/-- Exact rank-five row-class masses at the injective-kernel cell `(n,p)=(16,2593)`. -/
def h2593r5 : List ℤ :=
  [131184, 46736, 37968, 36592, 45152, 51120, 50720, 41824,
    31328, 45696, 48976, 51376, 50560, 35360, 36816, 52784]

/-- Exact rank-six row-class masses at the same injective-kernel cell. -/
def h2593r6 : List ℤ :=
  [448096, 211312, 179088, 172416, 205104, 224432, 221152, 192864,
    157744, 207696, 214176, 224368, 219920, 167264, 174384, 228048]

/-- Both predeclared low-order normals are positive while CORE is negative. -/
theorem positive_normals_negative_gate_97 :
    kernelGate 97 16 7949760 h97 = -6285008 ∧
      orderTwoNormal 97 h97 = 6125744 ∧
      orderFourRealNormal 97 h97 = 6675152 := by
  norm_num [kernelGate, orderTwoNormal, orderFourRealNormal, alternatingSum, quarterTurnSum, h97]

/-- Both normals are negative while CORE is positive, refuting the reverse sign transfer. -/
theorem negative_normals_positive_gate_113 :
    kernelGate 113 16 7949760 h113 = 1727120 ∧
      orderTwoNormal 113 h113 = -309168 ∧
      orderFourRealNormal 113 h113 = -341712 := by
  norm_num [kernelGate, orderTwoNormal, orderFourRealNormal, alternatingSum, quarterTurnSum, h113]

/-- At one injective-kernel prime, the CORE gate changes sign across the two live ranks while both
low-order kernel-character normals stay positive. -/
theorem injective_cell_adjacent_rank_sign_split :
    kernelGate 2593 16 7949760 h2593r5 = 24201296 ∧
      kernelGate 2593 16 34978944 h2593r6 = -13779712 ∧
      0 < orderTwoNormal 2593 h2593r5 ∧ 0 < orderTwoNormal 2593 h2593r6 ∧
      0 < orderFourRealNormal 2593 h2593r5 ∧
      0 < orderFourRealNormal 2593 h2593r6 := by
  norm_num [kernelGate, orderTwoNormal, orderFourRealNormal, alternatingSum, quarterTurnSum,
    h2593r5, h2593r6]

/-- Positivity of both canonical low-order kernel normals does not imply a nonnegative CORE gate. -/
theorem positive_low_order_normals_do_not_certify_core :
    ∃ (p n total : ℤ) (H : List ℤ),
      0 < orderTwoNormal p H ∧ 0 < orderFourRealNormal p H ∧ kernelGate p n total H < 0 := by
  refine ⟨97, 16, 7949760, h97, ?_⟩
  norm_num [positive_normals_negative_gate_97]

/-- Negativity of both normals does not force a negative CORE gate either. -/
theorem negative_low_order_normals_do_not_track_core :
    ∃ (p n total : ℤ) (H : List ℤ),
      orderTwoNormal p H < 0 ∧ orderFourRealNormal p H < 0 ∧ 0 < kernelGate p n total H := by
  refine ⟨113, 16, 7949760, h113, ?_⟩
  norm_num [negative_normals_positive_gate_113]

#print axioms positive_normals_negative_gate_97
#print axioms negative_normals_positive_gate_113
#print axioms injective_cell_adjacent_rank_sign_split
#print axioms positive_low_order_normals_do_not_certify_core
#print axioms negative_low_order_normals_do_not_track_core

end ArkLib.ProximityGap.Frontier.G285KernelDomainCharacterNoGo
