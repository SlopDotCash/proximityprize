# δ* / #466 — SYZ59: the empty middle, with the SYZ55⇄SYZ47 convention reconciled

Date: 2026-07-11
File: `ArkLib/Research/ProximityGap/Frontier/_SYZ59EmptyMiddle.lean`
Probe: `scripts/probes/probe_syz59_empty_middle.py`
Status: axiom-clean (propext / Classical.choice / Quot.sound only; no `sorryAx`). CORE OPEN / ON-BGK.

## The task

"Empty middle": no realizable band triple has a minimal syzygy strictly between the SYZ47 floor and
near-balance. The brief flagged an apparent contradiction — SYZ55's census says realizable witnesses
have `δ₁ = 0`, but SYZ47's floor says `δ₁ ≥ max(a,b,c) > 0`. Reconcile first, then land what is
provable.

## Convention reconciliation (the load-bearing finding)

There are **two** degree conventions for the minimal syzygy of a pairwise-coprime band triple
`(W_AB, W_AC, W_BC)`, reduced degrees `(a,b,c)`, `S := a+b+c`:

- **PRODUCT-degree** (SYZ44 degree-sum law, SYZ45 `imbalance`, SYZ47 floor): `δᵢ = max slot
  product-degree = max_slot deg(W_slot · s_slot)`, with `δ₁+δ₂ = S` and floor `δ₁ ≥ max(a,b,c)`.
- **COFACTOR-degree** (SYZ55 *prose*): `δᵢ = deg` of the cofactor vector `s`.

A **constant** syzygy `c₀W_AB + c₁W_AC + c₂W_BC = 0` of a balanced triple (`a=b=c=d`) has

- cofactor degree `0` (cofactors are the field constants `C cᵢ`) — SYZ55's "`δ₁ = 0`", and
- product-degree `d = max(a,b,c)` (a nonzero scalar preserves degree) — SYZ47's floor **attained**.

Bridge: **`product_δ₁ = cofactor_δ₁ + max(a,b,c)`**. So SYZ55 and SYZ47 describe the *same* witness;
the floor is **tight**, not violated. The SYZ45 `(4,4,4)⇒ι=2` "refutation" is exactly this
attainment: `δ₁ = 4 = max`, `ι = ⌊12/2⌋ − 4 = 2`. The probe verifies both readings by exact linear
algebra over `𝔽₁₃`/`𝔽₁₀₁` (`product_δ₁ = 4`, `cofactor_δ₁ = 0` on `f = 3g − 2h` witnesses).

Cleaned target (product convention): the SYZ55 census "all realizable witnesses have `δ₁ = 0`
(cofactor)" is **"all realizable witnesses have `δ₁ = max(a,b,c)` (product) — floor attained"**. Empty
middle = *no realizable triple has `max(a,b,c) < δ₁ ≤ ⌊S/2⌋ − 2`*.

## What is proved (axiom-clean)

- §1 **Convention bridge**: `const_syzygy_cofactor_degree_zero`, `const_slot_product_degree_eq`
  (`natDegree_C_mul`), `const_syzygy_product_degree_eq_max` (leading slot attains `d`, all slots
  `≤ d`).  (The former `ℕ` "bridge" `convention_bridge` was the identity `h ↦ h` and was removed.)
- §2 **Empty-middle dichotomy** (pure `ℕ`): `no_middle_iff_dichotomy` — under the floor + degree-sum
  law, *not in the middle band* ⟺ `δ₁ = max ∨ δ₁ ≥ ⌊S/2⌋ − 1`; the near-balance branch feeds
  `ι ≤ 1` (`near_balance_imbalance_le_one`); `empty_middle_dichotomy` packages it.
- §3 **Hand-entered constant-syzygy examples** (renamed from the former "`n ≤ 20` census"
  `productCensus` / `realizable_floor_attained` / `realizable_no_middle`):
  `constSyzygyExamples` lists `(d,d,d,δ₁ = d)` for `d ∈ {3,4,5}` with `δ₁` typed equal to `max`, so
  `constSyzygyExamples_floor_attained` / `constSyzygyExamples_no_middle` are true by construction and
  are not a census of realizable triples; `(3,3,3)` is not balanced-interior.
- §4 **General status / residual**: `general_empty_middle_from_geometry` (interface: given the
  geometric no-middle residual, the dichotomy follows).  The former `wronskian_no_jump` skeleton
  (hypotheses forcing `dᵢ = dⱼ = max`) was removed; the Wronskian route is recorded as not closing
  the gap in prose only.

**Correction (SYZ71).** The empty middle is contradicted at `n = 20`: SYZ71's band-realizable
`μ₂₀ ⊂ 𝔽₄₁` probe witness (`P = (29+10X)W_AC + (30+X)W_BC`, `deg P = 7`, rank 3, no constant
syzygy) occupies `middleBand 6 6 6 7`.  The claims below about an "`n ≤ 20` census" are superseded.

## General-proof status: OPEN

The general empty middle = SYZ45's geometric residual "no realizable *non-constant* low-degree
dependence", which SYZ45 proved is **not** an algebraic identity (needs band realizability). SYZ59
does not close it; the Wronskian/μ-exchange attack is recorded as blocked (§4). The landable content
is the convention bridge (removes the SYZ55/SYZ47 apparent contradiction) + the `n ≤ 20` finite
census in the reconciled convention. Rate-½ `uniformSylvester` still consumes `ι ≤ 1`; CORE remains
OPEN / ON-BGK.
