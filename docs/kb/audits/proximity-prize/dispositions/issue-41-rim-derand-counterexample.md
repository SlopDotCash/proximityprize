STATUS: CLOSED — RIM/AGL24 derandomization counterexample fully formalized in-tree; audit found only stale theorem-name references in two docstrings, now corrected.

# issue-41 — Formalize the RIM/AGL24 derandomization counterexample

Tracking issue: lalalune/ArkLib#41
Files:
* `ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRefutation.lean`
* `ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRIMRank.lean`
* `Research/ProximityPrize/PermanentlyBlocked.lean` (dead-route index)
* `ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDThreshold.lean` (Grand LD link)

## Finding

The issue asked for four things. On audit, all four are settled in the tree (the heavy
lifting landed in `7975db16` and `a039ca1c`); the only genuine defects were stale
docstring references to pre-rename theorem names, now fixed.

### 1. Concrete rank-deficient RIM instance — DONE

`MuTwoPowDerandRefutation.badHypergraph : Fin 8 → Finset (Fin 3)` is the ±-pair
hypergraph `[(0,1),(0,2),(1,2),∅,(0,1),(0,2),(1,2),∅]` from the research note, with
`badHypergraph_kwpc : IsWeaklyPartitionConnected badHypergraph 3` (and
`badHypergraph_weight_tight : labelWeight badHypergraph id = 6` in the RIMRank file —
the instance is *minimal* 3-wpc). The explicit 6×6 reduced intersection matrix is
`rimMatrix`, with `badHypergraph_coord_eq` / `edgeFst_mem` / `edgeSnd_mem` discharging
(by `decide`) that its rows exhaust exactly the nonempty edges.

### 2. Determinant/rank drop over a concrete field — DONE

Generic form, over **every** field containing `ω` with `ω⁴ = -1` (every prize-legal
field):
* `rimMatrix_mulVec_eq_zero` — the explicit kernel vector `rimKernelVec` (nonzero by
  `rimKernelVec_ne_zero`) is annihilated;
* `rimMatrix_det_eq_zero` — determinant vanishes;
* `rimMatrix_rank_lt_six` (RIMRank) — **column-rank drop**, the exact form the
  AGL24/GZ capacity machinery consumes.

Concrete `F₁₇` certificate (`ω = 9`, of order 8), matching the mod-`p` search output:
`rimMatrix_zmod17_eq` (the fully numeric matrix), `rimKernelVec_zmod17_eq` (kernel
certificate `(5, 0, 14, 1, 0, 1)`), `rimMatrix_det_eq_zero_zmod17`, and
`rimMatrix_rank_lt_six_zmod17`.

### 3. Consequence: universal μ_{2^t} RIM full-rank target is false — DONE

* Certificate level: `not_kwpc_rigidity` (and `not_kwpc_rigidity_zmod17`) — a 3-wpc
  hypergraph with a nonzero degree-≤2 agreement certificate, killing the k-wpc rigidity
  statement the derandomization route needs.
* Matrix level: `rimMatrix_rank_drop` packages hypergraph + 3-wpc proof + singular RIM
  in one statement.
* Kernel ↔ certificate bridge: `rimMatrix_mulVec_eq_certDiff` (an identity in `ω`, no
  hypothesis) plus `rimKernelVec_poly₀`/`rimKernelVec_poly₁` discharge the prose claim
  that `rimMatrix` is *the* RIM of `badHypergraph` and the kernel vector *is* the
  certificate's coefficient vector — the formalization is not a disconnected matrix fact.
* Decoding-side corollary: `mu8_list_three` exhibits the induced 3-element list at the
  μ₈ smooth domain.

### 4. Grand LD doc links + CONJ-A/CONJ-3 supersession — DONE (with fixes)

* `GrandChallengeLDThreshold.lean` carries the "Dead route (do not revive)" paragraph
  pointing at the refutation modules and `PermanentlyBlocked`;
  `PermanentlyBlocked.lean` §"Smooth-domain AGL24 derandomization" is the dead-route
  index entry. Issue #40 (Grand LD value question) and #43 (permanently-blocked
  tracking) reference the same boundary.
* **Fixed in this audit:** both docstrings referenced pre-rename theorem names
  (`rim_rank_drop`, `rim_det_eq_zero`, `rim_rank_lt_six`); corrected to
  `rimMatrix_rank_drop`, `rimMatrix_det_eq_zero`, `rimMatrix_rank_lt_six` so the
  references resolve.
* The CONJ-A/CONJ-3 research notes named in the issue
  (`research/proximity-prize/conj3-proof/…`) do not exist in this repository or the
  parent workspace any longer; no greppable CONJ-A/CONJ-3 reference survives in-tree,
  so there is nothing left to mark superseded. The reproduction pointers live on in
  this disposition and the module docstrings.

## Verification

Both modules are `sorry`-free (grep). Proof surface is elementary: `decide` for the
finite hypergraph facts, `linear_combination`/`norm_num` for the `ω`-identities, explicit
kernel vector for the rank drop. Axiom audit is queued behind the shared v4.30.0-rc2
Mathlib rebuild (#34/#35) like every other module; the census tooling reads git HEAD, so
these files are in scope for the next #36 sweep.

## Regression check

```sh
grep -rn "rim_rank_drop\|rim_det_eq_zero\|rim_rank_lt_six" --include="*.lean" ArkLib | grep -v rimMatrix   # expect: no hits
grep -cn "sorry" ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRefutation.lean \
  ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRIMRank.lean                                          # expect: 0, 0
```
