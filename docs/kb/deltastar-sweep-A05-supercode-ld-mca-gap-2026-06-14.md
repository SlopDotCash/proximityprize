# sweep A05 — super-code list bridge: LD/MCA gap, measured (2026-06-14)

**Actionable A05** (merged 407-T11 / 389-T02): re-land the super-code list-size bridge unifying
both grand challenges, and attach the probe confirming the `δ*_LD < δ*_MCA` gap (`>24x` at
`μ_16, a=4`).

## State found (collision check)

- The bridge `explainableScalars_card_le_superList` is **already landed and axiom-clean in-tree**
  at `ArkLib/Data/CodingTheory/ProximityGap/SuperCodeListBridge.lean` (NOT in `Frontier/` as the
  A05 spec assumed — a parallel worker landed it at the cone root). `lake env lean` axiom audit:
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. (Only a harmless unused-section-var
  linter warning for `[Nonempty ι]`.)
- The C048 connection entry (`RESEARCH_SYNTHESIS_407_CONNECTIONS.md`) documents the unification:
  the dilation symmetry (`FarLineIncidenceEquivariance`) pins the worst `(dim+1)`-super-code to
  `RS[k+1]`, so the grand MCA challenge = the list-decoding grand challenge of `RS[k+1]`.
- The **missing** piece was the LD/MCA gap probe. Delivered here.

## The bridge (proven object)

For any linear `C` and far direction `u₁ ∉ C`,
`I(u₀,u₁; δ) = #{γ : line u₀+γ·u₁ (1−δ)n-agrees with some c∈C}  ≤  |list(C⊕⟨u₁⟩, u₀, δn)|`
via the injection `γ ↦ c_γ − γ·u₁` (injective since `u₁∉C` makes the sum direct). For `RS[k]` on
`μ_n` the dilation-extremal far direction is `u₁ = X^k`, giving `C⁺ = RS[k+1]`.

## Probe: `scripts/probes/sweep_A05_ld_mca_supercode_gap.py`

EXACT arithmetic over `F_q`. Prize-shaped: `n=16=2^4`, `q=65537=2^16+1` (so `16 | q−1`, `q ~ n^4`,
`a=log_n q = 4`), rate `ρ`, super-code `RS[k+1]`, far direction `X^k`. The far-line incidence `I`
is computed via the bridge (full `RS[k+1]` subset-interpolation list of `u₀`, then the recovered
`γ` = degree-`k` coefficient), scanning `u₀ = X^e` over the dilation-fundamental far family.

**Cross-check (rigor):** at `μ_8, k=2`, the bridge `I` matches a brute-force scan over **all** `q`
scalars `γ` exactly at every agreement (`a=3: 25=25`, `a=4: 9=9`, `a=5: 0=0`). The probe computes
the correct object.

## Results (`δ*_LD` = Johnson unique-decoding radius of `RS[k+1]`; `δ*_MCA` = radius where worst
far-line incidence drops to `≤1`)

| instance | `δ*_LD` | `δ*_MCA` | threshold gap | mid-window `I` / Johnson-guarantee |
|---|---|---|---|---|
| `μ_16, ρ=1/4, a=4` | 0.1250 | 0.4375 | **+0.3125** (5 levels) | `a=6 (δ=.625): I=89` vs 1 → **89×** (super-list 186×) |
| `μ_16, ρ=1/2, a=4` | 0.0000 | 0.1875 | +0.1875 (3 levels) | `a=10 (δ=.375): I=40` vs 1 → 40× |
| `μ_8,  ρ=1/4`       | 0.1250 | 0.3750 | +0.2500 (2 levels) | `a=3 (δ=.625): I=40` vs 1 → 40× |

Window-interior incidence ladder at `μ_16, ρ=1/4` (the prize window `δ∈(0.5,0.75)`): `a=7 (δ=.56):
I=9`, `a=6 (δ=.625): I=89`, `a=5 (δ=.688): I=3664`. (The `a=5` value is the degenerate
low-radius regime where nearly the full `C(16,5)=4368` list trivially agrees — NOT used for the
headline; the structural beyond-Johnson super-linear point is `a=6: I=89 = 5.6·n`.)

## Verdict (honest)

**PARTIAL — the gap is real and `>24×`, but it is not a closure; it sharpens the open list-form.**

1. The LD/MCA gap is decisive and `>24×`: at the prize instance `μ_16, ρ=1/4, a=4`, the
   mid-window (`δ=0.625`) far-line incidence is `89` while the Johnson (=LD) bound certifies a
   singleton (`1`) — an `89×` list-size gap (super-list `186×`), and a `+0.3125` absolute
   threshold gap (`δ*_MCA = 0.4375` vs `δ*_LD = 0.1250`).
2. **The deeper structural fact** (the honest takeaway): in the entire prize window the Johnson
   list cap is **vacuous** (`a² − n·b ≤ 0`), i.e. the radius is beyond the Johnson radius
   everywhere the MCA incidence is nonzero. So "`LD < MCA`" is not a `24×` quantitative loss — it
   is a **qualitative** one: the LD/Johnson guarantee gives **no bound at all** in the window where
   `δ*` lives. Closing the prize via the bridge therefore requires a **beyond-Johnson list bound
   for `RS[k+1]`** — exactly the open list-form (`B4`, `δ*` core), not anything Johnson supplies.
3. The bridge **does** correctly unify the two grand challenges (MCA ⟶ `RS[k+1]` list-decoding),
   and the probe confirms the reduction is faithful (exact match to brute force). What stays open
   is unchanged: the worst-case beyond-Johnson list size of explicit smooth `RS[k+1]` in the
   window — the same wall as the `B`-form Gauss-period / Paley-eigenvalue input.

## Artifacts
- Lean (already in-tree, re-verified axiom-clean):
  `ArkLib/Data/CodingTheory/ProximityGap/SuperCodeListBridge.lean`
- Probe (new): `scripts/probes/sweep_A05_ld_mca_supercode_gap.py`
- This note: `docs/kb/deltastar-sweep-A05-supercode-ld-mca-gap-2026-06-14.md`
