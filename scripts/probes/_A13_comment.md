### [sweep][A13] Inverse-theorem unification: the ε*-bad family as a sumset object — PARTIAL

**Collision note.** A13 (merged 357-T12 / 334-T07) was attacked qualitatively earlier
(`wf407-T357-12-inverse-unification-bet.md`, REFUTED+WALLED). Per the collision protocol I
**verified + extended**: reproduced axis-1, then sharpened the weak link (axis-2 used a loose
`K = 1/ε*` proxy). A13's actual ask — *phrase the bad family as a sumset object and measure it* —
was never done. I did it, exactly.

**The sumset object, stated precisely.** For `RS[F_q,μ_n,k]`, direction `(u₀,u₁)`, radius `δ`,
the right object for an inverse theorem is the **bad-scalar set in the additive group**
`Bad(u₀,u₁) = { γ ∈ (F_q,+) : d(u₀+γ·u₁, C) ≤ δn }`, with `ε_mca = max |Bad|/q`. The prior pass
conflated this with the codeword *list* (lives in `F_q^{μ_n}`). B-R/Sanders need `Bad` to have
small doubling `K = |Bad+Bad|/|Bad|` (equiv. energy `E(Bad) ≥ |Bad|³/K^{o(1)}`).

**The constraint (in-tree, axiom-clean).** `MCAWitnessSpread.unique_bad_gamma_common_witness`:
for a FIXED witness coord-set `S`, at most ONE bad `γ`. ⟹ `L` bad scalars need `≥ L` distinct
witness sets; the bad scalars are coupled only through code geometry, never through an additive
relation in `(F_q,+)`. The geometry leaves `Bad`'s additive structure entirely free.

**The measurement (exact, `_wf357_a13_inverse.py`, window interior n=16, k=2, t=4):**

| p | \|Bad\| | density | K=\|Bad+Bad\|/\|Bad\| | E(Bad)/Sidon |
|---|---|---|---|---|
| 97  | 32 | 0.330 | 3.03 | 5.72 |
| 113 | 25 | 0.221 | 4.48 | 3.48 |
| 193 | 18 | 0.093 | 6.94 | **1.59** |

**New result — the thinness law.** As `p` grows with `n` fixed (toward the prize regime, where
`Bad` is ε*-thin), the doubling **grows** (3.0→4.5→6.9) and the Sidon-energy ratio **falls to 1**
(5.7→3.5→1.6): the binding bad set becomes **asymptotically Sidon** (every pairwise sum distinct,
zero additive structure). The moderate K at the smallest prime is a wrap-around artifact (`Bad`
was 1/3 of `F_p`). Witness-distinctness confirmed: `17/17, 27/27, 34/34` bad γ have distinct
witness sets, exactly `unique_bad_gamma_common_witness`.

**Verdict — the bet dies on its premise, now quantitatively.** At prize thinness
`|Bad|/q ≤ 2⁻¹²⁸` the law gives `K → |Bad|`, `E(Bad) → 2|Bad|² ≪ |Bad|³` ⟹ Sanders/Bloom–Sisask
return a "structure" of rank `≈ |Bad|`, i.e. no compression; covering count `exp(|Bad|)`,
super-poly in `1/ε*`. This is the SAME conclusion as the prior `K=1/ε*` proxy but via the correct
object and a measured law. The in-tree `MCAEigenstackOrbitLaw`/`SparseDeviationExtremality`
structure theorems govern the *ceiling* extremizer, not the binding maximizer (DISPROOF O161–O163);
they confirm the catalogue claim for the ceiling and are silent on the binding set, which §4 shows
is unstructured.

**Where it lands:** the same additive-energy / Paley-eigenvalue core (`E_{F_p}(μ_n)=n^{2+o(1)}`,
Shkredov-open). The inverse-theorem route does not bypass it — B-R's small-doubling hypothesis IS
an additive-energy statement about `Bad`, and that energy is at the Sidon floor exactly where the
prize lives. Circular.

**Artifacts:**
- `docs/kb/deltastar-407-inverse-theorem-setup.md` — the sumset framing, the constraint, the
  thinness law, the honest verdict.
- `scripts/probes/_wf357_a13_inverse.py` — exact `Bad` enumeration + doubling/energy + thinness
  trend (S1b) + witness-distinctness + random-sparse-killer (S2).

**No Lean brick** (refutation-by-measurement; a `*_REFUTED` brick would only restate the probe).
**Honest remaining gap:** the additive-energy core is untouched; no inverse theorem helps. PARTIAL
= the object is now precisely framed and measured, the bet is refuted, the wall is unchanged.
