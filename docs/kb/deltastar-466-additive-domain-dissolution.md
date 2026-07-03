# #466 lane L5 — Additive/Binius domain dissolution: the multiplicative wall is a domain artifact (2026-07-02)

**Status: LANDED, axiom-clean.** Dossier v3 §6 Tier-3 item "Additive/Binius domain dissolution"
is now formalized. Two Lean files, every `#print axioms` a subset of
`[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`, verified with `scripts/pg-iterate.sh`:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AdditiveDomainDissolution.lean`
  (fixed-character dichotomy, coset blindness, `E(S) = |S|³`; ✅ OK 163s)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AdditiveDomainDissolutionDual.lean`
  (full dilated spectrum `{η_b}_b`, exact spike localization on `S^⊥`; ✅ OK 153s)

This is a **bankable off-core win** (no wall contact): it proves the analytic core of the
multiplicative prize obstruction *does not exist* on additive (Binius / additive-NTT) domains.
It is NOT a refutation and NOT a prize-core advance; nothing here goes in DISPROOF_LOG.

## 1. What this DOES prove (theorem names)

Setting: `S` an additive subgroup of an ambient group/ring `F` — stated once for any
`SetLike`+`AddSubgroupClass`, so it instantiates verbatim for `AddSubgroup G` and for
`Submodule K F` (the Binius shape: `K = ZMod 2`, `F = F_{2^k}`, target `R = ℂ`, `ψ = ` trace
character). Characters are Mathlib `AddChar F R` into any integral domain `R`.

1. **Fixed-character dichotomy** (`addChar_sum_subgroupClass_dichotomy`, plus
   `addChar_sum_addSubgroup_dichotomy` / `addChar_sum_submodule_dichotomy`):
   `∑_{x∈S} ψ x = |S|` (iff `ψ` is trivial on `S`) or `= 0`. Pure `AddChar` orthogonality on
   the subgroup (`AddChar.sum_eq_card_of_eq_one` / `AddChar.sum_eq_zero_of_ne_one` applied to
   the restriction `ψ ∘ S.subtype`).
2. **The full far-direction spectrum collapses** (`dilated_sum_dichotomy`, Dual file): for
   EVERY dilation direction `b`, `η_b(S) := ∑_{x∈S} ψ(b·x) ∈ {0, |S|}`. So the additive-domain
   analogue of the prize wall object `M(μ_n) = max_{b≠0} |η_b(μ_n)|` is degenerate: the
   spectrum is a two-point set, with no intermediate eigenvalue at ANY direction. Compare the
   multiplicative case, where `M ∈ [√(p−n), 2√(p log p)]`-ish is a genuinely transcendental
   quantity (Gauss-period house, Paley conjecture, the entire #444/#464/#466 no-go landscape).
3. **Exact spike localization** (`dilated_sum_eq_card_iff_mem_dualDirections`, char-0 target):
   the set of directions where `η_b(S) = |S|` is EXACTLY the annihilator
   `S^⊥ := dualDirections S ψ = {b | x ↦ ψ(b·x) trivial on S}`, constructed as an honest
   `AddSubgroup F`. Off `S^⊥` the sum vanishes identically
   (`dilated_sum_eq_zero_of_not_mem_dualDirections`).
4. **Coset blindness** (`addChar_coset_sum_eq_zero_of_nontrivial`): for `ψ` nontrivial on `S`,
   every coset sum `∑_{x∈S} ψ(y+x) = ψ(y)·∑_{x∈S} ψ(x) = 0` vanishes *identically in `y`* —
   ambient character analysis cannot distinguish cosets of `S`.
5. **Exact extremal energy** (`subgroupClass_energy` / `addSubgroup_energy` /
   `submodule_energy`): `E(S) = #{(a,b,c,d) ∈ S⁴ : a+b = c+d} = |S|³`, by the one bijection
   `(a,b,c) ↦ (a,b,c,a+b−c)` (closure gives membership of the fourth coordinate). The
   quadruple condition is stated in the AMBIENT group — the form relevant to an evaluation
   domain `S ⊆ F`. Also `Fintype.card` form and the tie-in `addEnergy_univ_cube` to Mathlib's
   `Finset.addEnergy`. Compare: pinning `E(μ_n)` beyond `n³` on multiplicative smooth domains
   consumed campaign-scale effort (#444 energy chain, DC crossover, Wick-surplus wall).

**Consequence, stated honestly:** the specific analytic mechanism that blocks
Johnson→capacity on multiplicative smooth domains — a nondegenerate far-direction character
spectrum whose maximum `M` nobody can push below `n^{1−o(1)}` — is a **multiplicative-domain
artifact**. F₂-linear evaluation domains have no such object: all `η_b` are `0` or `|S|`
exactly, and additive energy is extremal exactly.

## 2. What this does NOT prove (do not over-claim)

- **It does NOT solve any Binius / additive-RS proximity, MCA, or soundness question.** The
  beyond-Johnson mutual-correlated-agreement problem for additive-NTT RS codes remains OPEN.
  Binius soundness (DP24 and successors) has its own open questions; none is touched here.
- **It does NOT transfer anything back to the prize core.** The prize regime (#466 §2) is
  multiplicative smooth `μ_n ⊂ F_p^×`; this brick only certifies that the additive analogue of
  its wall object degenerates. No statement here constrains `M(μ_n)`, `E(μ_n)`, or δ* for
  multiplicative RS.
- **"Degenerate spectrum" ≠ "easy proximity".** Vanishing of every nontrivial `η_b` means
  ambient Fourier analysis is *blind* on additive domains (item 4 above), not that the
  proximity question is resolved — a tool losing its grip is not the problem disappearing.

## 3. The relocated hardness, precisely

For additive domains the far-direction analysis does not vanish — it **relocates**, and the
Lean development pins where:

- All magnitude information in `{η_b(S)}_b` degenerates to the indicator function of the
  annihilator subgroup `S^⊥ = dualDirections S ψ` (theorem 3 above). Under the trace pairing
  of `F_{2^k}` this is the trace-dual F₂-subspace, `|S^⊥| = |F|/|S|`; Parseval
  (`∑_b |η_b|² = |F|·|S|`) cross-checks: `#spikes = |F|/|S|` exactly, consistent with the
  spikes being exactly `S^⊥`.
- Therefore the discriminating object for an additive-RS far-direction/proximity statement is
  the **coset geometry of `S^⊥` across the NTT subspace flag**
  `S = S_k ⊃ S_{k−1} ⊃ ⋯ ⊃ S_0`: which characters are trivial on which flag members —
  equivalently the dual-code weight/coset structure of the folded domains. That is a
  **combinatorial, subspace-lattice problem** (no transcendental character-sum scale), with
  its own open questions; nothing in this lane bounds it.
- Agreement on *proper subsets* of `S` — the actual proximity object — is invisible to ambient
  characters (coset blindness), so any additive-domain δ*-analogue must be attacked with
  dual-flag combinatorics, not exponential sums. This is the precise sense in which the
  Johnson→capacity gap question for additive domains is a *different problem*, not a solved
  one.

## 4. Verification record

```
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AdditiveDomainDissolution.lean
  ✅ OK — all 12 #print axioms ⊆ [propext, Classical.choice, Quot.sound], 0 sorryAx
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AdditiveDomainDissolutionDual.lean
  ✅ OK — all 7 #print axioms ⊆ [propext, Classical.choice, Quot.sound], 0 sorryAx
```

(One fix during audit: the vanishing branch of `dilated_sum_eq_card_iff_mem_dualDirections`
needed a defeq-bridging `have` before `rw` — `AddChar.sum_eq_zero_of_ne_one` produces the sum
over `dilatedRestrict ψ b s`, which is only definitionally equal to `∑ x : s, ψ (b·x)`.)

Cross-references: dossier v3 §6 Tier-3 (this item now DONE); companion multiplicative-side
walls in `SubgroupGaussSum*.lean`; #444 energy-chain memory for the contrast class.
