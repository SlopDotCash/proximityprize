## Adversarial validation (25-agent workflow): all 4 prunes hold, closed-form δ* needs TWO amendments, 0/7 novel routes survive — the core is irreducibly `B(μ_n)=o(n)`

Ran a 5-phase adversarial workflow (red-team the prunes · stress-test δ* against every ABF26
negative result · generate+filter 7 novel combinatorial routes · synthesize), every kill checked
against a **verified in-tree artifact**. Net below; this *sharpens* the workbench, no fabricated
closure.

### 1. The closed form `δ* = H_q⁻¹((1−ρ) − log_q(1/ε*)/n)` — confirmed but needs two amendments
**Confirmed** as the CA/list crossing radius: it is *identically* the level set of the Crites–Stewart
domain-generic bad line (`L_heur(δ) ≈ q^{(H_q(δ)−(1−ρ))n+1}`, set `=q·ε*`). Numerically (ρ=1/2,
n=2³⁰, q=2²⁵⁶) `δ* = 0.4960939215`, sitting `4.7×10⁻¹⁰` below the entropy ceiling `δ_CS`, with
`Johnson(0.293) < δ* < δ_CS < capacity`. Thm 4.18 (Johnson spike `n²/|F|=2⁻¹⁹⁶`) is below the
window and is a *constructive lower-half witness*, not a contradiction.

**Amendment 1 — the ε* term is a red herring; the binding term is `Θ(1/log q)` (Thm 4.17 CS25
collapse).** The collapse offset `1/√(n log q)+2/n−1/log q` is dominated by `−1/log q ≫
log_q(1/ε*)/n`. For `ρ ≤ 1/4` (log₂) the naive δ* sits **above** the collapse line (where `ε_ca=1`)
by `+7×10⁻⁴…+2.6×10⁻³`. Sharp statement:
> `δ*_safe = (1−ρ) − max( log_q(1/ε*)/n , c/log q ) = (1−ρ) − Θ(1/log q)`, the closed form valid
> only **up to** the CS25 collapse line.

**Amendment 2 — δ* is a CA/list answer, NOT a Grand-MCA answer at the same radius.** The list⟹MCA
bridge (Thm 5.1 [GCXK25]) has a **√-proximity loss**: list radius `δ*=0.496` ⟹ guaranteed-MCA
radius `1−√(1−δ*)=0.290 < Johnson`. So CS+bridge certify Grand-MCA only to ≈Johnson; closing the
window for MCA is the open analytic wall (orthogonal to all four negative theorems).

### 2. All four pruned routes hold (conf 9), validated against the tree
- **GM-MDS/Lovett** — field-size lower bound `q ≥ C(n−2,k−1) ≈ 2^{Θ(n)}` (crossover at n≈256) **and**
  "det(M)≠0 on fixed μ_n" = KRZ26 Open Problem 1. (Confirms: stop the Lovett grind.)
- **Folded/subspace-design** — `folding_transfer_no_go` (in-tree): plain-vs-folded metric mismatch is
  maximal; factor-s loss confines any unfold to `δ < (1−ρ)/s`, inside Johnson.
- **Kong–Tamo** — the Hamming ball is algebraizable only via the exponent `q−1`, the unique
  non-permutation power KT excludes; absorbing it ⟹ vacuous `q^{m/2}`, removing it ⟹ Johnson.
- **Character sums** — degree-1 g preserves `E(μ_n)` exactly (dilation invariance) and `x↦xʲ`
  permutes μ_n, so "structured-b" collapses to unrestricted `η_b`; needs `max_b|S(b)|≤C√n` = the
  Shkredov wall (`≈q^{0.0015}`, `E≲n^{49/20}`), hopeless at `n<p^{1/4}`.
- *Lone sub-crack (not a prize crack):* `ListIncidencePolyMethod.incidence_numeric_F7` — the
  slice-rank/CLP method gives an interior bound *sometimes tighter than Johnson without a character
  sum* (F7: |L|≤7 vs Johnson 24, true 6). Field-blind + super-polynomial in the interior, so it
  can't reach `ε*·q`, but it's the only non-Johnson non-analytic foothold. Worth a look.

### 3. 0 of 7 novel routes survive — every one is `B(μ_n)=o(n)` in disguise
Far-pair 2nd moment (→ the 2nd-moment proof of Johnson, vacuous in-window; `deep_band_failure_closed_form`
runs it to ε_mca≥129/131) · cyclotomic subresultant tower (σ-closure false; cites absent lemmas) ·
Newton-stratified census (descent gated by `abs_norm_le = B^{φ(n)}=B^{n/2}` ⟹ `q>2^{2^31}`) ·
punctured-dual Krawtchouk ("low-degree phase⟹small char sum" *is* the Weil bound) · container/Vieta
product (refuted by `SubsetSumEsymmVanishing` no-go + `subsetSum_fiberMax_sq_le_energy` is subset-SUM)
· seed-increment (m-th-root fabricated; `Lambda_interleaved_arity_mono` proves the *opposite*
monotonicity) · Selberg-weighted line moment (the weight β(w) *is* the incomplete char sum in
costume). Closest was the cyclotomic subresultant (novelty 7.5) — it "reduces the prize to the prize."

### 4. The single residual-free deliverable: the irreducibility no-go
Smoothness forces `p ≡ 1 mod n` ⟹ p splits completely in `K=ℚ(ζ_n)`, so
`v_p(N_{K/ℚ}(σ(c))) = Σ_{i∈(ℤ/n)^×} v_{𝔭_i}(σ(c)) = #{i : ∑_j c_j ζ^{ij} ≡ 0 (mod 𝔭)}`. Hence the
census-domination upper half is **logically equivalent** to per-embedding incomplete-character-sum
nonvanishing. The proposed axiom-clean target (wiring `resultant_X_pow_sub_one_eq_bgk_prod`
[`AdditiveEnergyResultantProduct.lean:152`] to `abs_norm_le` [`EffectiveTransfer.lean`]):
> **`census_transfer_iff_charsum_nonvanishing`** — for n=2ᵃ, p≡1 mod n, the char-0 exact list law
> descends to F_p **iff** every incomplete sum `σ_i(c) = ∑_j c_j ωⁱʲ ≢ 0`. I.e. **every** transfer
> route to the upper half provably *is* the Shaw gap `B(μ_n)=o(n)`. (An equivalence, not the bound —
> it certifies the wall's irreducibility, it does not cross it.)

**Bottom line.** δ* is the right CA/list conjecture (needs the `1/log q` amendment, and is *not* the
MCA answer); all 4 prunes hold; all 7 novel routes are the one wall. The honest core is
`B(μ_n)=o(n)` (25y open). New verified machinery this session: `LiWanSubsetSumEquidistribution.lean`
(exact `N_fib=C(s,k)/s`, additive case). Full writeup: `RESEARCH_SYNTHESIS_389.md`.
