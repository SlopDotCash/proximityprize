# Resolution of the BGK-to-Prize Bridge and Normalized Syndrome-Space Spectral Laws

**Module:** `ArkLib/Research/ProximityGap/Frontier/CarbonBGKPrizeBridgeResolution.lean`  
**Probe / Style Audit:** `scripts/probes/probe_carbon_bgk_lint_and_bridge.py`  
**Honesty Status:** Unconditional theorems + exact refutations (zero `sorry`, zero new `axiom`; standard `{propext, Classical.choice, Quot.sound}` only).

---

## 1. Executive Summary

This note and companion Lean 4 module resolve **Remaining Proof Obligation #4** of `docs/research/proximity-gap/integration-assessment-2026-11-21.md` (`_PrizeFloorOfBGK.lean` vs `PROXIMITY_PRIZE_WORKBENCH.lean` vs `IncidenceDeviationCharSum.lean`) on three fronts:

1. **Normalized `(n - k)`-Dimensional Syndrome-Space Spectral Bridge (`§1`):**
   `IncidenceDeviationCharSum.lean` worked in the 1D toy model `V = F` without dividing by `|V|`, incurring a vacuous `q · B` deviation factor (`|I - |G|| ≤ q · B`) and noting explicitly that no in-tree theorem identified the `(n - k)`-dimensional syndrome quotient of the prize with the spectral sum. We prove:
   - **`card_directionPerp_mul_eq`**: For any finite `F`-vector space `V` and any `s₁ ≠ 0`, the annihilator hyperplane `s₁^⊥ ⊆ AddChar V ℂ` has exact cardinality `|V| / |F|` (`#(s₁^⊥) · |F| = |V|`), proved directly by specializing `LineIncidenceSpectral.lineIncidence_spectral` to `S = {0}, s₀ = 0`.
   - **`syndromeLineIncidence_abs_sub_mean_le`**: Dividing by `|V|` cancels `#(s₁^⊥ \ {0}) = |V| / |F| - 1` against `|F| / |V|` with **zero `q`-loss**:
     $$\left|I_V(S, s_0, s_1) - \frac{q\,|S|}{|V|}\right| \le \left(1 - \frac{q}{|V|}\right) \max_{\psi \in s_1^\perp \setminus \{0\}} \left\|\sum_{s \in S} \psi(s)\right\| \le B.$$
   - **`far_mcaBadCount_eq_syndromeLineIncidence` & `far_mcaBadCount_abs_sub_mean_le`**: For any linear code `C = ker H` (`H : (ι → F) →ₗ[F] V`) and far direction `u₁` (`FarFromCode C δ u₁`, `H u₁ ≠ 0`), the MCA bad-scalar count equals `syndromeLineIncidence F (syndromeBall H δ) (H u₀) (H u₁)` and inherits the `(1 - q/|V|) · B` spectral band.
   - **`syndrome_charSum_sup_sq_ge_parseval`**: Conversely, Parseval on `V` forces every uniform nontrivial syndrome character bound `B` (`∀ ψ ≠ 0, ‖∑_{s ∈ S} ψ s‖ ≤ B`) to satisfy
     $$|S|\,(|V| - |S|) \le (|V| - 1)\,B^2.$$
     In codimension `n - k ≥ 2` at production radii where `|S_b| ≈ n · |V| / q = n · q^{n-k-1} ≫ n^2`, this proves unconditionally that **no phase-forgetting uniform bound `B` on `V` can ever satisfy `B = O(n)`**; reaching `O(n)` requires keeping oscillatory phase cancellation across `ψ ∈ s₁^⊥ \ {0}`.

2. **Refutation of the Unguarded Workbench Residual `WorstCaseIncidenceBound` (`§2`):**
   In `PROXIMITY_PRIZE_WORKBENCH.lean:351`, the single residual `(R)` was stated as:
   ```lean
   def WorstCaseIncidenceBound (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b B : ℕ) : Prop :=
     ∀ s₀ s₁ : Fin m → F, s₁ ≠ 0 → (cosetLowWeight H b s₀ s₁).card ≤ B
   ```
   Because this omits `FarFromCode`, **every** nonzero parity-check matrix `H ≠ 0` has some column `s₁ = H(e_i) ≠ 0` (`e_i = Pi.single i 1`), and along `s₀ = 0` every `γ ∈ F` produces the weight-`≤ 1` witness `γ • e_i` (`H(γ • e_i) = γ • s₁`). Thus `#badScalars = |F|` and `#cosetLowWeight ≥ |F|`, refuting `WorstCaseIncidenceBound H b B` for every `H ≠ 0`, `b ≥ 1`, and `B < |F|` (`not_workbenchWorstCaseIncidenceBound`). (In true MCA, `u₁ = e_i` is `1/n`-close to `0 ∈ ker H`, so `(0, 0)` jointly explains the pencil when `b ≥ 1`.)

3. **Unconditional Refutation of the Linear-Budget BGK-to-Above-Johnson Upgrade (`_PrizeFloorOfBGK.lean`) and Exact MCA-vs-List Separation (`§3`):**
   `_PrizeFloorOfBGK.lean` (lines 49–53, 108–111) posited that an actual proof of the subgroup character-sum bound `WorstCaseIncompleteSumBound ψ G M` on `G = μ_n ⊂ F_p^×` would have to upgrade to above-Johnson `OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ B` at the prize budget `B = ⌊p ε*⌋` (`ε* = 2^{-128}`). Combining `OpenCoreConditionalPin.worstCaseIncidence_pin` with `DesignatedPrimeJohnson` and `SmoothTwoHeadProduction`, we prove unconditionally:
   - **`firstPrime_no_aboveJohnson_incidence_at_prizeBudget` & `firstPrime_bgk_does_not_upgrade_above_johnson`**: At `P₁ = 2^{30}(2^{128} + 192) + 1` (`B = P₁ / 2^{128} = 2^{30} = n`), `WorstCaseIncidenceBounded` is **false** for every `δ ∈ [johnson k, 1]` across **all four prize rates** `k ∈ {2^{29}, 2^{28}, 2^{27}, 2^{26}}`—even under `WorstCaseIncompleteSumBound ψ G M` for **any** `M ≥ 0` (including `M = 0`).
   - **`secondPrime_rateEighth_list_beats_johnson_while_mca_fails`**: At `P₂ = 2^{30}(2 · 2^{128} + 13) + 1` (`B = P₂ / 2^{128} = 2^{31} = 2n`), rate `1/8` (`k = 2^{27}`), and the explicit above-Johnson integer error count `e = 694,116,763` (`johnson(2^{27}) < 694,116,763 / 2^{30}`):
     1. **Grand List Decoding succeeds within budget:** every Hamming ball of radius `694,116,763` contains at most `1,660,990,722 ≤ 2^{31}` codewords (`AtErrors dom 1 (2^27) 694116763 (P₂ / 2^128)`).
     2. **Grand MCA fails at the exact same code, prime, radius, and budget:** `¬ WorstCaseIncidenceBounded (ReedSolomon.code dom (2^27)) (694116763 / 2^30) (P₂ / 2^128)`.
     This proves unconditionally that **worst-case list-size bounds do not transfer linearly to line-MCA incidence bounds at `O(n)` budgets**: `s`-head algebraic secant amplification (`s = 2, 3, 4`) inflates a tiny `O(1)` list into `s(e + 1) > B` bad line scalars.
   - **`smoothWindow_lowRate_below_johnson`**: Across **every** finite field `F` with `Fintype.card F / 2^{128} ≤ 1,163,220,311` and **every** smooth domain `D : Fin (2^{30}) ↪ F`, both low prize rates `1/8` and `1/16` satisfy `mcaDeltaStar < johnson k`. In particular, across the entire narrow split-prime window `[2^{158}, 2^{158} + 2^{144}]` (`B ∈ [2^{30}, 2^{30} + 2^{16}]`) where `SplitPrimeSixthDensity.narrow_passing_count` guarantees `> 2^{106}` primes with unit sixth-moment Wick energy `E_3(μ_{2^{30}}) ≤ 15 n^3`, low-rate MCA remains strictly below Johnson—showing that **moment/flatness laws on `μ_n` govern list/tail geometry only after clearing the domain-independent multi-head secant budget `B ≥ s(e + 1)`**.
