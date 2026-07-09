# C-A1 design doc (small-char keystone, #304) — v3 after reading App C verbatim

## What App C actually does (BCIKS20 pp.57-58, extracted to _bciks20_fulltext.txt:3573+)
Factor `R(X, Y^p, Z)`, core `R(X,Ỹ,Z)` separable irreducible (p = p^f). Decoded root:
`Ỹ = Pz(X)^p` roots the core; `Pz(x₀)^p` is a simple root of the H-branch. Hensel runs on
the core with ADJUSTED WEIGHTS (Ỹ gets weight p; T = W·Ỹ weight D−(d_H−1)p; d ≤ D_Y/p;
Claim A.2 budgets: `Λ(β_t) ≤ ((d−1)e_t + t+1)(D−(d_H−1)p) − pt < (2t+1)dD`).
Vanishing pattern: `π_z(α_t) = 0` for all `t < D_X` EXCEPT `t ≤ pk` divisible by p
⟹ `γ = Σ_{t≤k} α_{pt}(X−x₀)^{pt}` (p-supported!).
THEN the paper builds `L̂ = L(T^{1/p}, Z^{1/p})` (genuinely inseparable extension — F(Z) is
imperfect even for finite F), takes `γ̂ = Σ σ̂(α_{pt})(X−x₀)^t` with `γ̂^p = γ`, and re-runs
the 5.2.7 per-x word-comparison counting IN L̂ to conclude `γ̂(x) = w(x,Z) = u₀(x)+Z·u₁(x)`,
i.e. the final family IS z-affine. (σ = Frobenius⁻¹ on F_q — the paper already uses
finiteness here.) BCHKS25 p.25 defers verbatim to this appendix ("the arguments there
remain applicable") — no newer published treatment.

## v3: ELIMINATE L̂ — the powered-word comparison + finite-field subspace extraction
KEY REWIRING (better than the paper, feeds existing in-tree targets):

(i) **Stay in L.** Instead of σ̂-twisting γ, compare γ(x) against the POWERED word
   `w(x,Z)^p = (Σ_t Z^t u_t(x))^p = Σ_t Z^{pt}·u_t(x)^p` — an honest low-degree F[Z]-element
   (char-p binomial, C-K2). The per-x kill (in-tree `embedding_eq_zero_of_matchingSet_large`
   / the SectionNewton window analogues) applies IN L to `γ(x) − Σ_t Z^{pt} u_t(x)^p` with
   the p-adjusted budget. Conclusion: `γ(x) = Σ_t Z^{pt}·u_t(x)^p` per heavy x; interpolation
   over x (5.2.8, in-tree shapes) gives `γ = Σ_t Z^{pt}·B_t(X)` with `B_t ∈ F[X]`, and
   per-z: `P_z^p = π_z(γ) = Σ_t z^{pt}·B_t`.

(ii) **The subspace lemma (N1 — the genuinely new brick).** Over a FINITE field F, the set
   of p-th powers in F[X] is `{g^p} = F[X^p]` — an **F-linear subspace** (Frobenius
   surjective on F ⟹ coefficients range over all of F). For infinite imperfect F this is
   false — this is exactly the step replacing the perfect-closure twist.
   Then: `Σ_t z^{pt}·B_t ∈ F[X^p]` for ≥ k+1 distinct z (it equals `P_z^p`!), Vandermonde
   in `z^p` (injective in z) ⟹ each `B_t ∈ F[X^p]` (a subspace-valued interpolation:
   F-combinations of members stay in the subspace; solve for B_t as F-combos of the values).

(iii) **σ-extraction (N2 = C-K2 dictionary content).** `B_t ∈ F[X^p]` ⟹ unique `b_t` with
   `b_t^p = B_t` (`b_t = contract ∘ coeff-Frobenius⁻¹`), `deg b_t = deg B_t / p < k_deg`.
   Pointwise: `P_z^p = (Σ_t z^t·b_t)^p` ⟹ `P_z = Σ_t z^t·b_t` (Frobenius injective on F[X]).
   **THE FAMILY IS z-POLYNOMIAL OF WIDTH k WITH COEFFICIENT POLYNOMIALS b_t — the exact
   `StrictCoeffPolysResidual`/`CurveFamilyData` B-form, no shape change, no new front door.**

(iv) Budgets (C-K4): the p-adjusted Claim-A.2/window budgets, factor-count union bound over
   e_i ≤ log_p D_Y. All Schwartz–Zippel-counted shapes already in-tree.

## What dies / survives from v2
- v2's "ž-curve + Vandermonde word extraction + new front door" is SUPERSEDED: with the
  powered-word comparison, the conclusion is genuinely z-affine; existing targets suffice.
- The F-candidate "StrictCoeffPolysResidual false at small char" is WRONG — retracted
  (the kill against the powered word restores the B-form). Do NOT post it.
- The C-A5 fence stays valid and valuable with the corrected reading: it witnesses that the
  RAW root family of an inseparable factor (BEFORE the word-comparison kill) is only
  ẑ-structured — fencing routes that skip the powered-word comparison. Caption must be
  fixed accordingly when landing (the fence refutes "verbatim transport of the separable
  conclusion shape", not the final theorem's shape).
- C-K3 (probability reparametrization) DOWNGRADED to unneeded for the main chain.

## Brick list for the build wave (revised)
- N1 `PthPowerSubspace.lean`: (a) `Set.range (·^p) = F[X^p]`-submodule over finite F
  (or: ∀ f, (∀coeff i, i % p ≠ 0 → coeff = 0) ↔ ∃ g, g^p = f — choose the form easiest to
  consume); (b) line/Vandermonde interpolation INTO a submodule: values in a submodule at
  ≥ k+1 points with invertible Vandermonde ⟹ coefficients in the submodule (pure linear
  algebra over F, works for any submodule of any F-module).
- N2: already in the C-K2 dictionary brick (expand/contract/Frobenius + injectivity).
- N3 (next wave, after recon): the powered-word kill wiring into the SectionNewton window
  chain (p-adjusted budgets) — consumes N1+N2+the landed window capstones.
- N4 (last): factor-family assembly (e := max e_i, union bound) + the expChar-uniform
  statement (C-A4) so char-0/large-p/small-p are ONE theorem (q^e = 1 degenerates).
