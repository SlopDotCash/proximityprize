# Subspace-design derandomization route is DEAD for plain RS — caps at Johnson, domain-blind (#444)

> **Scope correction (2026-10-28 audit, T48).** The restricted calculation is correct. In a plain
> coordinate projection, each kernel `A_i` of a `d`-dimensional polynomial space has dimension
> `d − 1` except at common roots, so the total `n(d−1) + (k−d)` is attainable for `1 ≤ d ≤ k`. The
> no-go therefore applies to proofs that go **through this explicit subspace-design invariant**
> in the parameter regime analysed. It does not follow that every derandomization or proximity
> proof must use that invariant, or that folding is the only possible mechanism. The claim that all
> 2026 results "never" treat plain RS also conflicts with the random-RS capacity results cited in
> the opening paragraph (AGL24/GG25). Read "PROVABLY capped", "no structure of μ_n can change it"
> and "rigorous impossibility" as statements about this invariant only.

Rigorous route-elimination (RS-list-decoding army, derand-subspace angle, ranked N8/I9/F9). The highest-leverage
hope — derandomize the random-RS-to-capacity results (AGL24/GG25) to explicit smooth RS via subspace designs —
is PROVABLY capped at/below Johnson for plain (unfolded) RS, and no structure of μ_n can change it.

## The mechanism (rigorous)

Every subspace-design list-decoding / proximity-gap proof reduces to the **τ-subspace-design inequality**
(2601.10047 Def 4.3): for every dim-d subspace A ≤ C with d ≤ r, `(1/n)Σ_i dim(A_i) ≤ d·τ(r)`, `A_i={a∈A: a_i=0}`.
For RS, `Σ_i dim(A_i)` = total zero-count of a d-dim polynomial space over the domain.

- **For plain RS (folding m=1):** the worst dim-d subspace is `A = {polys divisible by k−d fixed linear factors}`
  (dim d, k−d common roots), giving `Σ_i dim(A_i) = n(d−1)+(k−d)`, hence
  **`τ(r) = max_{d≤r} [(d−1)/d + (k−d)/(dn)] → 1`** as d grows.
- Achievable radius `1−τ(r)` drops **below Johnson `1−√ρ` already at d=2** (ρ=1/4,n=64: τ(2)=0.609 ⟹ radius
  0.391 < Johnson 0.5).
- The line-stitching lemma (5.7) needs r≥3, ε>2/r — so it REQUIRES good τ up to d=r≥3, which plain RS can't supply.
- Cross-check: the FRS folded-Wronskian subspace-design bound `d(k−d)/(m−d+1)` (Lemma 4.1) is **undefined for d≥2
  when m=1** (denominator ≤0). Folding depth `m ≥ d` is STRUCTURALLY REQUIRED — folding is the only mechanism that
  divides the zero-count by (m−d+1) to keep τ near R as d grows. Plain RS (m=1) has no division.

## The decisive point: τ is DOMAIN-BLIND

`τ` depends ONLY on d and the max common-root count k−d — **both domain-independent**. So NO smoothness / 2-power
structure of μ_n changes τ. The smooth domain is genuinely not a subspace design of the required quality. This
matches that ALL 2026 results (Goyal–Guruswami, JLR, BCDZ) handle only **folded RS / multiplicity codes, never
plain RS**.

## Why this sharpens the prize

The subspace-design invariant **deliberately discards exactly the cancellation/incidence structure (char-sum
concentration) that distinguishes μ_n from a bad domain** — so it is provably the WRONG lens for the prize.
Getting past Johnson for plain RS needs the **char-sum / far-line-incidence concentration the prize has always
pointed at**, NOT a derandomization argument.

## Net (route eliminated)

The derandomization / subspace-design route is **dead for plain RS** — a rigorous impossibility (caps at Johnson,
domain-blind). Combined with the dilation-orbit list law (list = O(1) in window, floor ⟺ no codeword outside the
orbit = BGK wall) and Hab25 (MCA up to Johnson only), the picture is consistent: explicit-smooth-RS list-decoding
past Johnson reduces to the char-sum/BGK concentration, and the import-from-folded-RS shortcuts are all eliminated.
The prize genuinely requires the BGK char-sum bound, restated cleanly as a list-decoding statement. Closed
conjecture (impossibility): `τ(r) = (r−1)/r + (k−r)/(rn) ≥ (r−1)/r` for plain RS over ANY domain.
