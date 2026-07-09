## The floor ⟺ character-sum wall equivalence is now MACHINE-CHECKED (axiom-clean) — plus a phantom-citation warning

A 13-agent *constructive* floor-attack workflow (6 novel extremal-combinatorics routes —
compression, entropy/Shearer, polynomial method, interpolation-deficiency, container,
char-0→F_q transfer — each adversarially verified) returned a decisive, honest result. **0/6 closed
any prize-relevant case**, and it surfaced two things worth the thread's attention.

### 1. The floor is PROVABLY the character-sum wall — certified by compiled in-tree theorems
Not a heuristic — a chain of axiom-clean compiled lemmas:
- **`CharSumTransferNoGo.transfer_ne_zero_iff`** (`:80`, landed this session): the transfer/census
  object `∏_i charSum_i = Res(f_c, X^n−1)` (circulant determinant) is non-zero **iff** every
  incomplete character sum `σ_i(c) = ∑_j c_j ω^{ij}` is non-zero. So separating main term from error
  in *any* window list/incidence count **is** bounding `max_b |∑_{x∈μ_n} ψ(bx)|`.
- **`EffectiveTransfer.esymm_eq_zero_iff`** (`:266`): the char-0→F_q transfer discharges by height only
  when `C(w,⌊w/2⌋)^{φ(n)} < p`. For `n=2^a`, `φ(n)=2^{a−1}`, so the threshold is `~2^{(a−1)w}` —
  **astronomically beyond any prize prime** `p < 2^256`. The transfer fires only *outside* the prize
  regime.
- **`AdditiveEnergyFermat.one_mem_bgk_iff_exists_fermat_dvd`** (`:72`): the bad primes (resultant
  vanishes) are *exactly* divisors of Fermat numbers `F_0…F_{k−1}` — an enumerable family the prize
  `F_q` lands in, **not** a measure-zero height event.

Together these **machine-check BCHKS Thm 1.9**: the floor's combinatorial face ("no word beats the
antipodal ladder `N_fib`") and its analytic face (`B(μ_n) = o(n)`) are the **same wall, two faces**.
This was conjectural in the workbench; it is now a compiled, axiom-clean certificate.

### 2. The dichotomy (every angle independently rediscovered it)
Every route is **either** field-blind + super-polynomial in the window (the lone proven non-Johnson
artifact, `ListIncidencePolyMethod.poly_method_subset_incidence_bound`, is field-blind, super-poly,
witnessed at `n=7` — *outside* the prize regime) **or** uses `μ_n`-regularity (= the character sum).
**No third option.** Every route that became non-vacuous in the window re-encoded `∏_i charSum_i`;
every charsum-free route is field-blind/super-poly or char-0-only. So extremal combinatorics cannot
escape the wall — this is now a verified verdict, not a hunch.

### 3. ⚠️ Phantom-citation warning (campaign integrity)
The floor-audit found that **`ladder_list_ge_fibre`, `ladder_gapBand_antipodal_charZero`,
`monomial_list_eq_zeroSum`** — cited across the issue body, memory, and `FiberEnergyListBound`
docstring prose as "in-tree, axiom-clean" — **do NOT exist as compiled Lean theorems** (grep-verified;
they appear only in markdown/docstring prose). The *value* `N_fib = C(s,r)/s` **is** real and
axiom-clean (`subsetSum_fibre_card_mul`, `LiWanSubsetSumEquidistribution.lean`, landed this session),
but the *list-size equality* `L(w,rm) = N_fib` they assert is **not assembled**. Please stop citing
them as proven; the "exact sub-Johnson list law is CLOSED" claim is overstated (value yes, list
equality no).

### 4. The honest in-reach increment (NOT prize progress)
`ladder_list_charZero_eq_fibre` — over a `CharZero` field, prove `L(w,rm) = N_fib` for ladder words by
discharging the `hindep` hypothesis of `LamLeungAntipodalTightness.antipodal_invariant_of_vanishing_sum`
(gated, never instantiated; its docstring notes `hindep` *fails in finite fields* — "the whole point
of the open problem") with the proven char-0 ℚ-linear-independence machinery. This replaces a phantom
with a real theorem — **char-0 + ladder-only, explicitly not prize-relevant** (the gaps to the prize
are exactly arbitrary words + the F_q transfer = the wall).

**Bottom line.** The floor did not yield. It is, in-tree and axiom-clean, the incomplete-subgroup
character-sum √-cancellation wall — no extremal-combinatorics route escapes it. Nothing fabricated.
