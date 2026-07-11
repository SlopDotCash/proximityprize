# δ* #466 — `SmallPoolClosure` DISCHARGED: the small-pool branch of the P1 rate-quarter pin is an unconditional kernel theorem (2026-07-11)

**Lane:** P1 rate-quarter predecessor pin, charge arc (successor of
`deltastar-466-rate-quarter-small-pool-assembly-2026-07-10.md`).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterSmallPoolClosureDischarged.lean`
(pg-iterate OK 17s; 9 theorems audited, all `[propext, Classical.choice, Quot.sound]`;
no sorry, no new axioms, no new hypotheses).

## Result

The assembly file's honest residual `SmallPoolClosure` — the marginal-partition
counting-glue between the kernel-pinned ledger arithmetic and the small-pool branch
theorem — is **proved** (`smallPoolClosure_holds : ∀ dom, SmallPoolClosure dom`).
Consequently the P1 predecessor pin's open content through the counting branch shrinks
from `SmallPoolClosure ∧ StallResidual` to **`StallResidual` alone**
(`predecessor_budget_of_stall`).

## The proof, stage by stage

1. **Fiber partition.** For a bad family with base scalar `γ₀` of pool
   `F = |{D ≠ 0}| ≤ F₀ = 75018133`: `#bad = 1 + Σ_π fib(π)` over the through-base
   pencil image (`Finset.card_eq_sum_card_fiberwise`).  Each fiber member rides its
   pencil (`pencil_reproduces_first/second`), so `fib(π) ≤ F`
   (`riders_card_le_pool`) and `fib(π)·(T − A_π) ≤ F` (`riders_mul_le_Dsupport`).
2. **Layer cake** (`sum_layer_cake`, generic `ℕ`-valued): since `fib ≤ F ≤ F₀`,
   `Σ_π fib(π) = Σ_{m=1}^{F₀} #{π : fib(π) ≥ m}`.
3. **Level sets are Johnson families on `Z = {D = 0}`.** `m·(T − A) ≤ F` extracts
   `A ≥ T − ⌊F/m⌋` (nat division), and the level set is a pairwise-distinct
   through-base pencil family with aligned regions in `Z`, counted by
   `dirFamily_johnson_on_Dzero` + `johnson_core_to_subtracted`
   (`level_card_le_of_arith`).
4. **Uniform per-level caps for ALL `F ≤ F₀`** (the probe-swept values, now kernel):
   - `m = 1`: `≤ 657668325` (`cap_arith_m1`).  Substitute `x := F₀ − F`
     (`a = 517776833 + x`, `n = 998723691 + x`); the constant term is exactly the
     pinned boundary division (`657668326·378645484 = 249023141609739784 >
     249023141355186198 = 998723691·249341378`) and the `x`/`x²` coefficients are
     strictly dominated — a coefficientwise polynomial domination, no `nlinarith`.
   - `m = 2`: `≤ 7` (`cap_arith_m2`), after monotonising `n ≤ N − 2⌊F/2⌋`.
   - `m ≥ 3`: `≤ 5` each (`cap_arith_m3`), at level `T − ⌊F/3⌋`, `n ≤ N − 3⌊F/3⌋`.
5. **Ledger** (`smallPool_budget`):
   `#bad ≤ 1 + 657668325 + 7 + 5·(F₀ − 2) = 1032758988 ≤ N = 1073741824` — the
   uniform-cap closed bound of `ledger_uniform_caps_le_N`, now a theorem about bad
   families rather than pure arithmetic.

## What remains open (the pin's single residual)

`StallResidual` (defined in `_P1RateQuarterDChargeDerecursion.lean`): bad families
ALL of whose base scalars carry stalling pools `F ≥ F₀ + 1`.  There the window
`[T − F, ⌊√((N−F)(k−1))⌋]` is nonempty and sub-Johnson-on-`Z` direction swarms are
uncounted; the two pool-code regimes split at `F = k` (free pool vs nontrivial MDS
pool).  This is the same beyond-Johnson wall as the B-side.  No δ* movement; the
operational bracket `3/8 ≤ δ* ≤ 43/96 + ε` is untouched.

## Kernel-engineering pitfalls (recurring; promoted here)

On width-`F₀` (~7.5·10⁷) `Finset` intervals, two idioms pass elaboration but blow up
the **kernel** (deep recursion / deterministic timeout):

1. `ext`-proved `insert`-splits: `Icc 1 75018133 = insert 1 (insert 2 (Icc 3 …))`
   followed by `Finset.sum_insert`;
2. `rw [Finset.sum_const, …]` on a constant sum over the wide interval.

Kernel-safe replacements used here:

- peel bottom elements with `Finset.sum_eq_sum_Ico_succ_bot` after
  `rw [← Finset.Ico_add_one_right_eq_Icc]`, then `simp only [Nat.reduceAdd]`;
- bound constant tails with `Finset.sum_le_card_nsmul` and rewrite the card via
  `Nat.card_Ico` (which is kernel-cheap on numerals);
- keep all big-numeral cap inequalities in additive one-variable polynomial form:
  `ring`-normalise into `(const + coeff·x) + x·x` shape, compare coefficients with
  `norm_num`, close with `generalize`d product atoms + `omega`.

## Cross-checks

Probe: `scripts/probes/probe_rate_quarter_p1_dcharge_derecursion.py` — exact greedy
optimum `882722755` at `F₀`; uniform caps `{m=1: 657668325, m=2: ≤7, m≥3: ≤5}` swept
over all `F ≤ F₀` (this file's caps match the sweep; the m=1 cap is attained at
`F = F₀`).

## Consumers

- `smallPoolClosure_holds dom : SmallPoolClosure dom` — discharges the named Prop of
  `_P1RateQuarterSmallPoolAssembly.lean` (read-only; not edited).
- `predecessor_budget_of_stall dom (hstall : StallResidual dom) : … → G.card ≤ N` —
  the single-residual form of the P1 pin, composed through
  `predecessor_budget_of_smallPool_and_stall`.

## Next target

The stall band: `StallResidual` at pools `F ∈ [75018134, 480946859]`.  Sub-regimes:
`F < k = 2^28` (algebraically free pool — all structure is the direction list on `Z`,
an affine stack family `s ↦ u₁ − s·D` one level down) and `F ≥ k` (nontrivial MDS
pool code of dimension `k` — fresh algebra, the candidate attack surface named by the
derecursion file).
