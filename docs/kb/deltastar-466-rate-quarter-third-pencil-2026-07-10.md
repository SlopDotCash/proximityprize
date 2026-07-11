# Rate-quarter predecessor: the third pencil cannot be excluded — `BasePencilImageCap` refuted at literal P1

## Status

Closing round of the pencil-count arc
(`deltastar-466-rate-quarter-pencil-count-charge-2026-07-10.md`).  The fiber
consumer closed the prize budget iff at most two divided-difference pencils
pass through a base scalar.  This note records: (a) the exact structural
constraints on a third pencil (proved), and (b) its kernel-checked
realization at the literal canonical P1 domain (refutation of
`BasePencilImageCap`).

Formal kernel (compiles clean via lock-free `pg-iterate` (62s), 14 audited
theorems all `[propext, Classical.choice, Quot.sound]`, no `sorry`, no
`axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterThirdPencilExclusion.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_third_pencil.py` (full
enumeration at `μ_256/F_257` with image card 3, plus every literal-P1
constant).

## 1. Characterization (proved)

* `base_pair_inter_subset_aligned`: `S₀ ∩ S_j ⊆ aligned(π_j)` — the base's
  pairwise intersections are absorbed into the pencils' aligned regions.
* `base_triple_overlap_card_le`: for two distinct pencils through the base,
  `|S₀ ∩ S_i ∩ S_j| ≤ k − 1`.
* All naive exclusion arithmetic is vacuous at P1: `4T − 3N < 0`, and the
  Bonferroni bound `P(2T−N) ≤ N + C(P,2)(k−1)` never binds because
  `k − 1 = 268435455` dwarfs the `2T−N = 111848108` floors.

## 2. Refutation (kernel-checked at literal P1)

Partners-collinear trick: three partners on one pencil `σ = (x^(2m), 1)`,
base off `σ` — then the three pair pencils are pairwise distinct
*automatically* (`π_i = π_j` would force `p₀` onto `σ`).  With `m = 2^25`
(32 residue classes of `2^25` coordinates), `γ₀ = 2`, partners `3, 4, 5`:

```text
p₀ = x^(2m) + x^m,  p_j = x^(2m) + γ_j,
dir_j = (γ_j − x^m)/(γ_j − 2),   dir_i − dir_j ∝ (x^m − 2) ≠ 0
   (x^m ∈ μ_32 while 2^32 ≠ 1 in F_P: 0 < 2^32 − 1 < P),
classes: B = {0..13} σ-aligned (14·2^25 ≥ k), P₁ = {14..23} π₁-aligned
   (10·2^25 ≥ k), P₂ = {24..27}, P₃ = {28..31};
S₀ = P₁∪P₂∪P₃, S_j = B ∪ (4 classes of P_j): all 18·2^25 = 603979776 ≥ T.
```

Non-jointness by pinning: partners' second row pinned to the constant `1`
on `B`, mismatching on `P_j` (`dir_j = 1 ⟺ x^m = 2`); base's second row
pinned to `dir₁` on `P₁`, mismatching on `P₂` (`dir₁ = dir₂` forces the
common value `1`, then `x^m = 2`).  Everything is generator-symbolic from
`orderOf g = 2^30` — no `μ_32`-order lemma even needed, only
`(x^m)^32 = 1`.

`basePencilImageCap_canonicalDomain_refuted`: the four-scalar family
`{2,3,4,5}` has pencil-image cardinality **3** through its base at the
canonical domain.  The class budget also fits `P = 4` (S₀ = 4·4+2 classes),
and since the consumer needed `P ≤ 2`, **no uniform base-pencil cap
survives**.

## 3. Honest state of the predecessor branch

Dead proof routes (all kernel-refuted at literal P1): per-coordinate
escape charges (`SharedFreshTripleFree`), collinear-triple-freeness, and
uniform base-pencil caps (`BasePencilImageCap`).

Still valid and axiom-clean (the counting toolkit): pencil transport,
witness incomparability, absorption dichotomy, triple rigidity, collinear
boost, per-pencil vote bounds, uniform rider cap `N−T+1`, alignment ladder,
ten-rider Johnson crossover, per-fiber weighted cap
`fiber·(T−A_π) ≤ N−T`, base-triple `≤ k−1` overlap, four-witness triple
pigeonhole.

**Designated successor**: the layered/weighted budget.  For a base scalar,
`#bad − 1 = Σ_π fiber_π` with `fiber_π ≤ (N−T)/(T−A_π)`; pencils with
`fiber ≥ 9` have alignment `≥ T − (N−T)/9 = 539356427`, above the Johnson
threshold, and are Johnson-packable (aligned regions pairwise `< k`); the
light layers (`fiber ≤ 8`) are unbounded by pure counting and need either
an algebraic constraint linking many low-alignment pencils through one
point, or acceptance that the predecessor pin needs the structured-floor
route (`PredecessorStructuredFloorResidual`) instead.  A layer-cake
summation `Σ_{φ≥9} JohnsonCount(T − (N−T)/φ)` is the concrete next
computation.

## 4. What this is not

No delta-star change; the bracket
`3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` and the predecessor count
are untouched.  This closes (negatively) the last uniform-cap architecture
in the pencil branch and leaves the weighted layer analysis as the sharpest
open surface.

## 5. Lean pitfalls recorded (additions)

* Kernel deep recursion strikes on ANY `rfl`/`show` that crosses an
  `SMul F F` instance boundary at `F = ZMod P` (huge modulus): value-level
  `•` synthesized fresh vs. module-argument-derived instances are defeq
  only through the `ZMod P` recursor.  Safe pattern: `rw [pencilDir]` (the
  def's own equation) followed by `simp only [Pi.smul_apply, Pi.sub_apply,
  smul_eq_mul]` — elaborator-level rewriting only.
* Phrase every big-power formula through one canonical atom function
  (`xm g e = (g^e)^(2^25)`, with `x^(2m) = xm^2`), so `ring`/
  `linear_combination` see a single elaboration.
* `pg-iterate.sh` displays only the first 10 axiom-audit lines
  (`grep … | head`); the audit itself covers all `#print axioms`.
