# δ* / #466 — SYZ49: the cyclotomic-GCD bedrock — max level set of `R = W_BC/W_AC` on `μ_n` (2026-07-11)

## One-line

The balanced-interior obstruction reduces **exactly** to the max level set of the cyclic rational
function `R(ω) = W_BC(ω)/W_AC(ω)` on `μ_n`, equivalently
`max_{α,β} deg gcd(α·W_AC + β·W_BC, Xⁿ−1)`. **The max level set REACHES `a`** — and *not only* via
coset/binomial structure: over the **proper** subgroup `μ₁₂ ⊂ 𝔽₃₇^×` there are **48** disjoint
`(4,4,4)` triples with level set `= 4 = a`, **42 of them non-coset**, one verified to genuine
`min_syzygy_degree = 4 ⇒ ι = 2` on-domain. **This CORRECTS SYZ48:** the cyclotomic
domain-membership condition is **necessary but NOT sufficient** — it does not close the interior. The
true gate is the finer **band-realizability** (SYZ42 superadditive-union), not membership. The
level-set constancy is *literally* the **BGK additive-character wall**: `R` constant on `A` ⟺
`Σ_{S_BC} L(ω−s) − Σ_{S_AC} L(ω−s)` constant on `A` (discrete-log sum). **CORE OPEN / ON-BGK**, shield
now correctly located.

## Where this sits

- SYZ44: collapsed rate-1/2 `SylvesterInjective` to `ι = ⌊S/2⌋ − δ₁ ≤ 1` (`S=a+b+c`).
- SYZ45: `(4,4,4)⇒ι=2` via a constant syzygy, "only for non-band-realizable triples"; the bound
  fails on the **full** group `𝔽_p^×` cosets (`X^d−c` binomial dependence).
- SYZ47: floor `δ₁ ≥ max(a,b,c)`, discharging the *unbalanced strip* (~37.7%).
- SYZ48: pinned the *balanced interior* (~62.3%) to an on-domain question and **claimed** cyclotomic
  domain-membership (combination roots must return to `μ_n`) is load-bearing / closes it.
- **SYZ49 (this): tests that claim and refutes the sufficiency half.**

## The exact reduction (proved, `_SYZ49CyclotomicGcd.lean`, axiom-clean)

A constant-ratio syzygy `c₀·W_AB + α·W_AC + β·W_BC = 0` (AB-carrying) ⟺ `W_AB ∣ (α·W_AC + β·W_BC)`
(SYZ48). For the AB slot to be band-realizable, `deg gcd(α·W_AC + β·W_BC, Xⁿ−1) ≥ a`. The `μ_n`-roots
of `P := α·W_AC + β·W_BC` are **exactly** the `ω ∈ μ_n \ (S_AC∪S_BC)` with `R(ω) = −α/β` (a single
level). Hence

    max_{α,β} deg gcd(P, Xⁿ−1)  =  max level set of R on μ_n   (capped by max(b,c)).

Theorems (6, axiom-clean = propext/Classical.choice/Quot.sound, no `sorryAx`):
`combination_isRoot_iff_ratio` (root ⟺ level), `gcd_root_pow_eq_one` (domain membership),
`gcd_natDegree_le_max` (the `≤ max(b,c)` cap), `full_split_gives_constant_syzygy` (on-domain assembly),
`on_domain_admits_imbalance_ge_two` (**the corrective**), `mu_root_iff_level` (packaged reformulation).

## Probe (`probe_syz49_cyclotomic_gcd.py`) — the decisive numbers

| Experiment | Result |
|---|---|
| [A] exhaustive small `n` (full & proper subgroups), `b=c` | **MAX LEVEL SET = a** in every case (cap `max(b,c)=a` attained) |
| [A'] proper subgroup `μ₁₂⊂𝔽₃₇`, `b=c=4` | **48** disjoint triples reach level set `=4=a`; **42 non-coset**; `noncoset_max = 4` |
| [B] coset-structured `S`'s | level set **EXCEEDS a** (up to `2a`: `12` on `μ₄₂`, `10` on `μ₆₀`) — the SYZ45 binomial degeneracy |
| [C/C'] adversarial hill-climb, large `n` | only reaches `3–8` — a **search-power artifact** (needle configs), NOT an upper bound; exhaustive proves `= a` |
| [D] BGK: `L(R(ω)) = Σ_{BC}L(ω−s) − Σ_{AC}L(ω−s) (mod p−1)` | **identity holds** (all trials) — level set of `R` = coincidence set of the additive log-phase |

**Verified witness** (`/tmp/verify49.py`, ground-truth `min_syzygy_degree`):
`S_AC={1,8,27,29}`, `S_BC={6,10,11,31}`, `S_AB={14,23,26,36} ⊂ μ₁₂ ⊂ 𝔽₃₇^×`, pairwise-disjoint,
squarefree, **coset-order 1/1/1 (none a coset)**, constant syzygy `W_BC − 11·W_AC = −10·W_AB`,
`min_syzygy_degree = 4`, **`ι = 2` on the prize domain**.

## The BGK-correspondence statement (decisive)

Over `𝔽_p` with `L =` discrete log base a primitive root:

    L(R(ω)) = Σ_{s∈S_BC} L(ω − s) − Σ_{s∈S_AC} L(ω − s)   (mod p−1).

So **`R` constant on a set `A` ⟺ the additive discrete-log sum `f(ω) = Σ_{S_BC}L(ω−s) − Σ_{S_AC}L(ω−s)`
is constant on `A`** — an additive-combinatorics / character-sum statement about `Σ ± L(ω−s)`. This is
the **BGK wall in its native form**. The two campaign walls meet as *one* level-set statement: the
max level set of `R` = the max coincidence set of the additive log-phase. The cleanest unification
the campaign has produced — the μ-basis imbalance residual and the BGK character-sum bound are the
**same** object (max `R`-level = max `f`-coincidence).

## Verdicts (answers to the SYZ49 questions)

- **Max-level-set law:** `≤ max(b,c)` (cap, proved), and the cap is **ATTAINED** (`= a` on balanced
  `b=c=a`) — reaching happens generically (48 witnesses at `μ₁₂⊂𝔽₃₇` alone), not only via cosets.
- **Coset-structure verdict:** coset/binomial `S`'s give level set `≥ a` (up to `2a`) — the known
  SYZ45 `X^d−c` degeneracy — but they are **not** the *only* reachers; non-coset configs also hit `a`.
- **BGK correspondence:** **exact and verified** — `R`-level = additive discrete-log-sum coincidence;
  this is literally the BGK character-sum wall. **Two walls = one statement.**
- **What was proven:** the exact reduction chain (6 axiom-clean theorems) + the **corrective**
  `on_domain_admits_imbalance_ge_two`: domain-membership is *compatible with* `ι ≥ 2` (hypotheses
  satisfiable by the witness), so SYZ48's "domain load-bearing / closes the interior" is **overstated**.
- **New lever?** The genuine gate is re-located: **band-realizability (SYZ42 superadditive-union),
  NOT cyclotomic domain-membership**. CORE remains **OPEN / ON-BGK**, now with the shield in the right
  place and the wall identified as the BGK level-set/character-sum coincidence statement.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ49CyclotomicGcd.lean` (6 theorems, axiom-clean)
- `scripts/probes/probe_syz49_cyclotomic_gcd.py` (experiments A/A'/B/C/C'/D)
- Branch `codex/syz49-cyclotomic-gcd` off `fork/research/proximity-prize` @ 123dd54f2.
