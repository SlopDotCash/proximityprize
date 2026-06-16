# A09: q-spread of the e_2=0 count IS the mod-q additive-energy defect — a clean two-mechanism dichotomy (2026-06-14)

Actionable **A09** (#407 prize). Directly sample the per-prime *defect*
`defect(q) = N(F_q) − N(char0)` of the q-independent combinatorial core
`N = #{ distinct e_1(S) : S⊆μ_n, |S|=w, e_2(S)=0, e_1(S)≠0 }`
(the object from `issue400-e2zero-singles-decomposition…`, whose char-0 count is `Θ(n^{s_max})`,
`s_max=μ−1`). The defect is the `k_D` mod-q additive-energy defect = **the entire prize wall**.

Probes (EVIDENCE, not proof):
`scripts/probes/sweep_A09_modq_defect.py` (defect spread table + halo hunt),
`scripts/probes/sweep_A09_halo_carriers.py` (norm-collision characterization of the carriers).

## 1. The measured defect is NOT a single phenomenon — it splits cleanly in two

Over `F_q` (`q≡1 mod n`), `ζ∈F_q` is a primitive n-th root, so the char-0 ℚ-basis
`{1,ζ,…,ζ^{n/2−1}}` is no longer independent (`Φ_n` splits). Two opposite effects:

- **DROP (saturation).** Distinct char-0 e_1 vectors **collide** mod q ⟹ `N(F_q) < N(char0)`.
  Seen for w with char-0 support (`w=4,8`): defect ≤ 0, equals 0 at most q.
- **RISE (halo carriers).** Sets with `e_2(S)≠0` in char 0 but `e_2(S)=0 mod q`
  ("pure mod-q vanishing coincidences") produce **new** e_1 values ⟹ `N(F_q) > N(char0)`.
  Seen sharply for w where char-0 count is **0** (`w=6`): defect = `N(F_q) ≥ 0`, pure RISE.

So the actionable's premise ("q-spread = the mod-q defect") is confirmed, and the defect is
two-signed with a clean mechanism on each side.

## 2. Per-q defect spread (measured)

| n | w | N(char0) | defect range over q | spread | sign |
|---|---|---|---|---|---|
| 16 | 4 | 48 | [−32, 0] | 32 | DROP/0 |
| 16 | 6 | **0** | [0, +48] | 48 | RISE/0 |
| 16 | 8 | 48 | [−32, +48] | 80 | both |
| 32 | 4 | 224 | [−128, 0] | 128 | DROP/0 |
| 32 | 6 | **0** | [+96, +576] | 480 | RISE |
| 64 | 4 | 960 | [−256, +128] (large q) | 384 | both |

**Saturation caveat + unsaturated n=64 data.** `N(char0)=960`, so any prime `q<961` cannot represent
960 distinct e_1 values — the count is forced to `≤ q−1` (`q=193→192, 257→256, 449→448`), a pure
residue-field-size artifact, NOT defect structure. Re-running at **large** primes `q>1920` escapes
saturation and reveals the genuine two-signed `k_D`:

| q | N(F_q) | defect | |
|---|---|---|---|
| 2113 | 960 | 0 | |
| 2689 | 704 | −256 | DROP |
| 2753 | 1088 | +128 | **RISE** |
| 3137 | 704 | −256 | DROP |
| 3329 | 896 | −64 | DROP |
| 3457 | 768 | −192 | DROP |
| 4289 | 960 | 0 | |

So even for `w=4` (which HAS char-0 support) the unsaturated defect is **two-signed**: saturation
collisions (DROP) at most q, but genuine halo carriers (RISE, `q=2753`) and exact agreement
(`q=2113,4289`) also occur. This rules out "defect is always ≤0 for char-0-supported w" — both
mechanisms are present simultaneously.

The actionable cited "160/192/224 at n=32": confirmed — for `n=32,w=4` (N(char0)=224) the F_q
counts are exactly `{96,160,192,224}` over `q∈{97,193,257,353,449,577,641,673,769,929}`, i.e. the
defect spread `{−128,−64,−32,0}`. The defect is genuinely q-dependent (not a constant offset),
which is the per-q `k_D` fingerprint.

## 3. The halo carriers are EXACTLY the cyclotomic-norm divisors (carrier-onset law)

For `n=16, w=6` (char-0 count = 0, so 100% of the count is defect). A set `S` is a halo carrier
**iff** `q | N(α)`, `α := e_2(S) ∈ ℤ[ζ_n]`, `N(α)=Res(Φ_n,α)` (the field norm). Verified:

- The set of "halo primes" (primes `q≡1 mod n` dividing some `N(α)`) is exactly the set of q with
  RISE defect; and the primes with **no** carrier are `q∈{401,449,577,…}` — which are **precisely**
  the q where the main probe measured `w=6` defect `= 0`. Two independent probes cross-validate.
- The actual count `N(F_q)` for `w=6` (the #distinct new e_1 at the canonical root) reproduces the
  RISE column exactly: `q=17→16, 97→32, 113→48, 193→16, 241→32, 257→16, 337→16, 353→16`.
- Galois subtlety (resolved): `q|N(α)` means α vanishes at **some** conjugate root; the deployed
  count evaluates at the **canonical** root `ζ=g^{(q−1)/n}`, so #(canonical halo sets) =
  #(any-conjugate)/(≈ φ(n)/conj-orbit) — the clean factor `8` for large q (`128 vs 16`) is exactly
  the `φ(16)=8` conjugates. The carrier **structure** is conjugation-equivariant.

> **Carrier-onset law (n=16,w=6, measured exact):** `S` becomes an e_2=0 solution mod q ⟺
> `q | N(e_2(S))`. The defect support = primes dividing a cyclotomic norm of a sparse signed
> root-sum α = e_2(S). This is the **halo-form** of the wall made concrete: the defect carriers
> are the prime divisors of `Res(Φ_n, e_2(S))`.

## 4. What this localizes (and why it does NOT close anything)

The defect = "does some sparse symmetric-function combination `α=e_2(S)` of n-th roots vanish mod q"
= **exactly** the cyclotomic-norm collision `q|N(α)` that every prior #407 lane bottoms out in
(`arklib-407-largesieve-avgq-refuted`: bad primes = `q|N(α)`; `…-equidistribution-defect…`: the
spurious mod-p collision). A09 sharpens it to the **count object** and shows:

1. The defect is **q-dependent** and **two-signed** — no constant offset; a worst-case `∀q` bound
   must control both saturation collisions (DROP) and norm-divisor carriers (RISE).
2. At prize scale `q ~ n·2^128` with `n=2^32`, `q ≫ all the small norms N(α)` for low w, so the
   RISE carriers are rare per fixed q — BUT the **worst-case-over-q** demanded by the grand
   challenge can always pick a `q | N(α)` for the largest realizable `N(α)` (`N(α)` reaches prize
   size, cf. the `n^{3.25}→n^{5.99}` excess-prime data on #407). So the magnitude of the *largest*
   `N(e_2(S))` over window-weight-w sets is the real lever, NOT the per-q average.
3. The DROP side caps at `N(char0)` and the RISE side is bounded by `q−1` (distinct values) — these
   are not the wall; the wall is the **count of distinct carrier e_1 at the adversarial q**, which
   the data shows can equal the full `N(char0)`-order (`w=6,q=113→48 = full n=16 w=4 count`).

**Honest status: PARTIAL / structural.** Proven nothing for `n=2^32`. What is established
numerically (n=16,32; n=64 w=4) and characterized exactly (n=16,w=6): the q-spread *is* the mod-q
defect; it decomposes into saturation (DROP) + halo carriers (RISE); the carrier support is exactly
`{q : q|N(e_2(S))}`. No closed-form law for the defect magnitude; no closure of the prize. This
names and dissects the defect object at the count level — the cleanest small-n picture of `k_D`
to date — and confirms the wall is the **largest cyclotomic norm `N(e_2(S))` over window sets**,
the same NVM/faithfulness wall the whole #407 frontier reduces to.

| axis | score | note |
|---|---|---|
| novelty | 7 | two-mechanism (saturation vs halo) split of the count defect + norm-divisor carrier law is new |
| insight | 8 | defect-support = `{q\|N(e_2(S))}`; cross-validated by two probes; q=401/449/577 zero-defect predicted by no-carrier |
| proximity | 7 | samples `k_D` directly at the count level; calibrates the worst-case-q lever |
| feasibility | 5 | measured to n=64(w=4); the magnitude-of-largest-norm question is the open residual |

**No closure claimed.** Cross-refs: `issue400-e2zero-singles-decomposition…`,
`issue400-smax-law-mu-minus-1…`, `deltastar-gate-as-equidistribution-defect…`,
`arklib-407-largesieve-avgq-refuted`.
