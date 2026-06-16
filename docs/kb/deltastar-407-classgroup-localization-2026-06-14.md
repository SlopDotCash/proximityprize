# #407 — Class-group localization for a polynomial-p char-0→F_p transfer is a NO-GO (2026-06-14)

**Actionable A32** (merged 232-T09 / 334-T24). Pursue the O39 "class-group localization"
idea: can the ideal-class constraint on a bad prime `p` convert the *exponential* char-0→F_p
transfer threshold (`p > C(w,⌊w/2⌋)^{φ(n)}`, O49) into a *polynomial* one — closing the gap
"where the prize disproof side still breathes"?

**Verdict: NO-GO.** The class group is *vacuous* exactly where bad primes still occur, and
where it is large it makes the bad set *worse*, not rarer. The transfer threshold is governed
entirely by the **norm size** of the fiber equations — the route the height-gate no-go
(`deltastar-407-heightgate-nogo-2026-06-14`) already proved dead at the prize. Class-group
localization sees nothing the norm-size analysis does not.

Artifacts: `scripts/probes/sweep_A32_classgroup.py` (exact arithmetic, exit 0).

---

## 1. The object and the O39 hope

In-tree (`CyclotomicNormDefectThreshold.lean`, O49) the effective transfer is:
a `w`-subset `S ⊆ μ_n(F_p)` with `e_j(S)=0` for `j≤t` transfers to a char-0 vanishing
*whenever* `p > C(w,⌊w/2⌋)^{φ(n)}`, because the lift `α = e_j(S̃) ∈ ℤ[ζ_n]` has
`|N(α)| ≤ C(w,j)^{φ(n)}` and `p ∣ N(α)` if `α ≢ 0`. For `n = 2^μ`, `φ(n)=n/2`, this is
**exponential in n** — vacuous at the prize. The KKH26 disproof construction lives at
**polynomial** `p = Θ(n^β)`, `β∈[4,5]`, so the exponential vs polynomial gap is the
disproof's breathing room.

O39 (DISPROOF_LOG, 2026-06-09) localized the only object that could see inside the gap. A bad
prime `p` (one carrying an F_p excess solution absent in char-0) forces the relation ideal

>   `(α) = 𝔞·𝔭`,   `𝔭 ∣ p`,   `N(𝔞) ≤ budget`,

so **(i)** the prime `𝔭` must lie in the ideal class `[𝔞]^{-1}` (a `1/h`-density constraint by
Chebotarev over the Hilbert class field of `ℚ(ζ_n)`), and **(ii)** `𝔞𝔭` must admit a generator
inside the `{−2..2}` difference box (CDPR short-generator / log-unit geometry). The verified
class numbers (Washington tables, reproduced exactly in §A of the probe):

| μ | n | η=1/(n/2) | `h(ℚ(ζ_n))` | `h⁺` | `h⁻ = h/h⁺` |
|---|---|-----------|-------------|------|--------------|
| 4 | 16 | 1/8  | **1** | 1 | 1 |
| 5 | 32 | 1/16 | **1** | 1 | 1 |
| 6 | 64 | 1/32 | **17** | 1 | 17 |
| 7 | 128 | 1/64 (prize) | **359 057** | 1 | 359 057 |
| 8 | 256 | 1/128 (prize) | **1.045×10¹⁹** | 1 | 1.045×10¹⁹ |

The prize η = 1/64, 1/128 sit exactly at the fields where `h` explodes — the basis of the hope.

## 2. The two decisive measurements (probe `sweep_A32_classgroup.py`)

Object measured: 4-subsets `S ⊆ μ_n` with `e_1(S)=0`; **excess** = #(F_p solutions) −
#(char-0 solutions), i.e. the bad-prime defect. Exact integer arithmetic in
`ℤ[X]/(X^{n/2}+1)` (char-0) and `F_p` (primitive-root reduction).

**(C) The class constraint is VACUOUS where the defect lives.** In the `h=1` fields:

```
n=16 (h=1):  excess = 0 at every prime from p~n^2 upward.
n=32 (h=1):  excess > 0 at 5/8 primes near p~n^2 (max excess 64), then 0 from p~n^3 up.
```

In `ℚ(ζ_16)` and `ℚ(ζ_32)` **every ideal is principal**, so constraint (i) is identically
true — it imposes nothing. Yet polynomial-`p` bad primes still occur (n=32, p≈1024). A
constraint that is vacuous cannot be the mechanism that suppresses the very objects it is
supposed to control. The suppression that *does* happen (defect → 0 by `p~n^3`) is therefore
**not** class-theoretic.

**(D) Where `h` is large, the defect gets WORSE, not rarer.** Matched at the scale where bad
primes occur (`p ∈ [n², 4n²)`, where constraint (i) can bite):

```
n=32 (h= 1):  bad-fraction 0.478 (11/23),  avg excess-when-bad 34.9
n=64 (h=17):  bad-fraction 0.714 (10/14),  avg excess-when-bad 76.8
```

If the `1/h`-density class constraint were the dominant rarity, the `h=17` field should show a
**~17× thinner** bad set than `h=1`. Instead `h=17` has a *higher* bad-fraction and *larger*
excess. The bad set tracks `φ(n)` (more roots of unity ⇒ more candidate subsets), exactly
opposite to a `1/h` suppression. The class group is **not even monotone in the favorable
direction.**

**(C′) The decay that does occur is norm-size.** For n=32 the per-prime excess decays
monotonically with `p`:

```
p:    97  193  257  353  449  577  641  673  929 1153 1217 1249 1409 2113 2273 ...
exc: 288  128   96   96   96   96   96   64   64   32   64   32   32   32   32 → 0
     (~n^1.32 → ~n^2.23, then clean)
```

This is the signature of the **norm threshold**: a fixed integer `N(α)` with `|N|≤(2r)^{φ(n)}`
stops being divisible by `p` once `p > |N|`; larger `p` kills more of the spurious congruences.
The defect vanishes near the (object-specific, here small-`w`) norm bound, with **no dependence
on `h` whatsoever** — it is identical in `h=1` and `h=17` fields.

## 3. Why the class-group route *cannot* close the gap (the structural reason)

Three independent obstructions, the last one fatal regardless of any class computation:

1. **Splitting kills constraint (i) at the prize.** Prize primes satisfy `n ∣ p−1`, so
   `f = ord_n(p) = 1` and `p` **splits completely** into `φ(n)=n/2` primes `𝔭`, each of
   norm `p`, one in *every* residue degree-1 slot. The 334-T24 "residue-degree splitting law"
   (`v_p(N) ≡ 0 mod ord_n(p)`) is then vacuous (`ord_n(p)=1`). Because `p` populates *all*
   `φ(n)` prime slots above it, the relevant question is not "does `p` lie in a class" but
   "does *some* factor `𝔭_i` of `p` lie in `[𝔞]^{-1}`". The `n/2` factors form a single Galois
   orbit (`Gal ≅ (ℤ/n)^×` acts transitively on primes above a completely-split `p`), so the
   classes `{[𝔭_i]}` spread over a Galois orbit in the class group. With `n/2 = 2^{29}`
   candidate factors against `h ≈ 2^{19}` classes at the prize, the orbit is large relative to
   `h`, so whether *no* factor hits the target class is an orbit-coverage question, not a clean
   `1/h` rarity. Empirically (§D) the net effect is *no* suppression at all (larger `h` ⇒
   *more* bad primes, tracking `φ(n)`); the "1/h rarity" intuition does not survive the
   `n/2`-fold complete split.

2. **The box (constraint (ii)) is the height-gate wall, already dead.** Even granting a class
   constraint, `𝔞𝔭` must have a generator in the `{−2..2}^{deg}` box. The height-gate no-go
   proved `max_S |N(Σ_{i∈S} ζ^i)| ≈ (#S)^{n/4}` grows super-exponentially and crosses
   `p~2^128` already at `n≈128`; the explicit block `S={0,…,n/2−1}` has `|N| = 2^{n/2−1}`.
   So at the prize the box is *enormous* relative to `p`: short generators are abundant, not
   rare. Constraint (ii) is the norm-size wall in disguise, and it goes the wrong way.

3. **The prize is WORST-CASE over primes; `1/h` is an AVERAGE.** Even a perfect `1/h`-density
   Chebotarev statement says bad primes have density `1/h` — i.e. they *exist* (infinitely
   many, by Chebotarev's lower bound). The grand challenge demands the transfer hold for
   **every** prime `p` of prize shape (worst-case). A positive density of bad primes is a
   *refutation* of a worst-case transfer, not a tool for it. The class group can at best make
   bad primes *sparse*, never *absent* — and sparse-but-present is exactly what the KKH26
   disproof needs (`∃ p` near capacity), and exactly what the prize *upper* half cannot
   tolerate.

Together: the class-group constraint is satisfiable for ~every prize prime (1), the box is
huge so generators are abundant (2), and worst-case ≠ average so even a real `1/h` rarity is
the wrong shape (3).

## 4. Honest status and what survives

- **NO-GO** for the stated goal (polynomial-p transfer via class-group localization). The
  measurements (C),(C′),(D) are exact small-`n` evidence; the structural argument §3 is the
  reason it generalizes. This *confirms and retires* the O39 research direction on the
  EXACTNESS side, consistent with `QuotientPerPrimeInstantiation.md §4` already retiring it on
  the lower (counting) side: "O39's class-group/short-generator program … retired for the
  lower half … relevant only to the exact-image question as such" — and now the exact-image
  question, too, shows the class group is not the lever.

- **What survives (true facts, not the lever):** (a) the **norm-size threshold is the real
  governor** of char-0→F_p transfer, and it is provably the BGK/Paley wall at the prize
  (height-gate no-go); (b) the **complete-splitting + residue-degree law** (334-T24/O131-A2)
  is a genuine structural theorem about *which non-prize primes* are bad (`v_p(N)≡0 mod f`),
  but it is vacuous for prize primes (`f=1`); (c) the bad-prime defect tracks `φ(n)`, i.e. the
  number of roots of unity — the same object as the additive-energy / lacunary-count crux,
  reconfirming the consolidated picture that *everything reduces to the one open
  thin-subgroup BGK wall.*

- **The disproof side still breathes — but not through the class group.** Polynomial-`p` bad
  primes are real and abundant (C),(D); the KKH26 construction exploits norm-size, not class
  structure. The exponential→polynomial gap is closed *against* a worst-case transfer (bad
  primes are dense), which is consistent with the prize being open on the *upper* half, not a
  route to closing it.

## 5. Repro

```
python scripts/probes/sweep_A32_classgroup.py   # exact, exit 0; sections (A)..(D)
```

Class numbers cross-checked vs Washington, *Introduction to Cyclotomic Fields* (in-tree at
`~/Desktop/math/1.pdf`, O49 inventory). Norm-size context:
`docs/kb/deltastar-407-heightgate-nogo-2026-06-14.md`,
`ArkLib/.../Frontier/CyclotomicNormDefectThreshold.lean`,
`ArkLib/.../Frontier/BlockSumNormNoGo.lean`. Lower-half retirement:
`ArkLib/.../QuotientPerPrimeInstantiation.md`.
