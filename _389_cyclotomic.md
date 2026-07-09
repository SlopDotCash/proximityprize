**The EXACT smooth-domain cubic list size — reduced to ONE character sum (#389)**

Following the cubic orchard identity (`cubic_list_eq_zeroSum`: list of `x³` at `k=2,a=3` = zero-sum triple count, every domain), here is the **exact closed form on every smooth (multiplicative-subgroup) domain**, reducing the list size to a single character-sum quantity.

**The domain-general assembly** (probe `probe_zerosum_triple_assembly.py`, verified at all instances below — `scale`/`diag`/`div6` each independently confirmed): for a multiplicative subgroup `G ≤ Fₓ` of order `n`,

```
6 · #{unordered {a,b,c} ⊆ G distinct : a+b+c = 0}  =  n·M  −  3n·[−2 ∈ G]
```

where `M = #{y ∈ G : −(1+y) ∈ G}`, via three exact steps:
1. **scaling bijection** `T_ord := #{(a,b,c)∈G³ : Σ=0} = n·M` (fix `a`, scale `(b,c)↦(b/a,c/a)` onto `b'+c'=−1`);
2. **diagonal correction** `#ordered-distinct = T_ord − 3n·[−2∈G]` (a coincidence `a=b` forces `c=−2a∈G`);
3. **÷6** to unordered.

So the cubic list size on **any** smooth domain is `(n·M − 3n·[−2∈G])/6` — exact, character-sum-free in the structural part, reducing the whole question to the single quantity `M`.

**The cyclotomic evaluation of `M` on QR domains** (new Lean module `QRShiftPairCount.lean`, axiom-clean — proven WITHOUT character theory via the conic `y² = 1 + x²`):
- `card_units_squares`: `2·#QR* + 1 = q` (squaring is 2-to-1).
- `conic_card`: the conic `{y²=1+x²} ≅ Fˣ` via `(x,y)↦y−x` (since `(y−x)(y+x)=1`) — exactly `q−1` points.
- `qr_shift_count`: splitting the conic into `x=0` (2 pts), `y=0` (2 pts, needs `−1∈QR`) and the rest (4-to-1 via `u=x²`): **`4·#{u : u,u+1 ∈ QR*} + 5 = q`**, i.e. `M = N = (q−5)/4`, the order-2 cyclotomic number.

Combining: on a QR domain (`q≡1 mod 4`, `n=(q−1)/2`), the cubic list size is
```
n(q−5)/24    if q ≡ 5 (mod 8)    [−2 ∉ QR]
n(q−17)/24   if q ≡ 1 (mod 8)    [−2 ∈ QR]
```
the `mod 8` split being exactly whether `−2 ∈ QR` (supplementary quadratic reciprocity). **Verified 13/13** at `q = 29,37,41,53,61,73,89,97,101,109,113,137,149`; the domain-general form verified at 17 further non-QR subgroups (`q=41,61,73`, orders `5..36`).

**Status.** Tier 1 (`cubic_list_eq_zeroSum`) and Tier 3 (`qr_shift_count`, the cyclotomic core) are formalized axiom-clean. Tier 2 (the `G³`-scaling assembly above) is derived + probe-verified at 30 instances; its Lean formalization (Finset bijection over `G²` + diagonal + ÷6) is the next brick and would close the exact smooth-domain cubic list size end-to-end.

**Honest scope.** This is the EXACT list size of the *cubic word*. Over `F_q` the cubic is **not** globally extremal (the true orchard maximum exceeds it — `25 > 20` at `(31,15)`), so the per-word answer is exact while the worst-case orchard number over all words remains the open extremal core, bracketed `[best-cubic-fiber, ⌊n(n−1)/6⌋]`.
