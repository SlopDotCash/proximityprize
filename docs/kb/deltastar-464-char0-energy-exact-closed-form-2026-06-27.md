# Exact char-0 additive energy of μ_{2^μ} — closed form + Bessel GF (2026-06-27)

A clean **exact** evaluation of the characteristic-zero additive energy of the smooth subgroup,
sharpening the in-tree `E_r ≤ (2r−1)!! n^r` bound (`EnergyRelationAntipodal.energy_relation_count_antipodal`)
to an exact value. This fills the "remaining combinatorial half" that the
`EnergyRelationAntipodal` docstring explicitly flags as open.

## Result

Let `n = 2^μ`, `μ_n ⊂ ℂ^×` (or any `CharZero` field) the `n`-th roots of unity, and

```
E_r^(0) = V_{2r} := #{ (u_1,…,u_{2r}) ∈ μ_n^{2r} : u_1+…+u_{2r} = 0 }
        = #{ (a,z) ∈ μ_n^r × μ_n^r : Σ a_i = Σ z_j }    (char-0 additive energy; bijection u=(a,−z)).
```

Then, with `h = n/2`:

```
   V_{2r}  =  Σ_{m_1+…+m_h = r,  m_k ≥ 0}  (2r)! / ∏_{k=1}^{h} (m_k!)²
          =  (2r)! · [t^r]  I_0(2√t)^{h}                      (modified Bessel generating function),
```

and

```
   V_{2r}  ≤  (2r−1)!! · n^r  =  Wick,        with equality iff r ≤ 1.
```

## Why (proofs)

**Closed form.** By the Lam–Leung theorem for `2^μ`-th roots (in-tree:
`LamLeungMultisetAntipodal.multiset_antipodal_iff`), a multiset of `2^μ`-th roots sums to `0`
iff it is *antipodally balanced*: `count(ω) = count(−ω)` for every `ω`. Group `μ_n` into its
`h = n/2` antipodal pairs `{ω_k, −ω_k}`. A balanced `2r`-tuple is determined by, for each pair
`k`, a multiplicity `m_k` (the number of `ω_k`'s, which equals the number of `−ω_k`'s), with
`Σ m_k = r`; the number of ordered tuples with that profile is the multinomial
`(2r)! / ∏ (m_k! · m_k!)`. Summing over profiles gives the closed form. Since
`Σ_m t^m/(m!)² = I_0(2√t)`, the generating function is `I_0(2√t)^{h}`.

**Wick bound (elementary, NO Lam–Leung).** Since `m_k! ≥ 1`, `(m_k!)² ≥ m_k!`, so
`∏ 1/(m_k!)² ≤ ∏ 1/m_k!`, hence
```
   V_{2r}/(2r)! = Σ_{Σm_k=r} ∏ 1/(m_k!)²  ≤  Σ_{Σm_k=r} ∏ 1/m_k!  =  h^r / r!
```
by the multinomial theorem (`Σ_{Σm_k=r} r!/∏ m_k! = h^r`). Therefore
`V_{2r} ≤ (2r)!/r! · h^r = (2r−1)!!·(2h)^r = (2r−1)!!·n^r`. ∎

## Numerical verification (3 independent routes)

1. **Direct complex brute-force** over actual `n`-th roots (n=4,8; r=1,2,3): `V_4(μ_4)=36`,
   `V_6(μ_8)=5120`, … all match the closed form exactly.
2. **Wraparound-free mod-p** (two huge primes `p≡1 mod n` agree ⇒ char-0 value): matches for
   all stable rows, e.g. `V_8(μ_16)=4 649 680`, `V_6(μ_32)=446 720`.
3. **Closed-form DP** (Bessel-coefficient convolution): matches both.

Exact small table (`V_{2r}` in falling-factorial form):
`V_2 = n`,  `V_4 = 3n(n−1)`,  `V_6 = 15n³ − 45n² + 40n = 15·n^{(3)} + 10·n^{(1)}`.

Wick deficit `(Wick − V_{2r})/Wick`: at `r=2`, exactly `1/n` (e.g. 12.5% at n=8, 3.1% at n=32);
grows with `r` (33% at n=8,r=3). So the char-0 energy sits strictly *below* Wick, and the gap is
itself `Θ(Wick · r²/n)` for small `r`.

## Significance for the δ* wall

The DC-subtracted nontrivial-period energy is `S_r = Σ_{b≠0} η_b^{2r} = p·E_r − n^{2r}`, and
`E_r = V_{2r} + W_r/p` where `W_r` counts the mod-p **wraparound** solutions (the only part not
captured char-0). The prize bound `B ≤ √(2n ln p)` needs `S_r ≤ p·Wick` for `r ≲ ln p`. Substituting
the now-exact char-0 value:

```
   S_r ≤ p·Wick   ⟺   W_r  ≤  p·(Wick − V_{2r})  +  n^{2r}.
```

So the entire $1M floor is now an **exact** statement about wraparound alone, with a precise budget
`p·(Wick − V_{2r}) + n^{2r}` — and the char-0 side is closed in closed form. The wall did **not**
move (W_r is the same Paley/BGK obstruction, see `deltastar-OPEN-MATHEMATICS-2026-06-27.md`), but it
is now isolated to a single non-negative count with an exact target, and the char-0 half is a clean
finite identity. This is a sharpening, not a closure: `W_r > 0` past the onset (`n=256` numerics:
`R_r` crosses 1 at `r=4`), and bounding it remains the open phase-cancellation problem.

## Landable Lean increment

`energy_relation_count_antipodal` already proves the forward (antipodal-balance) direction. The new
content is (i) the exact multinomial closed form for the balanced-tuple count, and (ii) the
elementary `≤ (2r−1)!! n^r` bound on that multinomial sum (no Lam–Leung needed for (ii)). Brick:
`charZeroEnergy_eq_multinomialSum` (needs the in-tree Lam–Leung + a `Nat.multinomial` fiber count)
and the self-contained `multinomialSum_le_wick`.
