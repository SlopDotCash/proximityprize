# G104 primitive-concentration factorial no-go

Date: 2026-07-11
Issue: #466
Status: exact production-prime countercertificate; CORE remains open / on BGK

## Claim audited

The G104 scoping probe proposes a single all-depth input

```text
max_a #{primitive k-tuples of mu_n summing to a} <= 4 n^(2/3),
3 <= k <= 108,
```

where primitive means that no proper nonempty submultiset sums to zero. It claims this closes the `(2,s-2)` padded-collision chain at every `s=5,...,110`.

This is false already at `s=13`, `k=s-2=11`, in the first certified prize field.

## Exact countercertificate

Use the certified modulus and subgroup generator from `_PrizeShapePrimeP30.lean`:

```text
p = 365375409332725729550921208179070755120141565953,
n = 2^30,
g = 303645430271030343624574566109998498685964493478,
ord(g)=n.
```

The eleven elements

```text
g^0, g^1, ..., g^10
```

have all `2^11=2048` subset sums distinct modulo `p`. In particular, no nonempty subset sums to zero. Therefore every permutation of these eleven distinct elements is a primitive ordered 11-tuple, and all permutations have the same sum. One primitive sum-fiber consequently has cardinality at least

```text
11! = 39,916,800.
```

G104's actual sharp-envelope requirement at `s=13` is

```text
floor(219!! / (C(110,13)^2 * 97! * (2^30)^2))
  = 14,207,588.
```

Thus the explicit primitive fiber exceeds the binding threshold by factor

```text
39,916,800 / 14,207,588 = 2.809540...
```

It also exceeds the proposed uniform majorant

```text
4 n^(2/3) = 4 * 2^20 = 4,194,304
```

by factor `9.5175`.

The certificate is reproduced by:

```bash
python3 scripts/probes/probe_466_g104_primitive_concentration_factorial_no_go.py
```

The script verifies subgroup membership, all 2048 subset sums, the common sum, and both exact integer inequalities.

## Structural reason

This is not a small-prime artifact or a random/DC asymptotic. It is the unavoidable ordering multiplicity of a literal zero-sum-free support. Once a primitive support of size `k` exists, its `k!` permutations lie in one ordered sum-fiber. At production, a greedy subset-sum argument already guarantees zero-sum-free supports for modest `k` because `|mu_n|=2^30` greatly exceeds the number of forbidden subset sums. The explicit certificate avoids needing that general existence theorem.

Therefore a uniform `O(n^(2/3))` bound on **ordered** primitive tuple fibers cannot hold through depth 108. Any viable concentration input must quotient by permutations or normalize by `k!`, then reinsert the factorial exactly in the G86 reconstruction inequality. Doing so changes the binding inequality: G104's claimed threshold has no spare `k!` factor at `s=13`, so the stated `(2,s-2)` chain does not close after normalization.

## Literature / frontier integration

- FS15-FS18 already show fixed-depth resultant control reverses at prize depth. This no-go is complementary and finite: the failure occurs at depth 11 from permutation multiplicity before any asymptotic random mod-p bulk is invoked.
- G158/G159 correctly identify `(t!)^2` as the exact ordered-word multiplicity above balanced subset cores. G104 omitted the analogous `k!` cost when turning primitive supports into ordered completion fibers.
- G154's subset-core recurrence remains valid because it works with unordered finite supports. The failure is specifically the proposed weld from an unordered primitive notion to the ordered `maxN_s` concentration quantity without paying ordering multiplicity.
- ANT46 and low-rung projective classification remain useful. They cannot justify an all-depth ordered `4n^(2/3)` family.

## Binding conclusion

The G104 all-depth primitive-concentration family is refuted at the first certified prize prime. The corrected survivor is an unordered/normalized primitive-support bound with explicit factorial accounting. At `s=13`, the factorial alone already exceeds the sharp G86 budget, so this particular split chain is closed, not merely missing a proof. No Paley/BGK cancellation is consumed by the countercertificate; CORE remains open / on BGK.
