# #466 R267 n=128 ancestor resonance taxonomy

## Question

R266 showed that current-level filtering is too weak at n=128: a row can have
exact `MGF128 < 2` and still carry a large persistent coherent-path mass.  The
next hypothesis was recursive:

```text
dangerous n=128 paths descend from already-dangerous n=64 resonance ancestors.
```

This probe labels each high n=128 coherent path by its selected n=64 ancestor
and measures whether ancestor thresholds in `X64` or `fine64 = X64 - lift(X32)`
cover the dangerous mass.

## Command

```bash
python3 scripts/probes/probe_r267_n128_ancestor_resonance_taxonomy.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-per-row 4 --min-fine128 10 --top 25
```

## Result

The scan found:

```text
rows=233
coherent=231
max_mass=0.24618668
max_x128=27.390895
max_fine128=24.281529
```

Ancestor-threshold coverage:

```text
fine64 >=  8: captured=69 mass=0.985082 worstMass=0.181033
fine64 >= 10: captured=33 mass=0.623684 worstMass=0.181033
fine64 >= 12: captured=10 mass=0.401014 worstMass=0.181033
fine64 >= 14: captured=5  mass=0.332706 worstMass=0.181033

X64 >= 14: captured=88 mass=1.364626 worstMass=0.246187
X64 >= 16: captured=38 mass=0.686827 worstMass=0.181033
X64 >= 18: captured=17 mass=0.511581 worstMass=0.181033
X64 >= 20: captured=10 mass=0.433721 worstMass=0.181033
```

The two largest modes are different.

### Mode A: amplified moderate ancestor

The largest n=128 path is not a high-fine n=64 ancestor:

```text
p=231169, M128=1806
mass128=0.24618668
X128=24.39, fine128=10.32
X64=14.07, fine64=3.43
MGF128=1.753, MGF64=1.403
```

This row defeats a recursive `fine64` filter: its ancestor is moderate in
fine-layer terms, but the n=128 join amplifies it.

### Mode B: inherited high-fine ancestor

The expected recursive-resonance rows are present:

```text
p=665857, M128=5202
mass128=0.18103322
X128=27.39, fine128=23.52
X64=29.51, fine64=14.74
MGF128=1.686, MGF64=2.183

p=697601, M128=5450
mass128=0.130860
X128=26.28, fine128=24.28
X64=34.06, fine64=18.69
MGF128=1.679, MGF64=2.218
```

These are caught by high `fine64` and high `X64` thresholds.

## Conclusion

The simple recursive hypothesis is refuted:

```text
dangerous n=128 coherent paths are not only inherited high-fine n=64 paths.
```

There are at least two modes:

1. inherited high-fine ancestors, which a recursive resonance tree can catch;
2. amplified moderate ancestors, where the new top-level join creates the
   dangerous n=128 path.

The next theorem-shaped split should separate these modes explicitly:

```text
large n=128 coherent path
  -> either ancestor X64/fine64 is already resonant,
  -> or the new join has a large top-level amplification ratio.
```

The second branch is now the live target: bound large one-step amplification
from moderate ancestors, probably by a pair-angle/large-child counting theorem
rather than by current-level MGF or ancestor fine thresholds alone.
