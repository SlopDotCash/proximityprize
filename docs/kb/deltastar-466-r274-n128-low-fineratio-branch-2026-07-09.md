# #466 R274 n=128 low-fineRatio branch

## Question

R273 showed that the largest moderate row has lower fineRatio:

```text
p=231169, fineRatio=0.734, mass=0.246187.
```

This probe isolates the moderate low-fineRatio branch and asks whether it is a
stable third obstruction or a small finite family.

## Command

```bash
python3 scripts/probes/probe_r274_n128_low_fineratio_branch.py \
  --min-index 512 --max-index 12000 --chunk 4096 \
  --top-per-row 4 --min-fine128 10 --top 40
```

## Result

```text
rows=926
moderate=567
moderate_mass=4.41504521
```

FineRatio bands:

```text
[0.00,0.75): count=48  mass=0.360635 worstMass=0.246187 at p=231169
[0.75,0.85): count=176 mass=0.764966 worstMass=0.078839 at p=911233
[0.85,0.90): count=134 mass=1.009844 worstMass=0.129143 at p=288257
[0.90,0.95): count=133 mass=1.098813 worstMass=0.076779 at p=183041
[0.95,inf):  count=76  mass=1.180787 worstMass=0.088208 at p=222337
```

The low band is dominated by one row:

```text
p=231169 M=1806 mass=0.24618668 fineRatio=0.734
```

After that, the largest low-band rows are much smaller:

```text
p=303617  M=2372 mass=0.00613238 fineRatio=0.696
p=393473  M=3074 mass=0.00553216 fineRatio=0.726
p=577537  M=4512 mass=0.00499089 fineRatio=0.741
p=514561  M=4020 mass=0.00413705 fineRatio=0.714
p=535937  M=4187 mass=0.00374233 fineRatio=0.725
```

Low-band rank signature:

```text
median bestRank = 2
median worstRank = 5936.5
```

So these are top child plus extremely deep tail child events.

## Conclusion

The low-fineRatio branch is not a large new obstruction in this scan.  It is
dominated by a single finite exceptional row `p=231169`; after removing that
row, the remaining low-band masses are at the `0.006` level and decay with the
index window.

This suggests the next proof split:

```text
moderate low-fineRatio:
  finite exception p=231169,
  plus a small top-vs-deep-tail residual;

moderate high-fineRatio:
  conditional top-tail certificate;

inherited branch:
  recursive resonance tree.
```

The immediate next test should certify whether the post-`p=231169` low-band
tail stays small at wider n=128 windows and then package it as a finite
exception plus monotone tail claim.
