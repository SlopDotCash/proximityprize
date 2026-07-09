# #466 R286 n=128 low-fineRatio continuation

## Question

R274 isolated the n=128 moderate low-fineRatio branch:

```text
moderate := fine64best < 8 and X64max < 16
low-band := fine128 / X64best < 0.75
```

On `M <= 12000`, that branch was dominated by one finite exceptional row:

```text
p=231169 M=1806 mass=0.24618668 fineRatio=0.734
```

The next question was whether this is a genuine finite exception, or whether a
second large low-band row appears in the next window.

## Command

```bash
python3 scripts/probes/probe_r286_n128_low_fineratio_stream.py \
  --min-index 12001 --max-index 20000 \
  --progress-every-primes 10 --progress-every-seconds 20 --top 24
```

The script is intentionally streaming: it reports progress and keeps only the
low-band leaderboard, so wider windows can be interrupted without losing the
main evidence.

## Result

```text
R286 n=128 low-fineRatio stream M=[12001,20000] fineRatio<0.75
primes=1114 candidateRows=1542 moderateRows=891 lowRows=99
lowMass=0.11101839 maxLowMass=0.00178958
lowMassNoExceptions=0.11101839 maxLowMassNoExceptions=0.00178958
```

Largest low-band rows in the continuation window:

```text
mass       fRatio  X128    F128    X64max  F64best  bestR  worstR  M       p
0.00178958 0.7476  12.458  11.202  14.983  4.185    2      6656    12584   1610753
0.00166197 0.7486  12.538  11.264  15.047  0.171    2      7197    13824   1769473
0.00164052 0.7257  12.267  11.227  15.469  4.352    4      8137    13089   1675393
0.00163479 0.7236  12.433  11.397  15.751  3.349    1      8532    13691   1752449
0.00159038 0.7459  12.888  11.606  15.561  7.468    2      8202    15770   2018561
```

## Interpretation

No second heavy low-fineRatio obstruction appeared.  The continuation maximum is
smaller than the R274 finite exception by a factor of about `137.57`:

```text
0.24618668 / 0.00178958 = 137.56...
```

The rank signature persists: a top n=64 child is joined to a very deep aligned
tail child (`bestRank` usually `1..4`, `worstRank` in the thousands).  The low
branch therefore looks like:

```text
finite exceptional row p=231169
+ diffuse top-vs-deep-tail tax with individually tiny rows
```

This supports the next proof target:

```text
LowFineRatioTax(128):
  after excluding p=231169, a rowwise bound of about 0.002
  plus a counting/tail envelope for top child + deep aligned partner events.
```

It also refines the branch split from R274:

```text
moderate low-fineRatio:
  finite exception p=231169,
  plus top-vs-deep-tail tax;

moderate high-fineRatio:
  top-tail certificate near the 0.75 boundary;

inherited:
  recursive resonance tree.
```

