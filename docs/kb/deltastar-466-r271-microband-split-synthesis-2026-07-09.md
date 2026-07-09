# #466 R271: micro-band split synthesis

Date: 2026-07-09

## Current micro-band theorem

The direct target from R263/R264 is:

```text
TrimFiveMicroBand:
  after deleting the top five quotient values,
  S(0.75) <= 612 / 1485
```

for the main lane.

## Split

R266-R270 replace the knife-edge uniform theorem with:

```text
Finite branch:
  512 <= M < 1536
  checked by CSV certificate, 465 rows, 0 failures.

Large branch:
  M >= 1536
  prove the softer cap S(0.75) <= 0.4055.
```

Evidence:

- finite branch worst: `S=612/1485`, micro slack `0.000066`;
- large branch worst through `M=8000`: `S=0.405233` at `M=1567`;
- high-index stratified sample `8001 <= M <= 20000`: worst sampled
  `S=0.396309`.

## Remaining analytic subgoal

The micro-band route now needs a large-index vertical distribution theorem:

```text
M >= 1536 => #{x in R_5 : x >= 0.75} <= 0.4055 M.
```

This has about `0.0066` survival slack relative to the finite-branch global
cap `612/1485 ~= 0.412121`.
