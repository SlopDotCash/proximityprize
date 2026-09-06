# Retention aggregate correction

The reconstructed baseline at commit `58cc1f0e6f3645e2e78e9e4b15c16729dcd17753` contains 421 files and 92 without filename references. Its immutable 92-path list is recorded in `probe-retention-original-baseline-2026-09-06.json`.

The earlier G87V n=16 audit incorrectly counted `_out_466_g87v_census_rank_n16.txt` toward this group. That path is absent from the 92-path list. Its numerical replay is still useful, but it cannot increment this aggregate. Subtract one from the historical aggregate beginning with that review, including later totals of 61, 63 and 64.

The latest corrected total after the G101F stage-three review is 63 of 92, with 29 remaining. This includes both the transfer source and output, which are in the original group. Historical dated audit totals describe their original bookkeeping; this correction supersedes those totals. Neither filename references nor inclusion in a later audit alone establishes semantic completion.

The full G87V archive is in the original group and remains pending its separate complete replay. No source evidence has been deleted by this accounting correction.
