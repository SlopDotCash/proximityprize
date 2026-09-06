# W11 missing runtime dependency restored

The corrected W11 n=16 replay failed before computation with `ModuleNotFoundError: probe_466_windowed_extremal`. The retained probe imports its Setting and interpolation/search helpers. Commit 8416cfb0f468e29f89360fcae9655fe85c3d29f9 removed the helper during the earlier bulk cleanup.

`scripts/probes/probe_466_windowed_extremal.py` is restored byte-for-byte from that commit's parent. Its only nonstandard dependency is NumPy and its standalone experiment is guarded by `__main__`. W11 import and construction of Setting(8,2,17) now pass. The restored standalone experiment and its prose are not newly certified; the restored file is retained because W11 requires its runtime API.

This adds one required helper outside the original 421-artifact retention inventory. Of that inventory, 420 remain and one was removed; the restored dependency is additional. Completed original-unreferenced coverage remains 57/92. The failed replay did not produce a new numerical result; a fresh replay is needed.
