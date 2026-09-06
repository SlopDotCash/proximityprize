# Retained probe dependency recovery

A static scan of Python imports beginning with `probe_` or `_skeptic_` found two additional missing local modules after the W11 repair. `probe_r386_unique_root_strata.py` imports `build_n3` from `probe_r305_complete_census.py`; `probe_r383_n8k4_e2_exhaustive.py` imports field and projective-enumeration helpers from `probe_r383_half_radius_n8k4_exhaustive.py`.

Both helpers are restored byte-for-byte from the parent of bulk deletion commit 8416cfb0f468e29f89360fcae9655fe85c3d29f9. Their standalone experiments are guarded by `__main__`. Both retained consumers now import successfully. The companion JSON records the recovered hashes. This verifies dependency availability, not complete census results or historical mathematical conclusions.

Together with W11's helper, three files are restored outside the original 421-artifact inventory. Of that original inventory, 420 remain and one was removed. Completed original-unreferenced reviews remain 57/92. The prefix-based scan does not cover arbitrary dynamic imports or differently named local modules.
