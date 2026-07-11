# G169 Stepanov thickness fence, 2026-07-11

Axiom-clean arithmetic fence for the G169 double-deletion route.  At production shape
`p = 3*m + 1`, the Stepanov hypotheses `2*m <= B^3` and `m*B <= p` are incompatible once
`m >= 32`: the field-size condition forces `B <= 3`, while the multiplicity condition needs
`B^3 >= 64`.  In particular there is no admissible `B` at the certified `m = 2^30` cell.

Meaning: the G169 thin-subgroup Stepanov theorem remains valid, but its claimed `|G|^(1/3)`
saving is vacuous at the thick index-three production modulus.  A uniform shifted-fiber route
can only give a constant-factor improvement there; any further gain must be cancellation or
averaging, i.e. back at the BGK/Paley object.
