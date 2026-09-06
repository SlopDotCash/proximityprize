# Issue 2: documentation outside the Lean source tree

All 47 Markdown files formerly under `ArkLib/` are removed from that tree.
Research notes now live under `Research/ProximityPrize/kb/archive/`; the research
agent guide lives beside the research code, with `CLAUDE.md` linking to `AGENTS.md`.
The Binius reversal diagnosis is retained under `docs/kb/audits/`, and the two
short library-extension READMEs are consolidated in `local-extensions.md`.

The root disproof log was an exact byte-prefix extension of the ProximityGap
copy: it contained all 4,591,493 bytes of that copy plus a 385-byte section on
PR #53's region-middle counterexample. The complete version is now
`Research/ProximityPrize/DISPROOF_LOG.md`; the duplicate is deleted. No log entry
is lost. Path references and two mathematical expressions misread as Markdown
links were reformatted after consolidation.

Incoming links, root guides, and distributed agent instructions use the new
locations. The documentation checker now scans Research and rejects Markdown
under ArkLib; regression tests cover both boundaries. This structural change
preserves the archived research notes. Their semantic distillation and removal,
the remaining knowledge-corpus consolidation, and issue #2's proof work are
separate unfinished requirements.
