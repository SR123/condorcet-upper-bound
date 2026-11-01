1 NOVEMBER 2026 -- MANUSCRIPT AND COMPUTATIONAL-MATERIAL UPDATE

The canonical manuscript/main.pdf and main.tex are the 1 November review
draft: ten pages including references plus two mathematical appendix pages.
JOURNAL_PDF_VISUAL_REVIEW.json records the first upload, before its label was
shortened to "Review draft". REVIEW_DRAFT_LABEL_CHECK.json records the current
PDF/source hashes and the label-only correction; its other pages are unchanged.

The 21-page fully printed technical companion is preserved under
../../docs/full-proof-2026-11-01/. Its printed program was extracted and
compared with the executed source, including all 1160 coefficient values.
The included COMPANION_PRINTED_CHECKER_VERIFICATION.json belongs to that
unchanged companion, not to the shorter journal PDF.

The complete standalone Python checker is now at
../../ancillary/standalone/check_finite.py. FINITE_CHECK_RECEIPT.json and
finite_check.log record its earlier complete 1 November regeneration/check.
Its source hash is unchanged, so no new complete run is claimed for upload.
EXAMPLE_CHECKS.json records direct checks of all three paper examples.

The Lean proof, pins and all existing build records are unchanged. Every
base file was first matched to the public snapshot's Git blob hash, and
all Lean paths and proof records were checked again after the update.
The 29 October full independent build covers 326 project modules. The later
1 November correspondence summary covers typed restatements/interfaces
against verified proof objects; it is not a second full source rebuild.
See ../codex-independent-lean/ for the actual full-build/axiom evidence.

MANUSCRIPT_UPDATE_CHECKS.json records the manuscript/companion/program hashes,
1160 coefficient and nine correction comparisons, and the exact scope.
The current paper-to-Lean map is ../../docs/PAPER_LEAN_MAP.txt. The earlier
scope note is preserved at ../snapshots/2026-10-29/VERIFICATION_SCOPE.txt.

This is an authorised update of the public coauthor-review draft. No GitHub
release, DOI deposit, archival publication, Overleaf edit or email is included.
