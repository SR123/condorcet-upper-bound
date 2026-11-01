IMPROVED UPPER BOUNDS ON THE SIZE OF CONDORCET DOMAINS
Pavlos Moros and Søren Riis
Current review draft, 1 November 2026

START HERE
manuscript/main.pdf       Current paper: 10 pages including references + 2 appendix pages
manuscript/main.tex       Complete journal-paper LaTeX source
ancillary/standalone/     Complete exact single-file Python checker and instructions
docs/full-proof-2026-11-01/main.pdf   Fully printed 21-page technical companion
docs/full-proof-2026-11-01/main.tex   Its source, with all code/data printed
docs/PAPER_LEAN_MAP.txt   Map using the CURRENT paper's numbering
lean/                    Unchanged complete Lean project: 326 modules and pins
verification/            Precise scope, dated build and checking records
REVIEW_GUIDE.txt          Suggested starting points for independent review

VERSIONS
The current paper is the revised journal review prepared on 1 November.
It defines domains by never-conditions, explains all principal notation,
contains three small examples, highlights the exact fibre identity and
explicitly refers to Lean and computational verification. The mathematical
appendix proves the voting equivalence and every injection collision case.
The full finite coverage proof, data and complete program listing are in
the separate technical companion and the standalone checker.

The earlier checked 29 October snapshot remains accessible at:
https://github.com/SR123/condorcet-upper-bound/tree/0d5dd168854b208d8436ea685921aa03d7c42200
Its eight-page manuscript and older certificate supplement use different
numbering. supplement/ is retained as that earlier certificate supplement;
it is not required to read the current paper. Old preparation-stage claims
about Overleaf identity and GitHub placeholders describe the old snapshot,
not the new manuscript. No Overleaf edit is part of this GitHub update.

PAPER-TO-LEAN MAP: THEOREM 1.1
All names below have prefix CDCert.Main. in lean/CDCert/Main.lean.
The formal functions are the actual maximum sizes Condorcet.f and Condorcet.h.

General recurrence                    general_recurrence
General geometric bound               general_geometric
Peak-pit recurrence                   peak_recurrence
Peak-pit geometric bound               peak_geometric
General root limit and upper bound    general_limit
Peak-pit root limit and upper bound    peak_limit
Polynomial correction                 general_polynomial_correction

The first four theorems assume n >= 3; the last three have no extra premises.
There is no unproved density estimate, injection, enumeration assumption or
common-axis hypothesis in these final statements. The semantic definitions
quantify over all odd voter profiles, allowing repetitions, of actual strict
total orders. The proved value-restriction equivalence identifies them with
the combinatorial definition used in the current paper.

The updated supporting-result map, exact declaration names and scaling are
in docs/PAPER_LEAN_MAP.txt. Key declarations include:
- Condorcet.deletion_gap_adjacency_identity (Lemma 3.1).
- Condorcet.IsFull.component_from_fixed (Lemma 4.1).
- Condorcet.IsFull.component_inF and sum_components_deletionSum (Proposition 4.2).
- CDCert.FreeLocked.free_le_locked (Lemma 5.2 and Appendix A.2).
- CDCert.Recurrences.gap_inequality (Corollary 5.3).
- CDCert.K6.finite_lemma (Lemma 6.1 and the receiver argument in Section 7).
- CDCert.Bridge.InF.density (Proposition 8.1).

VERIFICATION SCOPE
The 326 Lean source modules, configurations, pins and existing proof records
are byte-for-byte unchanged by this update. Every source was independently
compiled on 29 October, including the final clarified-source recompilations;
the final 20-result statement/axiom check passed. Only propext,
Classical.choice and Quot.sound appear. There are no sorry/admit placeholders,
custom axioms or native_decide in the project. Conditional helper interfaces
are discharged before the final bounds are obtained.

On 1 November the tutorial correspondence check compiled 54 typed restatements,
checked 190 named interfaces and printed 72 definition bodies against verified
proof objects. The public snapshot's source hashes match the independently
built project. No second complete Lean source build is claimed here.

The previous manuscript's arbitrary-real-alpha Proposition 2.3 did not have
a separate generic Lean theorem. That reference belongs to the earlier
manuscript. The current paper does not assert such a numbered general-alpha
result; all seven conclusions of its Theorem 1.1 are covered.
Literal Python/C++ program correctness, runtime/case-count diagnostics,
examples as displayed, prose, historical attribution and bibliographic
metadata are not themselves Lean theorems. Lean proves the finite inequality
with its own coverage and kernel-checked certificates; it does not assume
native execution is correct. See verification/VERIFICATION_SCOPE.txt.

EXACT COMPUTATION
The standalone checker includes all 1160 coefficients and 14 exceptional
representatives. It generates all required families from their defining laws,
reads no input files and uses only Python's standard library. All mathematical
comparisons use exact integers and no optimiser.

From the repository root, with Python >=3.10 and assertions enabled:
  python3 ancillary/standalone/check_finite.py

A complete run on 1 November returned PASS in about 100 seconds:
  128400 labelled five-families / 1160 types;
  14105084 six-extensions, including five-seed multiplicities;
  14 exceptional six-types;
  26 oriented seven-label seed checks / 16888 seed-family cases.
These are not all counts of distinct labelled domains. Appendix B of the
technical companion proves coverage; Appendix C prints the entire checker.
The successful run and source hashes are in verification/editorial_2026-11-01/.
The unchanged checker was not rerun merely to upload the paper.

All 1160 weights and nine exceptional correction integers match the existing
native certificate. The earlier native strategy in ancillary/finite_certificate/
uses 18 seed families / 14248 seed-domain cases / 18316 feature rows, whereas
the Lean and standalone endpoint strategy uses 26 orientations / 16888 cases.
These strategies prove the same finite inequality using different counting
units. The older native data, checkers and generation records are preserved.

REPRODUCE: PAYLOAD INTEGRITY
  python3 scripts/manifest.py
The result must be PASS, with no missing, changed or unlisted payload file.
The updated MANIFEST.sha256 includes this revision and the front-page README.
Runtime caches/build products and the older native replay outputs are excluded.

REPRODUCE: JOURNAL PAPER
With ordinary pdfLaTeX and its standard packages:
  cd manuscript
  mkdir -p build
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
  cd ..

REPRODUCE: FULLY PRINTED TECHNICAL COMPANION
  cd docs/full-proof-2026-11-01
  mkdir -p build
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
  cd ../..
Keep its local check_finite.py beside main.tex: the program is included
verbatim. No custom style, external figures or bibliography file is required.

REPRODUCE: COMPLETE LEAN PROOF
Lean 4.26.0, Mathlib 4.26.0 and all transitive revisions are pinned in lean/.
From the repository root, after obtaining the specified toolchain:
  cd lean
  lake exe cache get
  python3 ../scripts/build_lean.py --jobs 1
  python3 ../scripts/check_lean_axioms.py
  cd ..
Use the complete official library cache; some imports require broad Mathlib
companion files. The cache contains standard libraries, not project proofs.
The proof can take hours and several GB of memory to rebuild. The portable
helper supports a bounded job count and source/artifact-checked resume.
Its fixture tests are separate from the actual independent direct-source
build records, which remain under verification/codex-independent-lean/.

Canonical alternative, with memory adequate for Lake's parallelism:
  cd lean
  lake build CDCert.Main CDCert.TwoInputs
  lake env lean receipts/FinalAxioms.lean
Both default targets explicitly name Main and TwoInputs. The 319-module
required closure and seven additional auxiliary modules are all covered by
the prior source-build evidence; no project binaries are distributed.

REPRODUCE: EARLIER NATIVE CHECKS
  sh scripts/reproduce_native.sh
For complete regeneration, also install a C++17 compiler named c++, and run
from ancillary/finite_certificate/ with a NEW output directory:
  python3 run_fresh_regeneration.py /absolute/path/to/new/output
The ancillary README distinguishes saved-data replay from full generation.

REVIEW AND ARCHIVAL STATUS
This remains a draft for coauthor review. Updating the public repository is
not a GitHub release or DOI deposit. Archival publication waits for author
agreement. Files in metadata/ remain inactive drafts and do not constitute
an approved license, release or deposit. No email is sent by this work.
