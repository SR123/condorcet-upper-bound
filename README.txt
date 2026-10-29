IMPROVED UPPER BOUNDS ON THE SIZE OF CONDORCET DOMAINS
Pavlos Moros and Søren Riis
Independent-review packet, 29 October 2026

START HERE
manuscript/main.pdf       Latest paper, eight pages
manuscript/main.tex       Complete standalone LaTeX source
supplement/main.pdf       Certificate supplement, three pages
supplement/main.tex       Complete standalone supplementary source
lean/                    Complete Lean project: 326 source modules and pins
ancillary/finite_certificate/   Native scripts, generators, data and witnesses
verification/            Precise scope, correspondence and verification receipts
REVIEW_GUIDE.txt          Suggested starting points for an independent review

AUTHORITATIVE VERSIONS
The paper source is byte-for-byte identical to the latest main.tex saved in
the shared Overleaf project after the journal-draft update and GitHub/DOI
placeholder correction. Both links in reference [9] deliberately remain
placeholders. The supplement's equations are unchanged; its paths and prose
now refer to this repository and to the separate Lean documentation.

The Lean project comes from Claude's final CDCert-MorosRiis bundle, rather
than the earlier four-module foundation package. Seven comments/docstrings
were clarified without changing mathematical commands or proof terms.
Every project source module has now been compiled independently, including
recompilation of the clarified files. No supplied project binaries were used.
Pinned standard Lean/Mathlib libraries were reused. The final two entry
points and all 20 statement/axiom checks passed after those recompilations.

PAPER-TO-LEAN MAP: THEOREM 1.1
All names below have prefix CDCert.Main. and are in lean/CDCert/Main.lean.
The functions are the actual maximum domain sizes Condorcet.f and Condorcet.h.

Paper result                          Lean declaration
General recurrence, equation (1)       general_recurrence
General geometric bound, equation (1)  general_geometric
Peak-pit recurrence, equation (2)      peak_recurrence
Peak-pit geometric bound, equation (2) peak_geometric
Existence/bound of general root limit  general_limit
Existence/bound of peak-pit root limit peak_limit
f(n)=O(n^(-8/11)*(32/11)^n)            general_polynomial_correction

The first four theorems assume only n >= 3; the last three have no extra
hypotheses. There is no assumed density estimate, finite coverage claim,
injection, common axis or computational oracle in these seven statements.
The semantic definitions quantify over every odd voter profile, permitting
repeated voters, on actual strict total orders.

SUPPORTING ARGUMENTS
Lemma 2.1: Condorcet.deletion_gap_adjacency_identity;
  Condorcet.IsExtremeFull.gapCount_zero.
Theorem 2.2: Condorcet.IsFull.component_inF and
  Condorcet.IsFull.sum_components_deletionSum.
Theorem 3.1: CDCert.Recurrences.gap_inequality.
Lemma 3.2: Condorcet.IsFull.missing_swap.
Lemma 3.3: move/count identities in Condorcet/GapCounts.lean, including
  Condorcet.move_counts_per_order, Condorcet.IsFull.second_move_count and
  Condorcet.IsFull.gap_slack_identity.
Lemmas 3.4-3.5: Condorcet.IsMaximal.fixed_pair_not_consecutive and
  CDCert.FreeLocked.FreePair.law, not_both, lift_locked, drop_locked.
Proposition 3.6: CDCert.FreeLocked.psi_inj and free_le_locked.
Lemma 4.1: CDCert.K6.finite_lemma in CDCert/K6/SevenFinal.lean;
  fixed-pair coverage, both orientations and the R8 receiver are proved
  inside the import chain, rather than assumed from a native PASS flag.
Proposition 5.1: CDCert.Bridge.InF.density, using CDCert.K6.adj_le;
  the window and ordered-copy arguments are in K6/Win.lean,
  K6/Concat.lean and K6/Density.lean.
Literal gap/density inputs and their transfer: CDCert.TwoInputs.first_input,
  second_input and transfer.
Supermultiplicativity: CDCert.Supermult.f_supermul and h_supermul.
Limits and polynomial correction: CDCert/Asymptotics.lean.
Many supporting statements use Fin(n+1); their gap coefficient n+2 is
therefore (number of alternatives)+1, exactly as in the paper. The finite
lemma is written with denominators cleared: cost10=10*C and qD=2*D*q.

ASSUMPTIONS, PLACEHOLDERS AND LIMITS OF COVERAGE
No sorry/admit placeholders, custom axioms or native_decide occur in the
326 project source modules. All 20 checked final/support results depend
only on propext, Classical.choice and Quot.sound. These are Lean's standard
foundations; this is not a claim of an axiom-free proof.

Bounds.FreeLockedInjection is a conditional helper interface, discharged
by CDCert.Recurrences.freeLockedInjection. It is not an assumption left
open in Theorem 1.1. Intermediate results retain their stated mathematical
premises, such as fullness, maximality or membership in the extreme-law
class; those premises are established where the results are applied.

The newer paper's Proposition 2.3 for an arbitrary real density constant
alpha has NOT been exported/proved as a separate parameterised Lean theorem
in this bundle. Its alpha=3/8 instance, used for every part of Theorem 1.1,
is fully proved. This is the one additional mathematical reformulation in
the journal draft that must not be advertised as a separately checked
formal theorem. Its short written proof is available for independent review.

The native generators/checkers themselves, their literal enumeration counts,
literature, attribution, novelty and bibliographical claims are outside the
Lean formalisation. The Lean proof uses its own proved enumeration: 26
oriented endpoint families and 16,888 final states, versus the native 18
seed families, 14,248 seed-domain cases and 18,316 feature rows. These are
different strategies/counting units proving the same required finite lemma.
The formal bounds do not trust execution of the native Python/C++ generators.

VERIFICATION THAT ACTUALLY SUCCEEDED
- Independent source build: all 319 modules required by Main and TwoInputs.
- Seven additional auxiliary modules compiled; all 326 source modules covered.
- Clarified-source recompilations and final Main/TwoInputs recompilations pass.
- Fresh checks of all 20 final/support statements and transitive axioms pass.
- Saved-data native replay passes all five checks, including 113,146 witnesses.
- Prior complete native regeneration passes and matches the saved feature rows;
  its separately labelled receipt is included. That full run was not repeated
  merely to package unchanged native files.
- Both PDFs compile twice without warnings; all eleven pages visually checked.
- Source correspondence, payload hashes and clean ZIP extraction are checked.
Details and receipts are under verification/. Claude's earlier clean-build
receipts are kept distinct from the new independent local receipts.

REPRODUCE: PAYLOAD INTEGRITY
From the extracted repository root, using Python 3:
  python3 scripts/manifest.py
The result must be PASS, with no missing, changed or unlisted payload file.
Runtime caches/build products are excluded from this integrity manifest.

REPRODUCE: PDFs
With standard pdfLaTeX and its standard packages installed:
  cd manuscript
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  cd ../supplement
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  cd ..
Both bibliographies/definitions are self-contained. No private manuscript,
external figures, bibliography database or custom style file is required.

REPRODUCE: COMPLETE MAIN LEAN PROOF
Install/use Lean 4.26.0 via elan. lean/lean-toolchain, lakefile.toml and
lake-manifest.json pin Lean, Mathlib v4.26.0 and all transitive revisions.
From the extracted repository root:
  cd lean
  lake exe cache get
  python3 ../scripts/build_lean.py --jobs 1
  python3 ../scripts/check_lean_axioms.py
  cd ..
Use the complete official library cache command above: some project modules
import the broad Mathlib module. A narrowly targeted cache can omit companion
library files. The cache contains standard external libraries, not project
proofs. Internet access is needed only to obtain tools/dependencies/caches.
The direct source-build receipt is lean/build/checked-source/BUILD_RECEIPT.json;
it must say PASS with 319 completed modules. Final axiom output and the
allowlist receipt are in lean/build/. A missing/failed/partial run is not PASS.

Large kernel certificate checks can take hours and several GB of memory.
The conservative command runs one compiler at a time; --jobs 2 is available
with sufficient free memory. The driver can resume its own successful outputs
only when sources and artifact hashes match. Use a fresh checkout/build when
changing sources. Fixture success/resume/failure checks of the portable
helper are recorded separately; the included full independent receipts came
from dependency-ordered direct compiler invocations, not a second full run
of this portable wrapper.

Canonical Lake alternative (with adequate memory for Lake's parallelism):
  cd lean
  lake build CDCert.Main CDCert.TwoInputs
  lake env lean receipts/FinalAxioms.lean
The two default Lake targets also explicitly name Main and TwoInputs.
The seven additional old auxiliary/example entry modules are outside the
final theorem import closure; their source-build receipts are included.

REPRODUCE: NATIVE CHECKS
From the extracted repository root, using Python 3's standard library:
  sh scripts/reproduce_native.sh
For complete generation, also install a C++17 compiler named c++, and run
from ancillary/finite_certificate/ with a NEW output directory:
  python3 run_fresh_regeneration.py /absolute/path/to/new/output
The success receipt says COMPLETE FRESH REGENERATION PASS. The ancillary
README distinguishes replay from full generation and explains all counts.

REVIEW / RELEASE STATUS
This packet is ready for independent review and transfer to a GitHub repository.
Repository URL and archived-release DOI remain deliberate placeholders. No DOI
registration, archive upload, publication, Git push, release, invitation or
email is performed by this package. Archival publication waits for Pavlos's
agreement. No license grant is invented; the authors still choose licensing
and approve the final paper, metadata and release. Files in metadata/ are
inactive drafts only. Private correspondence, project caches, compiled project
objects and superseded papers are excluded from the ZIP.
