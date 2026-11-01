# Improved Upper Bounds on the Size of Condorcet Domains

**Pavlos Moros and Søren Riis**

**Draft for coauthor review — updated 1 November 2026.** Not yet approved for archival release.

- [Current paper (PDF)](manuscript/main.pdf) · [LaTeX source](manuscript/main.tex) — ten pages including references, plus two mathematical appendix pages.
- [Complete technical companion (PDF)](docs/full-proof-2026-11-01/main.pdf) · [Source](docs/full-proof-2026-11-01/main.tex) — the fully printed proof, computational coverage argument and every coefficient and checking routine.
- [Standalone exact Python checker](ancillary/standalone/check_finite.py) · [Instructions](ancillary/standalone/README.txt).
- [Lean formalisation](lean/) · [Current paper-to-Lean map](docs/PAPER_LEAN_MAP.txt) · [Build and verification guide](README.txt).
- [Independent review guide](REVIEW_GUIDE.txt) · [Verification scope](verification/VERIFICATION_SCOPE.txt) · [File checksums](MANIFEST.sha256).

The journal paper keeps the mathematical argument and examples together; the code, exact tables and detailed finite calculations are provided separately here. Its main theorem gives the general base **32/11** and the peak-pit base **8/3**, with the sharper recurrence and polynomial correction.

All seven conclusions of Theorem 1.1 are formalised end to end. The finite inequality and its coverage are checked within Lean; execution of the Python checker is not a premise of that proof. The checked Lean sources, dependency pins and earlier build records are unchanged. The Python program is a separate reproducible check using the same exact coefficients.

This update replaces the manuscript and reading documentation and adds the computational companion. The independently checked [29 October snapshot](https://github.com/SR123/condorcet-upper-bound/tree/0d5dd168854b208d8436ea685921aa03d7c42200) remains available, including its earlier eight-page paper and certificate supplement. Numbering in the updated map refers to the current paper.

The [1 November verification note](verification/editorial_2026-11-01/README.txt) distinguishes the earlier full Lean build, the later correspondence checks and the complete standalone Python run. No new full Lean rebuild is claimed for this editorial update.

No GitHub release or DOI has been created. Archival publication remains subject to author agreement; preparation-stage files in `metadata/` remain inactive drafts.
