# Improved Upper Bounds on the Size of Condorcet Domains

**Pavlos Moros and Søren Riis**

**Joint preprint, version 1.0.0 — archived 2 November 2026.**

[Zenodo DOI: 10.5281/zenodo.23871004](https://doi.org/10.5281/zenodo.23871004) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The paper retains its 1 November review-draft date; archival references have been added.

- [Current paper (PDF)](manuscript/main.pdf) · [LaTeX source](manuscript/main.tex) — ten pages including references, plus two mathematical appendix pages.
- [Tutorial by Søren Riis (PDF)](tutorial/main.pdf) · [Tutorial sources and guide](tutorial/) — a separate exposition of the joint upper-bound results.
- [Complete technical companion (PDF)](docs/full-proof-2026-11-01/main.pdf) · [Source](docs/full-proof-2026-11-01/main.tex) — the fully printed proof, computational coverage argument and every coefficient and checking routine.
- [Standalone exact Python checker](ancillary/standalone/check_finite.py) · [Instructions](ancillary/standalone/README.txt).
- [Lean formalisation](lean/) · [Current paper-to-Lean map](docs/PAPER_LEAN_MAP.txt) · [Build and verification guide](README.txt).
- [Independent review guide](REVIEW_GUIDE.txt) · [Verification scope](verification/VERIFICATION_SCOPE.txt) · [File checksums](MANIFEST.sha256).

The paper keeps the mathematical argument and examples together; the code, exact tables and detailed finite calculations are provided separately here. Its main theorem gives the general base **32/11** and the peak-pit base **8/3**, with the sharper recurrence and polynomial correction.

All seven conclusions of Theorem 1.1 are formalised end to end. The finite inequality and its coverage are checked within Lean; execution of the Python checker is not a premise of that proof. The checked Lean sources, dependency pins and earlier build records are unchanged. The Python program is a separate reproducible check using the same exact coefficients.

This update replaces the manuscript and reading documentation and adds the computational companion. The independently checked [29 October snapshot](https://github.com/SR123/condorcet-upper-bound/tree/0d5dd168854b208d8436ea685921aa03d7c42200) remains available, including its earlier eight-page paper and certificate supplement. Numbering in the updated map refers to the current paper.

The [1 November verification note](verification/editorial_2026-11-01/README.txt) distinguishes the earlier full Lean build, the later correspondence checks and the complete standalone Python run. No new full Lean rebuild is claimed for this editorial update.

Moros's [earlier note](https://doi.org/10.5281/zenodo.23654773) is a precursor of the joint improved paper. The [joint-paper Zenodo record](https://doi.org/10.5281/zenodo.23871004) archives the paper, complete LaTeX/Lean sources, finite computational material and reproducibility records. Its exact payload is identified by its own checksums. The separate tutorial remains available here; no separate tutorial DOI has been registered.

The joint paper and accompanying original reproducibility material are licensed under CC BY 4.0; see `LICENSE.txt`. Third-party dependencies retain their own licences. The tutorial is a separate exposition by Søren Riis; the joint-paper archival licence does not purport to license it separately.
