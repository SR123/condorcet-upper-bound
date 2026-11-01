# A Tutorial on Upper Bounds for Condorcet Domains

**Søren Riis** · Review draft, 1 November 2026

[Read the tutorial (PDF)](main.pdf) · [LaTeX source](main.tex) · [Joint research paper](../manuscript/main.pdf)

This is a separate exposition of the upper-bound results of **Pavlos Moros and Søren Riis**. Its contribution is the organisation of the ideas, worked examples, numerical comparisons and a detailed guide from mathematical statements to the existing Lean proofs. The research results and formalisation remain credited to their sources. Claude and ChatGPT/Codex assisted the development and checking of the material.

The opening credit and bibliography identify the joint paper and Moros's earlier AI-assisted note, whose author supplied DOI is [10.5281/zenodo.23654773](https://doi.org/10.5281/zenodo.23654773). The current joint paper is in this repository; the exact checked Lean snapshot is preserved at commit `0d5dd168854b208d8436ea685921aa03d7c42200`.

## Reading guide

Start with the opening roadmap and first-pass guide. They separate twelve ideas and show how the two counting inequalities yield 32/11. The chapters give the full structural argument, the finite local estimate, overlapping windows and ordered copies, then the final bounds and growth limits. Small explicit domains illustrate the counts. Tables compare the same n=5,6,7,8,9,10,20,30,100 at successive proof stages.

The strongest estimate is computer assisted. The finite certificates are proved in Lean; this tutorial does not replace them with a new short hand proof. Its optional use of the known small maxima, including f(8)=224, improves finite numerical estimates and is not a premise of the exponential base proof.

The two appendices map all ten exported declarations of Main/TwoInputs, ten further audited results and 190 named definitions/helpers, and explain verification scope. The distinction between formal theorem coverage, intuition and independently checked examples is explicit.

## Source and verification files

- `main.tex`, `sections/`: complete editable tutorial source.
- `data/`: exact numerical table entries and small-construction calculations.
- `scripts/check_tutorial.py`: source identity, declaration locations, examples, local contradictions and exact scaling checks.
- `scripts/build_numerical_examples.py`: regenerate both numerical comparisons and the small construction table.
- `audit/TUTORIAL_LEAN_MAP.json`, `ENTRYPOINT_SIGNATURES.txt`: exact declaration names, locations, signatures and hypotheses.
- `audit/TutorialCorrespondence.lean`, `TutorialSupportStatements.lean`, `TutorialNamedInterfaces.lean`: the 54 typed restatements and 190 named interface checks.
- `audit/fresh_check/`: successful 1 November correspondence receipt and its three logs; `audit/prior_kernel_build/` retains the earlier build/axiom evidence.
- `audit/PUBLIC_TUTORIAL_REVIEW.json`: this exposition update's scope, byline, provenance, source and PDF checks.

The complete original 326-module Lean project is shared at [`../lean/`](../lean/); it is not duplicated inside the tutorial. File paths beginning with `lean/` in the source map are relative to the repository root. Paths beginning `audit/`, `data/`, `scripts/` or `sections/` in the tutorial refer to this directory.

## Reproduction

From the repository root, with Python 3:

```sh
python3 tutorial/scripts/check_tutorial.py
python3 tutorial/scripts/build_numerical_examples.py
```

To rebuild the PDF with ordinary pdfLaTeX and its standard packages:

```sh
cd tutorial
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
```

The result is `build/main.pdf`; the distributed `main.pdf` is the reviewed copy. Build directories are excluded from the repository integrity manifest.

To rebuild the shared formal proof and then check the tutorial interfaces, from the repository root:

```sh
cd lean
lake exe cache get
lake build CDCert.Main CDCert.TwoInputs
lake env lean receipts/FinalAxioms.lean
lake env lean ../tutorial/audit/TutorialCorrespondence.lean
lake env lean ../tutorial/audit/TutorialSupportStatements.lean
lake env lean ../tutorial/audit/TutorialNamedInterfaces.lean
```

Lean 4.26.0, Mathlib 4.26.0 and dependencies are pinned. The full certificate build can take substantial time and memory. The recorded full independent build covered all 326 project modules on 29 October; the 1 November correspondence check compiled 54 typed proofs and checked the 190 named interfaces using verified proof objects. This exposition revision does not claim another full Lean build. All original Lean source hashes remain unchanged.

## Publication relationships

- **Moros's earlier research note:** the precursor, with the existing author-supplied DOI above.
- **Moros–Riis joint paper:** the improved research results; archival publication and a DOI wait for author agreement.
- **This Riis tutorial:** a separate expository document, explicitly based on the joint results. A separate DOI may be considered once the tutorial is stable, linked to the research paper; none has been registered.

This GitHub addition creates no archive deposit, DOI or GitHub release. The review-draft status is retained.
