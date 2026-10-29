LEAN PROJECT: IMPROVED UPPER BOUNDS ON THE SIZE OF CONDORCET DOMAINS
Pavlos Moros and Søren Riis -- independent-review packet, 29 October 2026

Read ../README.txt for the full paper-to-declaration map, assumptions,
coverage limits, reproduction commands and release status. This is the
complete final source project from Claude, not the earlier four-module
foundation package. Main and TwoInputs have a 319-module import closure;
all 326 project modules (including seven extra auxiliary modules) have
been independently compiled. Six clarified files in the required closure,
plus the seventh clarified auxiliary file, have also been recompiled;
the final entry points and 20 statement/axiom checks passed afterwards.

Entry points:
  CDCert/Main.lean       all seven parts of the paper's Theorem 1.1
  CDCert/TwoInputs.lean  literal gap/density inputs and the transfer
  receipts/FinalAxioms.lean   printed semantic definitions, statements/axioms

From this directory, with elan/Lean 4.26.0 and Python 3:
  lake exe cache get
  python3 ../scripts/build_lean.py --jobs 1
  python3 ../scripts/check_lean_axioms.py
An alternative is lake build CDCert.Main CDCert.TwoInputs. Use the complete
standard-library cache, not only the analysis subdirectory. No .lake cache
or project .olean is distributed. All imported finite certificates are
self-contained Lean terms checked by the kernel; native generator execution
is not a trusted proof input.

No sorry/admit/custom axiom/native_decide occurs in the project. The final
axiom lists are exactly the standard propext, Classical.choice and Quot.sound.
The generic alpha version of the new Proposition 2.3 has no separate Lean
declaration; the alpha=3/8 instance and all of Theorem 1.1 are proved.
Conditional helper interfaces are explicitly discharged for the final bounds.
The native family counts are not literal outputs of the Lean enumeration;
see ../verification/VERIFICATION_SCOPE.txt for the two enumeration strategies.

Seven inherited comments/docstrings were clarified without changing proof
commands or string literals. The proof-source equivalence record and diff
are in ../verification/. Source build and axiom receipts are under
../verification/codex-independent-lean/; Claude's earlier receipts are in
../verification/claude-clean-rebuild/. Read those two kinds of evidence
separately. The final compilation coverage receipt records the exact
packaged source hashes, including the clarified files.
