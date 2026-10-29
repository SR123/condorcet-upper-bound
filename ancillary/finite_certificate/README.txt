EXACT NATIVE CERTIFICATE -- RELEASE CANDIDATE
Improved Upper Bounds on the Size of Condorcet Domains

These mathematical files are unchanged from the independently audited
29 October snapshot. Run the commands below from this directory.

SAVED-DATA REPLAY -- Python 3 standard library only
  sh run_joint_checks.sh
Successful completion has exit status zero. This checks exact rational
residuals, all 113,146 tuple witnesses, the compressed potential, scalar
transfers and supplementary bounded charge-map cases. It replays the
saved data; it is not a fresh exhaustive generation of the family.

COMPLETE REGENERATION -- Python 3 and C++17 compiler named c++
  python3 run_fresh_regeneration.py /absolute/path/to/new/output
The output directory must not exist. No optimizer, network or nonstandard
Python package is needed. The driver regenerates the families from the
defining laws, checks completeness flags and all witnesses, and compares
the resulting feature rows. Success writes FULL_REGENERATION_RECEIPT.json
with result COMPLETE FRESH REGENERATION PASS. A prior complete run is
recorded in the verification statement; it is not silently claimed anew.

NATIVE ENUMERATION COUNTS
128400 labelled five-families /1160 relabelling types;
14105084 six-extensions /94830 feature rows;
397 selected sets /14 types on 13 exceptional feature rows;
18 seven-label seeds /14248 seed-domain cases /18316 feature rows.
These are different counting units. Both orientations are covered.
The generic and R8 receiver cases and the passage to arbitrary n are
the mathematical arguments in the paper. A separate Lean proof also
formalises those steps and uses its own larger seven-label enumeration;
see ../../verification/VERIFICATION_SCOPE.txt for that distinction.

The Lean proof is under ../../lean/, not the older four-module partial
foundation package. Its pinned dependencies and exact theorem statements
are documented there. Neither native PASS output nor a source-token scan
alone establishes end-to-end Lean verification.
