#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_joint_exact.py
python3 verify_joint_tuple_features.py
python3 verify_compressed_potential.py
python3 checks/check_global_derivation.py
python3 checks/check_charges.py
