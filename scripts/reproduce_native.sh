#!/bin/sh
set -eu
cd "$(dirname "$0")/../ancillary/finite_certificate"
sh run_joint_checks.sh
