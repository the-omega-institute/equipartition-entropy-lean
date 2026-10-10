#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p evidence
lake --no-cache --wfail build 2>&1 | tee evidence/build.log
lake env lean -j 2 -M 4096 -E warning DinovLean/Axioms.lean 2>&1 | tee evidence/axioms.log
