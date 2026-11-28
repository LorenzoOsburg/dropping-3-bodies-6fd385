# Verification record

## Frozen source

- Branch `feature/q2-power-law`, clean and tracking `origin/feature/q2-power-law`.
- Combined checkpoint `40164c309e448b6cae1a67542dc8be97bb17377f`.
- Generalized Q1 checkpoint `0b5950ffbea5024171b3c5f26972b5b8e5f2ea13`.
- Original toolchain `leanprover/lean4:v4.32.0-rc1`. Original Mathlib
  revision `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
- The frozen source records successful Lean builds and principal axiom audits
  in `audit_evidence/general-central-*` and `audit_evidence/q2-power-law-*`.
  The Q1 evidence precedes its checkpoint commit. The Q2 recorded combined
  recheck completed 8,728 jobs.

## Principia environment

The official template is `PrincipiaMathOrg/PrincipiaTemplate` commit
`da848aff2c509e82aae4426a82f50dc525928013`, with Lean 4.35.0-rc2
(commit `11acb17ec6b07a8f9e9173e6845197929540936b`). The template's
Linux comparator CI job is `comparator` in `.github/workflows/ci.yml`.
The disposable local guest is Ubuntu 24.04 on aarch64 via Lima and Apple
Virtualization, with bubblewrap 0.9.0. A guest AppArmor profile grants user
namespace creation to `/usr/bin/bwrap` so the official sandbox can start.

## Module-system port

The 147 frozen Lean modules use `module` and `public import`. Modules with
public definitions use `@[expose] public section`. The public visibility and exposure preserve
cross-module references and unfolding. Private declarations retain their
original visibility. The shared model moves 43 declarations from the proof
tree and retains their names and bodies. The source map gives each move.

The compatibility edits outside module headers and definition moves are
proof-only.

| File | Compatibility edit |
| --- | --- |
| `Dropping3Bodies.lean` | Put both groups of imports in the header and re-export them. |
| `Dropping3Bodies/Support/IntervalEndpoint.lean` | Use the direct `neg_nonneg` lemma for the nonpositive endpoint instead of relying on `linarith` to simplify function negation. |
| `NBody/Regularity.lean`, `Dropping3Bodies/Dynamics/Energy.lean`, `Dropping3Bodies/Dynamics/RegularDomain.lean` | Remove redundant `rfl` steps where the newer simplifier closes the inverse-cube identity. |
| `Dropping3Bodies/EqualMass/SolutionSideOrdering.lean` | Compose `continuous_neg` with the established continuous curves and unfold function composition explicitly. |
| `Dropping3Bodies/Geometry/EuclideanAreaSymmetry.lean` | Enumerate three distinct permutation images to avoid the changed Mathlib permutation enumeration. |
| `Dropping3Bodies/Inertia/RegularEndpointDerivative.lean` | Use continuous constant scalar multiplication with the explicit square-root factor. |
| `Dropping3Bodies/MainResults/Q1Complete.lean` | Use `Matrix.det_zero` with its inferred nonempty-index instance. |

## Verification results

The previous ten-statement comparator, build, and audit logs are in
[the archived verification record](.verification/ten-statements).
The stock template smoke tests remain recorded separately.

The fresh verification covers ten Q1 statements and one Q2 statement,
including `PrincipiaThreeBodies.orientedArea_deriv_neg`.
The original ten signatures and `PrincipiaThreeBodies/Definitions.lean`
match the prior verified baseline byte for byte.

| Check | Result |
| --- | --- |
| Source requirements | Passed the template's Lean source checker on macOS and Ubuntu. |
| Pinned macOS build | Passed `lake build` with 9,084 jobs. |
| Exact elaborated-type comparison | Passed for all eleven declarations using `scripts/check-interface.py`. |
| Axiom audit | Passed for all eleven declarations. The new proof uses exactly `propext`, `Classical.choice`, and `Quot.sound`. |
| Sandboxed Linux build | Passed. Challenge completed 2,482 jobs and Solution completed 9,080. The eleven Challenge placeholders account for the build's `sorry` warnings. |
| Official comparator and independent replay | Passed `./scripts/verify-comparator.sh` on Ubuntu. Con-ron accepted 52,704 exported declarations. NanoDa and Lean's default kernel accepted the solution. The script exited 0 and printed `Your solution is okay!`. |

The [Linux comparator log](.verification/linux-comparator.log),
[macOS build log](.verification/macos-build.log), and
[local type and axiom audit](.verification/macos-interface.log) are for this
eleven-statement version. The [input fingerprints](.verification/linux-input-sha256.txt)
match all 157 archived Linux verifier inputs to the delivered files.
The comparator ran in the local Ubuntu guest. GitHub Actions remains
configured in `.github/workflows/ci.yml`.

## Local tooling and metadata

- The official comparator invocation on macOS exits with
  `error: bwrap is required to run lake comparator`. The Linux verdict above
  used bubblewrap and the unchanged template verifier script.
- The byte-for-byte comparison with the stock template's Apache-2.0 LICENSE
  passed. The local Ruby bundle check reports
  `Could not find 'bundler' (2.7.2) required by your Gemfile.lock`
  on system Ruby 2.6.10. The template's licensee check remains configured
  in CI.
- The template's Ruby metadata check passed. The published v0.4 JSON Schema
  reported `$.project.authors [] should be non-empty`. The template also
  requires `project.responsible_maintainers`. Both lists await confirmation.
  The schema content used for this check has SHA-256
  `25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce`.

The frozen checkout remained clean at the combined checkpoint during
verification. No commits or pushes were made.


## Supplementary mathematical audits

The following reports provide additional human-guided
reviews of selected mathematical arguments and their
corresponding Lean formalizations.

These documents supplement, but do not replace, the
machine-checked Lean proofs and official Comparator results.

- [Generalized Theorem and Tensor Audit](docs/audits/Generalized_Theorem_2_1_and_Newton_Tensor_Lean_Audit_v2_2.pdf)
- [Power-Law Q2 Semantic Audit](docs/audits/Power_Law_Q2_Lean_Semantic_Audit_v1_0.pdf)
