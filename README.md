# Three Bodies Released from Rest

This Principia draft formalizes generalized Q1 for symmetric attractive
central pair forces and subcritical Q2 for the equal-mass, common-coupling
inverse-power potential. The [statement inventory](STATEMENTS.md) records the
exact Lean signatures, temporal domains, hypotheses, and provenance.
[Challenge](Challenge.lean) uses only Mathlib imports and states the model
definitions alongside the eleven theorems. [Solution](Solution.lean) and the
proof development use the matching model in
[Definitions](PrincipiaThreeBodies/Definitions.lean). Comparator checks
the definitions that the theorem statements depend on, including the
construction of the maximal trajectory. [SOURCE-MAP.md](SOURCE-MAP.md)
traces the model declarations and the included proof modules.

## Build and check

The project uses the official Principia template at commit
`da848aff2c509e82aae4426a82f50dc525928013`, including the pinned
`leanprover/lean4:v4.35.0-rc2` toolchain and Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Root and docbuild Lake manifests
pin the dependency revisions.

```sh
python3 scripts/check-lean-sources.py
ruby test/validate_formalization_test.rb
ruby scripts/validate-formalization.rb
lake exe cache get
lake build
python3 scripts/check-interface.py
(cd docbuild && DOCGEN_SRC=file DISABLE_EQUATIONS=1 lake build PrincipiaThreeBodies:docs)
```

On Linux with bubblewrap installed and allowed to create its sandbox, run
`./scripts/verify-comparator.sh`. The template's
[CI workflow](.github/workflows/ci.yml) has an Ubuntu job named
**Check statement against solution**. It invokes the same script with the
Lean toolchain's own comparator and bundled NanoDa and con-ron checkers.
The local interface check compares elaborated theorem types and runs
`#print axioms`. The [verification record](VERIFICATION.md) records the
kernel and independent-checker results separately.

## Submission integration

- `main.tex` is pending integration by the paper collaborator. The visualization is a separate deliverable.
- The template's Ruby validation checks the document version, license field,
  description, and template placeholders. The published metadata schema
  requires a nonempty `project.authors` list. The template also requests
  `project.responsible_maintainers`. Both fields await confirmed identities.
- The template's Apache-2.0 `LICENSE` and `project.license` are preserved.
  The frozen checkout has no root license or grant identified for the copied
  Lean source. Confirm authorization from its rights holders to distribute
  that source under the required Apache-2.0 terms before upload. Git commit
  attribution alone does not establish submission authorship or permissions.
  Mathlib and the other pinned dependencies retain their respective licenses.
  This directory excludes the frozen checkout's external source snapshots.
- The file preflight uses `Challenge.lean`, `Solution.lean`, and
  `comparator.json` from the saved verification files. For full verification,
  link the GitHub repository and use the Comparator CI result for the exact
  checked commit. Solution needs the supporting Lean modules and pinned Lake
  environment from that checkout.
