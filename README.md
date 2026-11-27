# Dropping 3 Bodies

Lean 4 formalization of the Principia project [Dropping 3 Bodies](https://principia-math.com/projects/6fd385f995b49c7a4d929f6f47b979a9). The layout follows the Palomar template.

We prove some properties of brake orbits in the (Newtonian) 3 body-problem.

## Layout

- `Challenge.lean` states the advertised results with `sorry`; keep its imports to Lean core and Mathlib.
- `Solution.lean` proves the same declarations by importing the development in `Dropping3Bodies/`.
- `comparator.json` lists the declarations Comparator checks between the two.
- `formalization.yaml` records the public description, provenance, authorship, automation and review status. Replace every `TEMPLATE` value.

## Checks

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

Repository: https://github.com/LorenzoOsburg/dropping-3-bodies-6fd385
