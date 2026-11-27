module

public import Dropping3Bodies

public section

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

theorem Dropping3Bodies.main_result (n : ℕ) : n + n = 2 * n := by
  exact add_self_eq_two_mul n

