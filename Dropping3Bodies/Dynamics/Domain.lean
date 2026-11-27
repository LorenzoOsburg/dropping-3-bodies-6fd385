module

public import Dropping3Bodies.Basic
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-!
The regular configuration domain for the Newtonian vector field.
-/

namespace DroppingThreeBodies

/-- Collision freedom is equivalent to positivity of every distinct-pair distance. -/
theorem collisionFree_iff_dist_pos (q : Fin 3 → Point) :
    CollisionFree q ↔ ∀ i j, i ≠ j → 0 < dist (q i) (q j) := by
  constructor
  · intro h i j hij
    exact dist_pos.mpr (h i j hij)
  · intro h i j hij
    exact (dist_pos).mp (h i j hij)

/-- Every admissible initial configuration lies in the regular domain. -/
theorem initialData_collisionFree (d : InitialData) : CollisionFree d.position :=
  d.pairwise_distinct

end DroppingThreeBodies
