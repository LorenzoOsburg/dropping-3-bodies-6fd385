module

public import Dropping3Bodies.Dynamics.Newton
public import Mathlib.Tactic

@[expose] public section

/-!
Instantaneous pair-cancellation identities for the unit-mass Newton field.
-/

namespace DroppingThreeBodies

noncomputable section

/-- The inverse-cube kernel is symmetric in its two body indices. -/
@[simp] theorem inverseCubeDistance_comm (q : Fin 3 → Point) (i j : Fin 3) :
    inverseCubeDistance q i j = inverseCubeDistance q j i := by
  simp [inverseCubeDistance, dist_comm]

/-- The total internal acceleration vanishes by pairwise force cancellation. -/
theorem unitAcceleration_sum_eq_zero (q : Fin 3 → Point) :
    unitAcceleration q 0 + unitAcceleration q 1 + unitAcceleration q 2 = 0 := by
  ext k
  simp [unitAcceleration, inverseCubeDistance]
  rw [dist_comm (q 0) (q 1), dist_comm (q 0) (q 2), dist_comm (q 1) (q 2)]
  ring

/-- The net torque of internal Newtonian forces vanishes instantaneously. -/
def unitTotalTorque (q : Fin 3 → Point) : ℝ :=
  ∑ i : Fin 3, cross (q i) (unitAcceleration q i)

theorem unitTotalTorque_eq_zero (q : Fin 3 → Point) : unitTotalTorque q = 0 := by
  simp [unitTotalTorque, unitAcceleration, inverseCubeDistance, cross,
    Fin.sum_univ_succ, dist_comm]
  ring

end

end DroppingThreeBodies
