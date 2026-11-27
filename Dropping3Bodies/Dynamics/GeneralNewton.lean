module

public import Dropping3Bodies.Dynamics.Newton
public import Mathlib.Tactic

@[expose] public section

/-! Newton's vector field with arbitrary masses and gravitational constant. -/

namespace DroppingThreeBodies

noncomputable section

/-- Acceleration of body `i` for masses `m` and gravitational constant `G`.
    The diagonal summand is set to zero; the remaining two summands are the
    Newtonian pair forces divided by the mass of body `i`. -/
def generalAcceleration (G : ℝ) (m : Fin 3 → ℝ)
    (q : Fin 3 → Point) (i : Fin 3) : Point :=
  ∑ j : Fin 3, if j = i then 0 else
    (G * m j * inverseCubeDistance q i j) • (q j - q i)

/-- First-order phase-space field for arbitrary point masses. -/
def generalNewtonField (G : ℝ) (m : Fin 3 → ℝ) (z : Phase) : Phase :=
  (z.2, fun i => generalAcceleration G m z.1 i)

/-- The general-mass acceleration specializes definitionally, after the
    finite sum is evaluated, to the existing unit-mass acceleration. -/
theorem generalAcceleration_one_eq_unit (q : Fin 3 → Point) (i : Fin 3) :
    generalAcceleration 1 (fun _ : Fin 3 => 1) q i = unitAcceleration q i := by
  fin_cases i <;>
    simp [generalAcceleration, unitAcceleration, inverseCubeDistance,
      Fin.sum_univ_succ]

/-- For a cyclic opposite-side pair, all general-mass force terms except
    those sourced at the opposite body cancel from the pair torque. The
    remaining torque is the source mass and gravitational constant times the
    unit-mass pair torque. -/
theorem general_pair_torque_eq_source_mass_mul_unit_pair_torque
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) (i : Fin 3) :
    cross (sideVector q i)
      (generalAcceleration G m q (cyclicPrev i) -
        generalAcceleration G m q (cyclicNext i)) =
      G * m i * cross (sideVector q i)
        (unitAcceleration q (cyclicPrev i) -
          unitAcceleration q (cyclicNext i)) := by
  fin_cases i <;>
    simp [generalAcceleration, unitAcceleration, sideVector, cyclicPrev,
      cyclicNext, inverseCubeDistance, Fin.sum_univ_succ, cross] <;>
    ring

/-- The general-mass cyclic pair torque is controlled by the same side gap
    as in the equal-mass problem, with a positive factor `G*m i`. -/
theorem general_pair_torque_eq_neg_area_gap
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) (i : Fin 3)
    (hprev : 0 < dist (q (cyclicPrev i)) (q i))
    (hnext : 0 < dist (q (cyclicNext i)) (q i)) :
    cross (sideVector q i)
      (generalAcceleration G m q (cyclicPrev i) -
        generalAcceleration G m q (cyclicNext i)) =
      -(G * m i) * signedDoubleArea q *
        inverseCubeGapFactor
          (dist (q (cyclicPrev i)) (q i))
          (dist (q (cyclicNext i)) (q i)) * sideGap q i := by
  rw [general_pair_torque_eq_source_mass_mul_unit_pair_torque,
    unit_pair_torque_eq_neg_area_gap q i hprev hnext]
  ring

theorem generalNewtonField_one_eq_unit (z : Phase) :
    generalNewtonField 1 (fun _ : Fin 3 => 1) z = unitNewtonField z := by
  apply Prod.ext
  · rfl
  · funext i
    exact generalAcceleration_one_eq_unit z.1 i

end

end DroppingThreeBodies
