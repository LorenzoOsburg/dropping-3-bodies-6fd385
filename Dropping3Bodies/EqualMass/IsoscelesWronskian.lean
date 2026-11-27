module

public import Dropping3Bodies.EqualMass.IsoscelesReduction
public import Mathlib.Tactic

@[expose] public section

/-!
# Wronskian force identity in the equal-mass isosceles subspace

This is a pointwise identity for the Newton acceleration at an isosceles
configuration. It is not yet a trajectory-level bootstrap theorem.
-/

namespace DroppingThreeBodies

noncomputable section

/-- The acceleration contribution to the derivative of `W = x*z' - z*x'`
    in the symmetric coordinates `x` (base half-length) and `z = v-u`.
    Along a twice differentiable symmetric solution this equals `W'`. -/
def isoscelesWronskianForce (x u v : ℝ) : ℝ :=
  x * isoscelesRelativeHeightAcceleration x u v -
    (v - u) * isoscelesBaseHalfAcceleration x u v

/-- Exact Wronskian acceleration identity from the equal-mass Newton field. -/
theorem isoscelesWronskianForce_eq (x u v : ℝ) (hx : 0 < x) :
    isoscelesWronskianForce x u v =
      (v - u) / (4 * x ^ 2) -
        2 * x * (v - u) * inverseCubeDistance
          (isoscelesConfiguration x u v) 0 2 := by
  rw [isoscelesWronskianForce,
    isoscelesRelativeHeightAcceleration_eq,
    isoscelesBaseHalfAcceleration_eq x u v hx]
  field_simp [hx.ne']
  ring

/-- In the positive-height orientation, the Wronskian force is positive when
    the leg inverse-cube factor lies below the base threshold. -/
theorem isoscelesWronskianForce_pos_of_kernel_bound
    (x u v : ℝ) (hx : 0 < x) (hz : 0 < v - u)
    (hk : 8 * x ^ 3 * inverseCubeDistance
      (isoscelesConfiguration x u v) 0 2 < 1) :
    0 < isoscelesWronskianForce x u v := by
  rw [isoscelesWronskianForce_eq x u v hx]
  have hnum : 0 < 1 - 8 * x ^ 3 * inverseCubeDistance
      (isoscelesConfiguration x u v) 0 2 := by linarith
  have hden : 0 < 4 * x ^ 2 := by positivity
  have hcoef : 0 < (1 - 8 * x ^ 3 * inverseCubeDistance
      (isoscelesConfiguration x u v) 0 2) / (4 * x ^ 2) :=
    div_pos hnum hden
  have hcoef' : (1 - 8 * x ^ 3 * inverseCubeDistance
      (isoscelesConfiguration x u v) 0 2) / (4 * x ^ 2) =
      1 / (4 * x ^ 2) - 2 * x * inverseCubeDistance
        (isoscelesConfiguration x u v) 0 2 := by
    field_simp [hx.ne']
    ring
  have hprod : 0 < (v - u) *
      (1 / (4 * x ^ 2) - 2 * x * inverseCubeDistance
        (isoscelesConfiguration x u v) 0 2) := by
    rw [← hcoef']
    exact mul_pos hz hcoef
  calc
    (v - u) / (4 * x ^ 2) - 2 * x * (v - u) *
        inverseCubeDistance (isoscelesConfiguration x u v) 0 2 =
      (v - u) * (1 / (4 * x ^ 2) - 2 * x *
        inverseCubeDistance (isoscelesConfiguration x u v) 0 2) := by ring
    _ > 0 := hprod

end

end DroppingThreeBodies


