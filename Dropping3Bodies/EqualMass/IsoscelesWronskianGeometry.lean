module

public import Dropping3Bodies.EqualMass.IsoscelesWronskian
public import Mathlib.Tactic

@[expose] public section

/-!
# Geometric threshold for the isosceles Wronskian force

A leg longer than the base is exactly the distance condition that makes the
pointwise Wronskian force positive in the positive-height orientation.
-/

namespace DroppingThreeBodies

noncomputable section

/-- A leg longer than the isosceles base makes its inverse-cube kernel fall
    below the threshold in the Wronskian force identity. -/
theorem isosceles_kernel_bound_of_leg_gt_base
    (x u v : ℝ) (hx : 0 < x)
    (hleg : 2 * x < dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 2)) :
    8 * x ^ 3 * inverseCubeDistance
      (isoscelesConfiguration x u v) 0 2 < 1 := by
  let d := dist (isoscelesConfiguration x u v 0)
    (isoscelesConfiguration x u v 2)
  have hd : 0 < d := lt_trans (by positivity) hleg
  have hcube : (2 * x) ^ 3 < d ^ 3 := by
    have hfactor : 0 < (d - 2 * x) *
        (d ^ 2 + d * (2 * x) + (2 * x) ^ 2) :=
      mul_pos (sub_pos.mpr hleg) (by positivity)
    nlinarith [hfactor]
  have hthreshold : 8 * x ^ 3 < d ^ 3 := by nlinarith [hcube]
  have hkernel : inverseCubeDistance
      (isoscelesConfiguration x u v) 0 2 = (d ^ 3)⁻¹ := by
    simp [inverseCubeDistance, zpow_neg]
    rfl
  rw [hkernel]
  calc
    8 * x ^ 3 * (d ^ 3)⁻¹ < d ^ 3 * (d ^ 3)⁻¹ :=
      mul_lt_mul_of_pos_right hthreshold (by positivity)
    _ = 1 := by field_simp [ne_of_gt (pow_pos hd 3)]

/-- With positive signed height, a leg strictly longer than the base gives
    strictly positive Wronskian force. -/
theorem isoscelesWronskianForce_pos_of_leg_gt_base
    (x u v : ℝ) (hx : 0 < x) (hz : 0 < v - u)
    (hleg : 2 * x < dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 2)) :
    0 < isoscelesWronskianForce x u v := by
  apply isoscelesWronskianForce_pos_of_kernel_bound x u v hx hz
  exact isosceles_kernel_bound_of_leg_gt_base x u v hx hleg

end

end DroppingThreeBodies
