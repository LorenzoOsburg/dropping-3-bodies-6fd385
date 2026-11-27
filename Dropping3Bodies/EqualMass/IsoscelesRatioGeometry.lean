module

public import Dropping3Bodies.EqualMass.IsoscelesWronskianGeometry
public import Mathlib.Tactic

@[expose] public section

/-!
# Ratio threshold for the isosceles Wronskian force

The strict ratio threshold `|z/x| > sqrt 3` implies that the two equal legs
are longer than the base, which makes the Wronskian force point outward.
-/

namespace DroppingThreeBodies

noncomputable section

/-- A positive isosceles half-base and ratio above `sqrt 3` make the leg
    strictly longer than the base. -/
theorem isosceles_leg_gt_base_of_ratio_gt_sqrt_three
    (x u v : ℝ) (hx : 0 < x)
    (hratio : Real.sqrt 3 < (v - u) / x) :
    2 * x < dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 2) := by
  have hratio_mul : Real.sqrt 3 * x < v - u :=
    (lt_div_iff₀ hx).mp hratio
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hq : 0 < Real.sqrt (3 : ℝ) * x := mul_pos hsqrt hx
  have hz : 0 < v - u := lt_trans hq hratio_mul
  have hsq_sqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsquare_diff :
      0 < (v - u - Real.sqrt (3 : ℝ) * x) *
        (v - u + Real.sqrt (3 : ℝ) * x) :=
    mul_pos (sub_pos.mpr hratio_mul) (add_pos hz hq)
  have hheight_sq : 3 * x ^ 2 < (v - u) ^ 2 := by
    nlinarith [hsquare_diff, hsq_sqrt]
  let d := dist (isoscelesConfiguration x u v 0)
    (isoscelesConfiguration x u v 2)
  have hd_nonneg : 0 ≤ d := dist_nonneg
  have hd_sq : d ^ 2 = x ^ 2 + (v - u) ^ 2 :=
    isoscelesConfiguration_leftLeg_dist_sq x u v
  have hlong_sq : (2 * x) ^ 2 < d ^ 2 := by
    rw [hd_sq]
    nlinarith [hheight_sq]
  have hlong : 2 * x < d := by
    by_contra hnot
    have hle : d ≤ 2 * x := not_lt.mp hnot
    have hprod : 0 ≤ (2 * x - d) * (2 * x + d) :=
      mul_nonneg (sub_nonneg.mpr hle) (add_nonneg (by positivity) hd_nonneg)
    nlinarith [hlong_sq, hprod]
  simpa [d] using hlong

/-- Above the positive `sqrt 3` ratio threshold the Wronskian force is
    strictly positive. -/
theorem isoscelesWronskianForce_pos_of_ratio_gt_sqrt_three
    (x u v : ℝ) (hx : 0 < x)
    (hratio : Real.sqrt 3 < (v - u) / x) :
    0 < isoscelesWronskianForce x u v := by
  have hz : 0 < v - u := by
    have hr := hratio
    rw [lt_div_iff₀ hx] at hr
    exact lt_trans (mul_pos (Real.sqrt_pos.2 (by norm_num)) hx) hr
  exact isoscelesWronskianForce_pos_of_leg_gt_base x u v hx hz
    (isosceles_leg_gt_base_of_ratio_gt_sqrt_three x u v hx hratio)

end

end DroppingThreeBodies