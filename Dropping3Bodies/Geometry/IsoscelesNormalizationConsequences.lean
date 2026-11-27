module

public import Dropping3Bodies.Geometry.IsoscelesNormalization

@[expose] public section

/-! Metric consequences of the canonical isosceles normal form. -/

namespace DroppingThreeBodies

/-- A nondegenerate canonical isosceles triangle has nonzero signed height.
The static area identity is `isoscelesConfiguration_signedDoubleArea`. -/
theorem isosceles_normalized_nonzero_height
    (x u v : ℝ)
    (hnoncollinear : signedDoubleArea (isoscelesConfiguration x u v) ≠ 0) :
    v - u ≠ 0 := by
  intro hheight
  apply hnoncollinear
  rw [isoscelesConfiguration_signedDoubleArea, hheight]
  ring

/-- Equal legs strictly longer than the base force the signed normalized
height ratio into one of the two strict branches. -/
theorem isosceles_normalized_ratio_branches
    (x u v : ℝ) (hx : 0 < x)
    (hlong : dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 2) >
      dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1)) :
    Real.sqrt 3 < (v-u)/x ∨ (v-u)/x < -Real.sqrt 3 := by
  have hbase := isoscelesConfiguration_base_dist_sq x u v
  have hleg := isoscelesConfiguration_leftLeg_dist_sq x u v
  let dleg := dist (isoscelesConfiguration x u v 0)
    (isoscelesConfiguration x u v 2)
  let dbase := dist (isoscelesConfiguration x u v 0)
    (isoscelesConfiguration x u v 1)
  have hbaseNonneg : 0 ≤ dbase := dist_nonneg
  have hlegPos : 0 < dleg := lt_of_le_of_lt hbaseNonneg hlong
  have hsq : dleg ^ 2 > dbase ^ 2 := by
    nlinarith [sq_nonneg (dleg - dbase)]
  rw [hbase, hleg] at hsq
  have hratio : 3 < ((v-u)/x)^2 := by
    have hx2 : 0 < x^2 := sq_pos_of_pos hx
    field_simp
    nlinarith
  have hsqrt : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases hsign : 0 ≤ (v-u)/x
  · left
    by_contra hnot
    have hle : (v-u)/x ≤ Real.sqrt 3 := le_of_not_gt hnot
    nlinarith [sq_nonneg ((v-u)/x - Real.sqrt 3)]
  · right
    have hneg : (v-u)/x < 0 := lt_of_not_ge hsign
    by_contra hnot
    have hle : -Real.sqrt 3 ≤ (v-u)/x := le_of_not_gt hnot
    nlinarith [sq_nonneg ((v-u)/x + Real.sqrt 3)]

end DroppingThreeBodies
