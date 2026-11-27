module

public import Dropping3Bodies.Dynamics.Newton
public import Mathlib.Tactic

@[expose] public section

/-!
# Static equal-mass isosceles acceleration reduction

This module records the configuration-level algebra for a reflection-symmetric
isosceles triangle. It does not assert that a Newton trajectory stays in this
subspace.
-/

namespace DroppingThreeBodies

noncomputable section

/-- A planar point with the given two Cartesian coordinates. -/
def pointXY (x y : ℝ) : Point :=
  EuclideanSpace.single 0 x + EuclideanSpace.single 1 y

@[simp] theorem pointXY_apply_zero (x y : ℝ) : pointXY x y 0 = x := by
  simp [pointXY]

@[simp] theorem pointXY_apply_one (x y : ℝ) : pointXY x y 1 = y := by
  simp [pointXY]

/-- The isosceles configuration with base endpoints `(-x,u)`, `(x,u)` and
    apex `(0,v)`. -/
def isoscelesConfiguration (x u v : ℝ) : Fin 3 → Point
  | 0 => pointXY (-x) u
  | 1 => pointXY x u
  | _ => pointXY 0 v

/-- The signed double area of an isosceles configuration is twice the base
    half-length times its signed vertical separation. -/
theorem isoscelesConfiguration_signedDoubleArea (x u v : ℝ) :
    signedDoubleArea (isoscelesConfiguration x u v) = 2*x*(v-u) := by
  have hax : (isoscelesConfiguration x u v 1 -
      isoscelesConfiguration x u v 0) 0 = 2*x := by
    simp [isoscelesConfiguration, pointXY]
    ring
  have hay : (isoscelesConfiguration x u v 1 -
      isoscelesConfiguration x u v 0) 1 = 0 := by
    simp [isoscelesConfiguration, pointXY]
  have hbx : (isoscelesConfiguration x u v 2 -
      isoscelesConfiguration x u v 0) 0 = x := by
    simp [isoscelesConfiguration, pointXY]
  have hby : (isoscelesConfiguration x u v 2 -
      isoscelesConfiguration x u v 0) 1 = v-u := by
    simp [isoscelesConfiguration, pointXY]
  unfold signedDoubleArea cross
  rw [hax, hay, hbx, hby]
  ring

theorem isoscelesConfiguration_base_dist_sq (x u v : ℝ) :
    dist (isoscelesConfiguration x u v 0) (isoscelesConfiguration x u v 1) ^ 2 =
      (2 * x) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [isoscelesConfiguration, pointXY, Real.dist_eq, sq_abs,
    Fin.sum_univ_succ]
  ring

theorem isoscelesConfiguration_leftLeg_dist_sq (x u v : ℝ) :
    dist (isoscelesConfiguration x u v 0) (isoscelesConfiguration x u v 2) ^ 2 =
      x ^ 2 + (v - u) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [isoscelesConfiguration, pointXY, Real.dist_eq, sq_abs,
    Fin.sum_univ_succ]
  ring

theorem isoscelesConfiguration_rightLeg_dist_sq (x u v : ℝ) :
    dist (isoscelesConfiguration x u v 1) (isoscelesConfiguration x u v 2) ^ 2 =
      x ^ 2 + (v - u) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [isoscelesConfiguration, pointXY, Real.dist_eq, sq_abs,
    Fin.sum_univ_succ]
  ring

theorem isoscelesConfiguration_legs_equidistant (x u v : ℝ) :
    dist (isoscelesConfiguration x u v 0) (isoscelesConfiguration x u v 2) =
      dist (isoscelesConfiguration x u v 1) (isoscelesConfiguration x u v 2) := by
  have hleft := isoscelesConfiguration_leftLeg_dist_sq x u v
  have hright := isoscelesConfiguration_rightLeg_dist_sq x u v
  have hn0 : 0 ≤ dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 2) := dist_nonneg
  have hn1 : 0 ≤ dist (isoscelesConfiguration x u v 1)
      (isoscelesConfiguration x u v 2) := dist_nonneg
  nlinarith [sq_nonneg (dist (isoscelesConfiguration x u v 0)
    (isoscelesConfiguration x u v 2) - dist (isoscelesConfiguration x u v 1)
      (isoscelesConfiguration x u v 2))]

/-- Horizontal acceleration of the left base body, negated so that it is the
    acceleration of the base half-length `x` under the isosceles symmetry. -/
def isoscelesBaseHalfAcceleration (x u v : ℝ) : ℝ :=
  -((unitAcceleration (isoscelesConfiguration x u v) 0) 0)

/-- The horizontal half-difference of the two base accelerations is the
    negative horizontal acceleration of the left base point. -/
theorem isoscelesBaseHalfAcceleration_eq_halfDifference (x u v : ℝ) :
    isoscelesBaseHalfAcceleration x u v =
      ((unitAcceleration (isoscelesConfiguration x u v) 1) 0 -
        (unitAcceleration (isoscelesConfiguration x u v) 0) 0) / 2 := by
  have hlegs := isoscelesConfiguration_legs_equidistant x u v
  have hbaseKernel : inverseCubeDistance (isoscelesConfiguration x u v) 1 0 =
      inverseCubeDistance (isoscelesConfiguration x u v) 0 1 := by
    simp [inverseCubeDistance, dist_comm]
  have hlegKernel : inverseCubeDistance (isoscelesConfiguration x u v) 1 2 =
      inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [inverseCubeDistance, hlegs]
  have hleft :
      (unitAcceleration (isoscelesConfiguration x u v) 0) 0 =
        2 * x * inverseCubeDistance (isoscelesConfiguration x u v) 0 1 +
          x * inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [unitAcceleration, isoscelesConfiguration, pointXY]
    ring
  have hright :
      (unitAcceleration (isoscelesConfiguration x u v) 1) 0 =
        -2 * x * inverseCubeDistance (isoscelesConfiguration x u v) 1 0 -
          x * inverseCubeDistance (isoscelesConfiguration x u v) 1 2 := by
    simp [unitAcceleration, isoscelesConfiguration, pointXY]
    ring
  rw [isoscelesBaseHalfAcceleration, hleft, hright, hbaseKernel, hlegKernel]
  ring

/-- The two base bodies have the same vertical acceleration at an isosceles
    configuration, so the apex-relative height acceleration is also relative
    to the mean base height. -/
theorem isoscelesBaseVerticalAccelerations_eq (x u v : ℝ) :
    (unitAcceleration (isoscelesConfiguration x u v) 0) 1 =
      (unitAcceleration (isoscelesConfiguration x u v) 1) 1 := by
  have hlegs := isoscelesConfiguration_legs_equidistant x u v
  have hlegKernel : inverseCubeDistance (isoscelesConfiguration x u v) 1 2 =
      inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [inverseCubeDistance, hlegs]
  simp [unitAcceleration, isoscelesConfiguration, pointXY, hlegKernel]

/-- Vertical acceleration of the apex relative to the left base body's height.
    In the symmetric subspace this is also the apex height relative to the
    mean base height. -/
def isoscelesRelativeHeightAcceleration (x u v : ℝ) : ℝ :=
  (unitAcceleration (isoscelesConfiguration x u v) 2) 1 -
    (unitAcceleration (isoscelesConfiguration x u v) 0) 1

theorem isoscelesBaseHalfAcceleration_eq (x u v : ℝ) (hx : 0 < x) :
    isoscelesBaseHalfAcceleration x u v =
      -(1 / (4 * x ^ 2) + x * inverseCubeDistance
        (isoscelesConfiguration x u v) 0 2) := by
  have hbase := isoscelesConfiguration_base_dist_sq x u v
  have hbaseDist : dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) = 2 * x := by
    have hdist : 0 ≤ dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1) := dist_nonneg
    nlinarith [sq_nonneg (dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) - 2 * x)]
  have hbaseInv : inverseCubeDistance (isoscelesConfiguration x u v) 0 1 =
      (2 * x) ^ (-3 : ℤ) := by
    simp [inverseCubeDistance, hbaseDist]
  have hforce :
      (unitAcceleration (isoscelesConfiguration x u v) 0) 0 =
        2 * x * inverseCubeDistance (isoscelesConfiguration x u v) 0 1 +
          x * inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [unitAcceleration, isoscelesConfiguration, pointXY]
    ring
  rw [isoscelesBaseHalfAcceleration, hforce, hbaseInv]
  simp [zpow_neg]
  field_simp
  ring

theorem isoscelesRelativeHeightAcceleration_eq (x u v : ℝ) :
    isoscelesRelativeHeightAcceleration x u v =
      -3 * (v - u) * inverseCubeDistance
        (isoscelesConfiguration x u v) 0 2 := by
  have hlegs := isoscelesConfiguration_legs_equidistant x u v
  have hlegInv : inverseCubeDistance (isoscelesConfiguration x u v) 2 1 =
      inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [inverseCubeDistance, dist_comm, hlegs]
  have hleftY :
      (unitAcceleration (isoscelesConfiguration x u v) 0) 1 =
        (v - u) * inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [unitAcceleration, isoscelesConfiguration, pointXY]
    ring
  have hkernelSymm : inverseCubeDistance (isoscelesConfiguration x u v) 2 0 =
      inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [inverseCubeDistance, dist_comm]
  have hapexY :
      (unitAcceleration (isoscelesConfiguration x u v) 2) 1 =
        -2 * (v - u) * inverseCubeDistance (isoscelesConfiguration x u v) 2 0 := by
    simp [unitAcceleration, isoscelesConfiguration, pointXY]
    rw [hlegInv, ← hkernelSymm]
    ring
  rw [isoscelesRelativeHeightAcceleration, hleftY, hapexY, hkernelSymm]
  ring

end

end DroppingThreeBodies
