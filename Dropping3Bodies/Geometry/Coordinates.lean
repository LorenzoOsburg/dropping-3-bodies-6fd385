module

public import Dropping3Bodies.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-!
Coordinate identities for planar Euclidean geometry.  These are algebraic
lemmas used by the Jacobi and equal-mass developments.
-/

namespace DroppingThreeBodies

noncomputable section

/-- The coordinate dot product on the plane. -/
def dot2 (u v : Point) : ℝ := u 0 * v 0 + u 1 * v 1

@[simp] theorem cross_self (u : Point) : cross u u = 0 := by
  simp [cross]
  ring

theorem cross_swap (u v : Point) : cross u v = - cross v u := by
  simp [cross]
  ring

theorem cross_add_left (u v w : Point) :
    cross (u + v) w = cross u w + cross v w := by
  simp [cross]
  ring

theorem cross_add_right (u v w : Point) :
    cross u (v + w) = cross u v + cross u w := by
  simp [cross]
  ring

theorem cross_sub_left (u v w : Point) :
    cross (u - v) w = cross u w - cross v w := by
  simp [cross]
  ring

theorem cross_sub_right (u v w : Point) :
    cross u (v - w) = cross u v - cross u w := by
  simp [cross]
  ring

theorem norm_sq_eq_dot2 (u : Point) : ‖u‖ ^ 2 = dot2 u u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dot2]
  ring

theorem cross_sq_add_dot2_sq (u v : Point) :
    cross u v ^ 2 + dot2 u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_eq_dot2, norm_sq_eq_dot2]
  simp [cross, dot2]
  ring

theorem cross_sq_le_norm_sq_mul_norm_sq (u v : Point) :
    cross u v ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [← cross_sq_add_dot2_sq u v]
  nlinarith [sq_nonneg (dot2 u v)]

/-- All cyclic choices of the vertex give the same oriented double area. -/
theorem signedDoubleArea_cyclic₁ (q : Fin 3 → Point) :
    cross (q 2 - q 1) (q 0 - q 1) = signedDoubleArea q := by
  simp [signedDoubleArea, cross]
  ring

theorem signedDoubleArea_cyclic₂ (q : Fin 3 → Point) :
    cross (q 0 - q 2) (q 1 - q 2) = signedDoubleArea q := by
  simp [signedDoubleArea, cross]
  ring

/-- Product rule for the coordinate dot product along differentiable planar
    vector curves. -/
theorem hasDerivAt_dot2_curve_coord
    {u v : ℝ → Point} {du dv : Point} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => dot2 (u s) (v s))
      ((du 0 * (v t) 0 + (u t) 0 * dv 0) + (du 1 * (v t) 1 + (u t) 1 * dv 1)) t := by
  have hu0 : HasDerivAt (fun s => u s 0) (du 0) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 0)).clm_apply hu
  have hu1 : HasDerivAt (fun s => u s 1) (du 1) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 1)).clm_apply hu
  have hv0 : HasDerivAt (fun s => v s 0) (dv 0) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 0)).clm_apply hv
  have hv1 : HasDerivAt (fun s => v s 1) (dv 1) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 1)).clm_apply hv
  change HasDerivAt
    (fun s => u s 0 * v s 0 + u s 1 * v s 1)
    ((du 0 * v t 0 + u t 0 * dv 0) + (du 1 * v t 1 + u t 1 * dv 1)) t
  exact (hu0.mul hv0).add (hu1.mul hv1)

/-- Product rule for the oriented determinant along differentiable planar
    vector curves. -/
theorem hasDerivAt_cross_curve_coord
    {u v : ℝ → Point} {du dv : Point} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => cross (u s) (v s))
      (du 0 * (v t) 1 + (u t) 0 * dv 1 - (du 1 * (v t) 0 + (u t) 1 * dv 0)) t := by
  have hu0 : HasDerivAt (fun s => u s 0) (du 0) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 0)).clm_apply hu
  have hu1 : HasDerivAt (fun s => u s 1) (du 1) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 1)).clm_apply hu
  have hv0 : HasDerivAt (fun s => v s 0) (dv 0) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 0)).clm_apply hv
  have hv1 : HasDerivAt (fun s => v s 1) (dv 1) t := by
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj 1)).clm_apply hv
  change HasDerivAt
    (fun s => u s 0 * v s 1 - u s 1 * v s 0)
    (du 0 * v t 1 + u t 0 * dv 1 - (du 1 * v t 0 + u t 1 * dv 0)) t
  exact (hu0.mul hv1).sub (hu1.mul hv0)
/-- Product rule for the coordinate dot product in compact vector notation. -/
theorem hasDerivAt_dot2_curve
    {u v : ℝ → Point} {du dv : Point} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => dot2 (u s) (v s))
      (dot2 du (v t) + dot2 (u t) dv) t := by
  have h := hasDerivAt_dot2_curve_coord hu hv
  convert h using 1; simp [dot2]; ring

/-- Product rule for the oriented determinant in compact vector notation. -/
theorem hasDerivAt_cross_curve
    {u v : ℝ → Point} {du dv : Point} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => cross (u s) (v s))
      (cross du (v t) + cross (u t) dv) t := by
  have h := hasDerivAt_cross_curve_coord hu hv
  convert h using 1; simp [cross]; ring
/-- Algebraic numerator identity for differentiating the angle encoded by
    arctan (dot2 u v / cross u v).  The vectors du,dv stand for the
    derivatives of u,v; this lemma itself is purely pointwise algebra. -/
theorem dotCross_derivativeNumerator_identity
    (u v du dv : Point) :
    dot2 u v * (cross du v + cross u dv) -
        cross u v * (dot2 du v + dot2 u dv) =
      dot2 u u * cross v dv - dot2 v v * cross u du := by
  simp [cross, dot2]
  ring
end

end DroppingThreeBodies
