module

public import Dropping3Bodies.Inertia.JacobiRiccati

@[expose] public section

/-!
# Determinant and area derivatives in the Jacobi frame

These results reuse the existing Jacobi calculus. They are kept separate from
the audited main results while the initial-branch finiteness argument is built.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Jacobi's determinant derivative formula for an invertible planar matrix. -/
theorem hasDerivAt_matrixDet_finTwo_mul_trace
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {V : Matrix (Fin 2) (Fin 2) ℝ}
    {t : ℝ} (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (V i j) t)
    (hdet : (Q t).det ≠ 0) :
    HasDerivAt (fun s => (Q s).det)
      ((Q t).det * Matrix.trace ((Q t)⁻¹ * V)) t := by
  let C := (Q t)⁻¹ * V
  have hQC : Q t * C = V := by
    dsimp [C]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mul]
  have h := hasDerivAt_matrixDet_finTwo hQ
  apply h.congr_deriv
  change _ = (Q t).det * Matrix.trace C
  rw [← hQC]
  simp [Matrix.det_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The determinant of the Jacobi position matrix has logarithmic derivative
`tr C`. No assumption on the orientation or the initial velocity is needed. -/
theorem generalNewton_jacobiDet_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (fun s => (jacobiMatrix m (z s).1).det)
      ((jacobiMatrix m (z t).1).det * Matrix.trace (jacobiRiccatiMatrixCurve m z t))
      t := by
  have hQ := generalNewton_jacobiPositionMatrix_deriv hsol ht hm0 hm1 hm2
  have hdet : (jacobiMatrix m (z t).1).det ≠ 0 := by
    rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z t).1 hm0 hm1]
    exact mul_ne_zero (mul_ne_zero (sqrt_jacobiMu_pos m hm0 hm1).ne'
      (sqrt_jacobiNu_pos m hm0 hm1 hm2).ne') harea
  exact hasDerivAt_matrixDet_finTwo_mul_trace
    (fun i j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ i)) j) hdet

/-- Along a noncollinear general-mass Newton solution, `B' = B tr C`, where
`B` is the signed double area. This applies to both orientations. -/
theorem generalNewton_signedDoubleArea_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (fun s => signedDoubleArea (z s).1)
      (signedDoubleArea (z t).1 * Matrix.trace (jacobiRiccatiMatrixCurve m z t)) t := by
  let k := Real.sqrt (jacobiMu m) * Real.sqrt (jacobiNu m)
  have hk : k ≠ 0 := mul_ne_zero (sqrt_jacobiMu_pos m hm0 hm1).ne'
    (sqrt_jacobiNu_pos m hm0 hm1 hm2).ne'
  have h := (generalNewton_jacobiDet_deriv hsol ht hm0 hm1 hm2 harea).const_mul k⁻¹
  have heq : (fun s => signedDoubleArea (z s).1) =ᶠ[nhds t]
      (fun s => k⁻¹ * (jacobiMatrix m (z s).1).det) := by
    filter_upwards [] with s
    rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z s).1 hm0 hm1]
    change _ = k⁻¹ * (k * _)
    simp [hk]
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z t).1 hm0 hm1]
  change k⁻¹ * (k * _ * _) = _
  field_simp

/-- The area logarithmic derivative identity, in the quotient form `B'/B`. -/
theorem generalNewton_signedDoubleArea_log_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    deriv (fun s => signedDoubleArea (z s).1) t / signedDoubleArea (z t).1 =
      Matrix.trace (jacobiRiccatiMatrixCurve m z t) := by
  rw [(generalNewton_signedDoubleArea_deriv hsol ht hm0 hm1 hm2 harea).deriv]
  exact mul_div_cancel_left₀ _ harea

end

end DroppingThreeBodies
