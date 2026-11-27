module

public import Dropping3Bodies.Inertia.AreaDerivative
public import Dropping3Bodies.Inertia.RegularEndpointDerivative
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# Strict concavity of the square root of positive area

The two-dimensional trace calculation avoids spectral theory: the squared
eigenvalue gap is `(C₀₀ - C₁₁)² + 4 C₀₁²` for symmetric `C`.
-/

namespace DroppingThreeBodies

noncomputable section

/-- First derivative of the square root of positive signed double area. -/
theorem generalNewton_sqrtArea_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : 0 < signedDoubleArea (z t).1) :
    HasDerivAt (fun s => Real.sqrt (signedDoubleArea (z s).1))
      (Real.sqrt (signedDoubleArea (z t).1) *
        Matrix.trace (jacobiRiccatiMatrixCurve m z t) / 2) t := by
  have h := (generalNewton_signedDoubleArea_deriv hsol ht hm0 hm1 hm2 harea.ne').sqrt
    harea.ne'
  apply h.congr_deriv
  have hn := (Real.sqrt_pos.2 harea).ne'
  field_simp
  linear_combination -Matrix.trace (jacobiRiccatiMatrixCurve m z t) * Real.sq_sqrt harea.le

/-- Coordinate form of the trace calculation in equation (3.6). -/
theorem matrix_trace_riccati_sqrt_identity
    (C K : Matrix (Fin 2) (Fin 2) ℝ) (hsym : C.transpose = C) :
    Matrix.trace C * Matrix.trace C / 4 + Matrix.trace (-(C * C + K)) / 2 =
      -(Matrix.trace K / 2 + (C 0 0 - C 1 1) ^ 2 / 4 + (C 0 1) ^ 2) := by
  have hsym' : C 1 0 = C 0 1 := congrFun (congrFun hsym 0) 1
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, hsym']
  ring

/-- The square-root area rate satisfies the strict concavity formula.
This differentiates the explicit first derivative, so it also applies at
endpoints of compact subintervals without any within-derivative conventions. -/
theorem generalNewton_sqrtAreaRate_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : 0 < signedDoubleArea (z t).1) (hrest : ∀ i, (z a).2 i = 0) :
    HasDerivAt
      (fun s => Real.sqrt (signedDoubleArea (z s).1) *
        Matrix.trace (jacobiRiccatiMatrixCurve m z s) / 2)
      (-Real.sqrt (signedDoubleArea (z t).1) *
        (Matrix.trace (jacobiForceMatrix G m (z t).1) / 2 +
          (jacobiRiccatiMatrixCurve m z t 0 0 -
            jacobiRiccatiMatrixCurve m z t 1 1) ^ 2 / 4 +
          (jacobiRiccatiMatrixCurve m z t 0 1) ^ 2)) t := by
  let C := jacobiRiccatiMatrixCurve m z t
  let K := jacobiForceMatrix G m (z t).1
  have hC := generalNewton_jacobiRiccatiMatrix_deriv hsol ht hm0 hm1 hm2 harea
  have htr : HasDerivAt (fun s => Matrix.trace (jacobiRiccatiMatrixCurve m z s))
      (Matrix.trace (-(C * C + K))) t := by
    simpa [Matrix.trace, Fin.sum_univ_succ, C, K] using! (hC 0 0).add (hC 1 1)
  have h := ((generalNewton_sqrtArea_deriv hsol ht hm0 hm1 hm2 harea).mul htr).div_const 2
  apply h.congr_deriv
  have hid := matrix_trace_riccati_sqrt_identity C K
    (generalNewton_jacobiRiccatiMatrix_symmetric hsol hconn ha ht hm0 hm1 hm2 harea hrest)
  change _ = -Real.sqrt (signedDoubleArea (z t).1) *
    (Matrix.trace K / 2 + (C 0 0 - C 1 1) ^ 2 / 4 + (C 0 1) ^ 2)
  change (Real.sqrt (signedDoubleArea (z t).1) * Matrix.trace C / 2 *
    Matrix.trace C + Real.sqrt (signedDoubleArea (z t).1) *
      Matrix.trace (-(C * C + K))) / 2 = _
  linear_combination Real.sqrt (signedDoubleArea (z t).1) * hid

/-- Positive masses, gravity, and collision-free positions give positive
trace of the Jacobi force matrix. -/
theorem jacobiForceMatrix_trace_pos
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hG : 0 < G) (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hcf : CollisionFree q) : 0 < Matrix.trace (jacobiForceMatrix G m q) := by
  have h0 := jacobiForceMatrix_quadratic_pos G m q hG hm0 hm1 hm2 hcf
    ![1, 0] (by intro h; have := congrFun h 0; norm_num at this)
  have h1 := jacobiForceMatrix_quadratic_pos G m q hG hm0 hm1 hm2 hcf
    ![0, 1] (by intro h; have := congrFun h 1; norm_num at this)
  simp [matrixQuadratic, Fin.sum_univ_succ] at h0 h1
  simpa [Matrix.trace, Fin.sum_univ_succ] using add_pos h0 h1

/-- Actual second derivative of the square root of area, strictly negative
at every positive-area time. Initial rest supplies the symmetry of `C`. -/
theorem generalNewton_sqrtArea_second_deriv_neg
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea : 0 < signedDoubleArea (z t).1) (hrest : ∀ i, (z a).2 i = 0) :
    deriv (deriv (fun s => Real.sqrt (signedDoubleArea (z s).1))) t < 0 := by
  have hB := generalNewton_signedDoubleArea_deriv hsol ht hm0 hm1 hm2 harea.ne'
  have hpos := hB.continuousAt.eventually (Ioi_mem_nhds harea)
  have heq : deriv (fun s => Real.sqrt (signedDoubleArea (z s).1)) =ᶠ[nhds t]
      (fun s => Real.sqrt (signedDoubleArea (z s).1) *
        Matrix.trace (jacobiRiccatiMatrixCurve m z s) / 2) := by
    filter_upwards [hsol.1.mem_nhds ht, hpos] with s hs hBs
    exact (generalNewton_sqrtArea_deriv hsol hs hm0 hm1 hm2 hBs).deriv
  rw [heq.deriv_eq]
  rw [(generalNewton_sqrtAreaRate_deriv hsol hconn ha ht hm0 hm1 hm2 harea hrest).deriv]
  have hK := jacobiForceMatrix_trace_pos G m (z t).1 hG hm0 hm1 hm2 (hsol.2 t ht).1
  have hp : 0 < Matrix.trace (jacobiForceMatrix G m (z t).1) / 2 +
      (jacobiRiccatiMatrixCurve m z t 0 0 -
        jacobiRiccatiMatrixCurve m z t 1 1) ^ 2 / 4 +
      (jacobiRiccatiMatrixCurve m z t 0 1) ^ 2 := by positivity
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.sqrt_pos.2 harea)) hp

/-- Strict concavity on any compact positive-area interval. -/
theorem generalNewton_sqrtArea_strictConcaveOn_Icc
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a s t : ℝ} (ha : a ∈ I) (hIcc : Set.Icc s t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea : ∀ x ∈ Set.Icc s t, 0 < signedDoubleArea (z x).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    StrictConcaveOn ℝ (Set.Icc s t) (fun x => Real.sqrt (signedDoubleArea (z x).1)) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc s t)
  · intro x hx
    exact (generalNewton_sqrtArea_deriv hsol (hIcc hx) hm0 hm1 hm2
      (harea x hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact generalNewton_sqrtArea_second_deriv_neg hsol hconn ha
      (hIcc (interior_subset hx)) hm0 hm1 hm2 hG (harea x (interior_subset hx)) hrest

end

end DroppingThreeBodies
