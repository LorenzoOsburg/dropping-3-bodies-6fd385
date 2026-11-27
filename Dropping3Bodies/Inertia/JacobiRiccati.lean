module

public import Dropping3Bodies.Inertia.JacobiDynamics
public import Dropping3Bodies.Support.CooperativePair
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-! Pointwise algebra for the symmetric-matrix Riccati inequality. -/

namespace DroppingThreeBodies

noncomputable section

/-- Product rule for a single entry of a time-dependent two-by-two matrix
    product, stated entirely in scalar coordinates. -/
theorem hasDerivAt_matrixMul_entry
    {A B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {A' B' : Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t)
    (i j : Fin 2) :
    HasDerivAt (fun s => (A s * B s) i j)
      (∑ k : Fin 2,
        (A' i k * B t k j + A t i k * B' k j)) t := by
  have h0 := (hA i 0).mul (hB 0 j)
  have h1 := (hA i 1).mul (hB 1 j)
  have hsum := HasDerivAt.add h0 h1
  have hfun : (fun s => (A s * B s) i j) =ᶠ[nhds t]
      ((fun s => A s i 0 * B s 0 j) + (fun s => A s i 1 * B s 1 j)) := by
    filter_upwards [] with s
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  simpa [Fin.sum_univ_succ] using hsum.congr_of_eventuallyEq hfun

/-- Before a syzygy, positive signed area makes the Jacobi matrix
    nonsingular. The determinant identity is the project's mass-normalized
    area formula. -/
theorem jacobiMatrix_det_pos_of_positive_area
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : 0 < signedDoubleArea q) :
    0 < Matrix.det (jacobiMatrix m q) := by
  rw [jacobiMatrix_det_eq_sqrtMass_mul_area m q hm0 hm1]
  exact mul_pos (mul_pos (sqrt_jacobiMu_pos m hm0 hm1)
    (sqrt_jacobiNu_pos m hm0 hm1 hm2)) harea

theorem jacobiMatrix_isUnit_of_positive_area
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : 0 < signedDoubleArea q) : IsUnit (jacobiMatrix m q) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  exact isUnit_iff_ne_zero.mpr
    (ne_of_gt (jacobiMatrix_det_pos_of_positive_area m q hm0 hm1 hm2 harea))

theorem jacobiMatrix_mul_nonsingInv_eq_one_of_positive_area
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : 0 < signedDoubleArea q) :
    jacobiMatrix m q * (jacobiMatrix m q)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv (jacobiMatrix m q)
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (jacobiMatrix_isUnit_of_positive_area m q hm0 hm1 hm2 harea))

theorem matrix_skew_acceleration_eq_zero
    (Q K : Matrix (Fin 2) (Fin 2) ℝ)
    (hKsym : Matrix.transpose K = K) :
    (-(Q * K)) * Matrix.transpose Q -
      Q * Matrix.transpose (-(Q * K)) = 0 := by
  rw [Matrix.transpose_neg, Matrix.transpose_mul, hKsym]
  noncomm_ring

theorem matrix_skew_acceleration_entry_sum_eq_zero
    (Q K : Matrix (Fin 2) (Fin 2) ℝ)
    (hKsym : Matrix.transpose K = K) (i j : Fin 2) :
    (∑ k : Fin 2, (-(Q * K)) i k * Q.transpose k j) -
      ∑ k : Fin 2, Q i k * (-(Q * K)).transpose k j = 0 := by
  have hs : ∀ a b, K a b = K b a := by
    intro a b
    have h := congrFun (congrFun hKsym a) b
    simpa [Matrix.transpose_apply] using h.symm
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, hs]
  ring

/-- Jacobi analogue of angular momentum: the skew part of `V Qᵀ`. -/
def jacobiSkewMatrixCurve (m : Fin 3 → ℝ) (z : ℝ → Phase) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let Q := jacobiMatrixCurve m (fun i s => (z s).1 i) t
  let V := jacobiMatrixCurve m (fun i s => (z s).2 i) t
  V * Matrix.transpose Q - Q * Matrix.transpose V

/-- Transposition only permutes the entries, so its derivative is inherited
    entrywise from the original matrix curve. -/
theorem hasDerivAt_matrixTranspose_entry
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A' : Matrix (Fin 2) (Fin 2) ℝ}
    {t : ℝ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (i j : Fin 2) :
    HasDerivAt (fun s => (Matrix.transpose (A s)) i j)
      ((Matrix.transpose A') i j) t := by
  simpa [Matrix.transpose_apply] using hA j i

/-- Skew matrix formed from a position matrix and its velocity matrix. -/
def matrixSkewCurve (Q V : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  V t * Matrix.transpose (Q t) - Q t * Matrix.transpose (V t)

/-- The derivative of the skew matrix of two arbitrary differentiable matrix
    curves, kept at the abstract matrix-curve level. -/
theorem hasDerivAt_matrixSkewCurve_entry
    {Q V : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {Q' V' : Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ}
    (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (Q' i j) t)
    (hV : ∀ i j, HasDerivAt (fun s => V s i j) (V' i j) t)
    (i j : Fin 2) :
    HasDerivAt (fun s => matrixSkewCurve Q V s i j)
      ((∑ k : Fin 2,
          (V' i k * (Q t).transpose k j + V t i k * Q'.transpose k j)) -
        ∑ k : Fin 2,
          (Q' i k * (V t).transpose k j + Q t i k * V'.transpose k j)) t := by
  have hVQt := hasDerivAt_matrixMul_entry hV
    (hasDerivAt_matrixTranspose_entry hQ) i j
  have hQVt := hasDerivAt_matrixMul_entry hQ
    (hasDerivAt_matrixTranspose_entry hV) i j
  have hsub := HasDerivAt.sub hVQt hQVt
  have hfun : (fun s => matrixSkewCurve Q V s i j) =ᶠ[nhds t]
      (fun s => (V s * Matrix.transpose (Q s) -
        Q s * Matrix.transpose (V s)) i j) := by
    filter_upwards [] with s
    rfl
  exact hsub.congr_of_eventuallyEq hfun

/-- If `Q' = V` and `V' = -QK` with symmetric K, every entry of the skew
    Jacobi matrix has zero derivative. -/
theorem hasDerivAt_matrixSkewCurve_entry_zero
    {Q V : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {K : Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ}
    (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (V t i j) t)
    (hV : ∀ i j, HasDerivAt (fun s => V s i j) (-(Q t * K) i j) t)
    (hKsym : Matrix.transpose K = K) (i j : Fin 2) :
    HasDerivAt (fun s => matrixSkewCurve Q V s i j) 0 t := by
  have hderiv := hasDerivAt_matrixSkewCurve_entry hQ hV i j
  have hvalue :
      (∑ k : Fin 2,
          (-(Q t * K) i k * (Q t).transpose k j + V t i k * (V t).transpose k j)) -
        ∑ k : Fin 2,
          (V t i k * (V t).transpose k j + Q t i k * (-(Q t * K)).transpose k j) = 0 := by
    have hs : ∀ a b, K a b = K b a := by
      intro a b
      have h := congrFun (congrFun hKsym a) b
      simpa [Matrix.transpose_apply] using h.symm
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hs]
    ring
  exact hderiv.congr_deriv hvalue

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Angular momentum, symmetry, and the Riccati equation", `eq:Wconstant`;
    the deduction from the formalized Newton matrix equation is project-derived.
    Newton's matrix equation makes the Jacobi skew matrix stationary at each
    collision-free time of a general-mass classical solution. -/
theorem generalNewton_jacobiSkewMatrixCurve_entry_deriv_zero
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (i j : Fin 2) :
    HasDerivAt (fun s => jacobiSkewMatrixCurve m z s i j) 0 t := by
  let Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s => jacobiMatrixCurve m (fun k τ => (z τ).1 k) s
  let V : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s => jacobiMatrixCurve m (fun k τ => (z τ).2 k) s
  let K := jacobiForceMatrix G m (z t).1
  have hQ : ∀ a b, HasDerivAt (fun s => Q s a b) (V t a b) t := by
    intro a b
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (generalNewton_jacobiPositionMatrix_deriv hsol ht hm0 hm1 hm2) a)) b
  have hV : ∀ a b, HasDerivAt (fun s => V s a b) (-(Q t * K) a b) t := by
    intro a b
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (generalNewton_jacobiMatrix_secondDerivative hsol ht hm0 hm1 hm2) a)) b
  have hKsym : Matrix.transpose K = K := by
    exact jacobiForceMatrix_symmetric G m (z t).1
  change HasDerivAt (fun s => matrixSkewCurve Q V s i j) 0 t
  exact hasDerivAt_matrixSkewCurve_entry_zero hQ hV hKsym i j

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Angular momentum, symmetry, and the Riccati equation", `eq:Wconstant`;
    this is the project-derived interval constancy consequence. The Jacobi
    skew matrix is constant on every preconnected solution domain. -/
theorem generalNewton_jacobiSkewMatrixCurve_eq_on
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiSkewMatrixCurve m z s = jacobiSkewMatrixCurve m z t := by
  ext i j
  change (fun τ => jacobiSkewMatrixCurve m z τ i j) s =
    (fun τ => jacobiSkewMatrixCurve m z τ i j) t
  apply hsol.1.is_const_of_deriv_eq_zero (f := fun τ => jacobiSkewMatrixCurve m z τ i j) hconn
  · intro τ hτ
    exact (generalNewton_jacobiSkewMatrixCurve_entry_deriv_zero
      hsol hτ hm0 hm1 hm2 i j).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [(generalNewton_jacobiSkewMatrixCurve_entry_deriv_zero
      hsol hτ hm0 hm1 hm2 i j).deriv]
    simp
  · exact hs
  · exact ht

/-- At an instant when all bodies are at rest, the Jacobi skew matrix is zero. -/
theorem jacobiSkewMatrixCurve_eq_zero_of_rest
    (m : Fin 3 → ℝ) (z : ℝ → Phase) (a : ℝ)
    (hrest : ∀ i, (z a).2 i = 0) :
    jacobiSkewMatrixCurve m z a = 0 := by
  have hvel : (fun i => (z a).2 i) = fun _ => (0 : Point) := by
    funext i
    exact hrest i
  have hV : jacobiMatrixCurve m (fun i s => (z s).2 i) a = 0 := by
    ext r c
    simp [jacobiMatrixCurve, jacobiMatrix, jacobiX, jacobiY,
      jacobiPairCenter, hvel]
  ext r c
  simp [jacobiSkewMatrixCurve, hV]

/-- Initial rest fixes the conserved Jacobi skew matrix to zero throughout
    the connected collision-free Newton solution interval. Source:
    [DroppingMontgomery2026], frozen 2026-10-29, same section, `eq:Wconstant`;
    the specialization to the project's initial-rest hypothesis is derived here. -/
theorem generalNewton_jacobiSkewMatrixCurve_eq_zero_of_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hrest : ∀ i, (z a).2 i = 0) :
    jacobiSkewMatrixCurve m z t = 0 := by
  have hconst := generalNewton_jacobiSkewMatrixCurve_eq_on
    hsol hconn ha ht hm0 hm1 hm2
  rw [jacobiSkewMatrixCurve_eq_zero_of_rest m z a hrest] at hconst
  exact hconst.symm

/-- A vanishing Jacobi skew matrix implies symmetry of the logarithmic
    derivative `Q⁻¹V`, whenever Q is nonsingular. -/
theorem matrix_nonsingInv_mul_velocity_symmetric_of_skew_zero
    (Q V : Matrix (Fin 2) (Fin 2) ℝ) (hdet : IsUnit Q.det)
    (hW : V * Q.transpose - Q * V.transpose = 0) :
    Matrix.transpose (Q⁻¹ * V) = Q⁻¹ * V := by
  have hdetT : IsUnit Q.transpose.det := by
    rw [Matrix.det_transpose]
    exact hdet
  have hEq : V * Q.transpose = Q * V.transpose := sub_eq_zero.mp hW
  have hmul : Q⁻¹ * V = V.transpose * Q.transpose⁻¹ := by
    calc
      Q⁻¹ * V = Q⁻¹ * V * 1 := by simp
      _ = Q⁻¹ * V * (Q.transpose * Q.transpose⁻¹) := by
        rw [Matrix.mul_nonsing_inv Q.transpose hdetT]
      _ = Q⁻¹ * (V * Q.transpose) * Q.transpose⁻¹ := by
        simp [Matrix.mul_assoc]
      _ = Q⁻¹ * (Q * V.transpose) * Q.transpose⁻¹ := by rw [hEq]
      _ = (Q⁻¹ * Q) * (V.transpose * Q.transpose⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = V.transpose * Q.transpose⁻¹ := by
        rw [Matrix.nonsing_inv_mul Q hdet]
        simp
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hmul.symm]

/-- Logarithmic derivative `C=Q⁻¹Q'` in the mass-normalized Jacobi frame. -/
def jacobiRiccatiMatrixCurve (m : Fin 3 → ℝ) (z : ℝ → Phase) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (jacobiMatrix m (fun i => (z t).1 i))⁻¹ *
    jacobiMatrix m (fun i => (z t).2 i)

/-- Before a syzygy, the conserved zero Jacobi skew matrix implies that the
    logarithmic derivative C is symmetric. Source: [DroppingMontgomery2026],
    frozen 2026-10-29, same section, `eq:Wconstant` and `eq:riccati`;
    this inverse-matrix deduction is project-derived. -/
theorem generalNewton_jacobiRiccatiMatrix_symmetric
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : 0 < signedDoubleArea (z t).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    Matrix.transpose (jacobiRiccatiMatrixCurve m z t) =
      jacobiRiccatiMatrixCurve m z t := by
  let Q := jacobiMatrix m (fun i => (z t).1 i)
  let V := jacobiMatrix m (fun i => (z t).2 i)
  have hW := generalNewton_jacobiSkewMatrixCurve_eq_zero_of_rest
    hsol hconn ha ht hm0 hm1 hm2 hrest
  have hunit : IsUnit Q := by
    exact jacobiMatrix_isUnit_of_positive_area m (z t).1 hm0 hm1 hm2 harea
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hunit
  change Matrix.transpose (Q⁻¹ * V) = Q⁻¹ * V
  exact matrix_nonsingInv_mul_velocity_symmetric_of_skew_zero Q V hdet
    (by simpa [jacobiSkewMatrixCurve, jacobiMatrixCurve, Q, V] using hW)

/-- Derivative of the determinant along a differentiable 2×2 matrix curve. -/
theorem hasDerivAt_matrixDet_finTwo
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A' : Matrix (Fin 2) (Fin 2) ℝ}
    {t : ℝ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt (fun s => Matrix.det (A s))
      (A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1 -
        (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0)) t := by
  have hdiag := (hA 0 0).mul (hA 1 1)
  have hoff := (hA 0 1).mul (hA 1 0)
  have hsub := HasDerivAt.sub hdiag hoff
  have hfun : (fun s => Matrix.det (A s)) =ᶠ[nhds t]
      (fun s => A s 0 0 * A s 1 1 - A s 0 1 * A s 1 0) := by
    filter_upwards [] with s
    rw [Matrix.det_fin_two]
  have htarget : A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1 -
      (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0) =
      (A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1) -
        (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0) := by ring
  rw [htarget]
  exact hsub.congr_of_eventuallyEq hfun

/-- Entrywise derivative of the inverse of an invertible 2×2 matrix curve,
    expressed through the determinant and adjugate derivatives. -/
theorem hasDerivAt_matrixInv_finTwo_entry
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A' : Matrix (Fin 2) (Fin 2) ℝ}
    {t : ℝ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hdet : Matrix.det (A t) ≠ 0) (i j : Fin 2) :
    HasDerivAt (fun s => (A s)⁻¹ i j)
      ((-( (A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1 -
          (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0)) /
            Matrix.det (A t) ^ 2)) * (A t).adjugate i j +
        (Matrix.det (A t))⁻¹ * (Matrix.adjugate A') i j) t := by
  let d' := A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1 -
    (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0)
  have hD := hasDerivAt_matrixDet_finTwo hA
  have hDinv := hD.inv hdet
  have hAdj : ∀ a b, HasDerivAt (fun s => (A s).adjugate a b)
      ((Matrix.adjugate A') a b) t := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.adjugate_fin_two, Matrix.of_apply] <;>
      first | exact (hA 1 1) | exact ((hA 0 1).neg) |
        exact ((hA 1 0).neg) | exact (hA 0 0)
  have hprod := hDinv.mul (hAdj i j)
  have hfun : (fun s => (A s)⁻¹ i j) =ᶠ[nhds t]
      (fun s => (Matrix.det (A s))⁻¹ * (A s).adjugate i j) := by
    filter_upwards [] with s
    simp [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul]
  have hvalue :
      (-(A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1 -
          (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0)) /
            Matrix.det (A t) ^ 2) * (A t).adjugate i j +
        ((fun s => (Matrix.det (A s))⁻¹) t) * (Matrix.adjugate A') i j =
      (-( (A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1 -
          (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0)) /
            Matrix.det (A t) ^ 2)) * (A t).adjugate i j +
        (Matrix.det (A t))⁻¹ * (Matrix.adjugate A') i j := by
    simp
    ring
  exact (hprod.congr_of_eventuallyEq hfun).congr_deriv hvalue

/-- Coordinate proof of the usual inverse derivative formula for an
    invertible 2×2 matrix curve. The determinant stays nonzero near t, so the
    product of the inverse and the original matrix is locally the identity. -/
theorem hasDerivAt_matrixInv_finTwo_formula_entry
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A' : Matrix (Fin 2) (Fin 2) ℝ}
    {t : ℝ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hdet : Matrix.det (A t) ≠ 0) (i j : Fin 2) :
    HasDerivAt (fun s => (A s)⁻¹ i j)
      (-( (A t)⁻¹ * A' * (A t)⁻¹) i j) t := by
  let M : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => (A s)⁻¹
  let D : Matrix (Fin 2) (Fin 2) ℝ := fun a b =>
    (-( (A' 0 0 * A t 1 1 + A t 0 0 * A' 1 1 -
      (A' 0 1 * A t 1 0 + A t 0 1 * A' 1 0)) /
        Matrix.det (A t) ^ 2)) * (A t).adjugate a b +
      (Matrix.det (A t))⁻¹ * (Matrix.adjugate A') a b
  have hM : ∀ a b, HasDerivAt (fun s => M s a b) (D a b) t := by
    intro a b
    simpa [M, D] using hasDerivAt_matrixInv_finTwo_entry hA hdet a b
  have hDdet := hasDerivAt_matrixDet_finTwo hA
  have hdet_eventually : ∀ᶠ s in nhds t, Matrix.det (A s) ≠ 0 :=
    hDdet.continuousAt.eventually_ne hdet
  have hconst : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) 0 t :=
    hasDerivAt_const t _
  have hDA : D * A t + M t * A' = 0 := by
    ext a b
    have hconst_ab :
        HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) a b) 0 t :=
      hasDerivAt_const t _
    have h := HasDerivAt.unique (hasDerivAt_matrixMul_entry hM hA a b)
      (hconst_ab.congr_of_eventuallyEq (by
        filter_upwards [hdet_eventually] with s hs
        have hunit : IsUnit (Matrix.det (A s)) := isUnit_iff_ne_zero.mpr hs
        have hmul := Matrix.nonsing_inv_mul (A s) hunit
        simpa [M] using congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B a b) hmul))
    change (∑ k : Fin 2, D a k * A t k b) +
      (∑ k : Fin 2, M t a k * A' k b) = 0
    simp only [Fin.sum_univ_succ] at h ⊢
    linear_combination h
  have hdetUnit : IsUnit (Matrix.det (A t)) := isUnit_iff_ne_zero.mpr hdet
  have hAM : A t * M t = 1 := Matrix.mul_nonsing_inv (A t) hdetUnit
  have hDM : D = -(M t * A' * M t) := by
    have hleft : D * A t = -(M t * A') := by
      ext a b
      have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B a b) hDA
      simpa [Matrix.add_apply] using eq_neg_of_add_eq_zero_left h
    calc
      D = D * 1 := by simp
      _ = D * (A t * M t) := by rw [hAM]
      _ = (D * A t) * M t := by simp [Matrix.mul_assoc]
      _ = (-(M t * A')) * M t := by rw [hleft]
      _ = -(M t * A' * M t) := by noncomm_ring
  have htarget := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B i j) hDM
  have hfinal := (hM i j).congr_deriv htarget
  simpa [M] using hfinal

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Angular momentum, symmetry, and the Riccati equation", `eq:riccati`;
    the coordinate inverse differentiation and the solution-level adapter are
    project-derived. Along a positive-area general-mass Newton solution, the
    logarithmic derivative C=Q⁻¹Q' satisfies the symmetric Riccati equation. -/
theorem generalNewton_jacobiRiccatiMatrix_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : 0 < signedDoubleArea (z t).1) (i j : Fin 2) :
    HasDerivAt (fun s => jacobiRiccatiMatrixCurve m z s i j)
      (-(jacobiRiccatiMatrixCurve m z t * jacobiRiccatiMatrixCurve m z t +
        jacobiForceMatrix G m (z t).1) i j) t := by
  let Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s => jacobiMatrixCurve m (fun k τ => (z τ).1 k) s
  let V : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s => jacobiMatrixCurve m (fun k τ => (z τ).2 k) s
  let K := jacobiForceMatrix G m (z t).1
  let M := (Q t)⁻¹
  have hQ : ∀ a b, HasDerivAt (fun s => Q s a b) (V t a b) t := by
    intro a b
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (generalNewton_jacobiPositionMatrix_deriv hsol ht hm0 hm1 hm2) a)) b
  have hV : ∀ a b, HasDerivAt (fun s => V s a b) (-(Q t * K) a b) t := by
    intro a b
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (generalNewton_jacobiMatrix_secondDerivative hsol ht hm0 hm1 hm2) a)) b
  have hdet : Matrix.det (Q t) ≠ 0 := by
    exact ne_of_gt (jacobiMatrix_det_pos_of_positive_area m (z t).1
      hm0 hm1 hm2 harea)
  have hMinv : ∀ a b, HasDerivAt (fun s => (Q s)⁻¹ a b)
      (-(M * V t * M) a b) t := by
    intro a b
    exact hasDerivAt_matrixInv_finTwo_formula_entry hQ hdet a b
  have hC := hasDerivAt_matrixMul_entry hMinv hV i j
  have hMQ : M * Q t = 1 := by
    exact Matrix.nonsing_inv_mul (Q t)
      (isUnit_iff_ne_zero.mpr hdet)
  have hmat :
      (-(M * V t * M)) * V t + M * (-(Q t * K)) =
        -((M * V t) * (M * V t) + K) := by
    calc
      (-(M * V t * M)) * V t + M * (-(Q t * K)) =
          -((M * V t) * (M * V t)) - (M * Q t) * K := by noncomm_ring
      _ = -((M * V t) * (M * V t)) - K := by rw [hMQ]; noncomm_ring
      _ = -((M * V t) * (M * V t) + K) := by noncomm_ring
  have hvalue :
      (∑ k : Fin 2,
        (-(M * V t * M) i k * V t k j + M i k * (-(Q t * K)) k j)) =
        (-(jacobiRiccatiMatrixCurve m z t * jacobiRiccatiMatrixCurve m z t + K) i j) := by
    have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B i j) hmat
    change (∑ k : Fin 2,
        (-(M * V t * M) i k * V t k j + M i k * (-(Q t * K)) k j)) =
      (-( (M * V t) * (M * V t) + K)) i j
    simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hh ⊢
    linear_combination hh
  have h := hC.congr_of_eventuallyEq (by
    filter_upwards [] with s
    rfl)
  have htarget :
      (∑ k : Fin 2,
        (-(M * V t * M) i k * V t k j + M i k * (-(Q t * K)) k j)) =
        (-(jacobiRiccatiMatrixCurve m z t * jacobiRiccatiMatrixCurve m z t +
          jacobiForceMatrix G m (z t).1) i j) := by
    simpa [K] using hvalue
  exact h.congr_deriv htarget

/-- Differentiate a fixed-vector quadratic form entrywise along a matrix curve.
    This is the coordinate calculus adapter for [DroppingMontgomery2026],
    frozen 2026-10-29, `eq:Cnegative`; the finite-sum proof is project-derived. -/
theorem hasDerivAt_matrixQuadratic_curve
    {C : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {C' : Matrix (Fin 2) (Fin 2) ℝ}
    {w : Fin 2 → ℝ} {t : ℝ}
    (hC : ∀ i j, HasDerivAt (fun s => C s i j) (C' i j) t) :
    HasDerivAt (fun s => matrixQuadratic (C s) w)
      (matrixQuadratic C' w) t := by
  have h00 := (HasDerivAt.const_mul (w 0) (hC 0 0)).mul_const (w 0)
  have h01 := (HasDerivAt.const_mul (w 0) (hC 0 1)).mul_const (w 1)
  have h10 := (HasDerivAt.const_mul (w 1) (hC 1 0)).mul_const (w 0)
  have h11 := (HasDerivAt.const_mul (w 1) (hC 1 1)).mul_const (w 1)
  have hsum := HasDerivAt.add (HasDerivAt.add h00 h01)
    (HasDerivAt.add h10 h11)
  have hfun : (fun s => matrixQuadratic (C s) w) =ᶠ[nhds t]
      (fun s => ((w 0 * C s 0 0) * w 0 + (w 0 * C s 0 1) * w 1) +
        ((w 1 * C s 1 0) * w 0 + (w 1 * C s 1 1) * w 1)) := by
    filter_upwards [] with s
    simp [matrixQuadratic, Fin.sum_univ_succ]
    ring
  have htarget :
      (w 0 * C' 0 0) * w 0 + (w 0 * C' 0 1) * w 1 +
        ((w 1 * C' 1 0) * w 0 + (w 1 * C' 1 1) * w 1) =
      matrixQuadratic C' w := by
    simp [matrixQuadratic, Fin.sum_univ_succ]
    ring
  exact (hsum.congr_of_eventuallyEq hfun).congr_deriv htarget

/-- Squared Frobenius norm of a 2×2 matrix. -/
def matrixFrobeniusSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (A i j) ^ 2

/-- Derivative of the squared Frobenius norm along a matrix curve. -/
theorem hasDerivAt_matrixFrobeniusSq
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A' : Matrix (Fin 2) (Fin 2) ℝ}
    {t : ℝ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt (fun s => matrixFrobeniusSq (A s))
      (2 * ∑ i : Fin 2, ∑ j : Fin 2, A t i j * A' i j) t := by
  have h00 := (hA 0 0).mul (hA 0 0)
  have h01 := (hA 0 1).mul (hA 0 1)
  have h10 := (hA 1 0).mul (hA 1 0)
  have h11 := (hA 1 1).mul (hA 1 1)
  have hsum := HasDerivAt.add h00 (HasDerivAt.add h01 (HasDerivAt.add h10 h11))
  have hfun : (fun s => matrixFrobeniusSq (A s)) =ᶠ[nhds t]
      (fun s => (A s 0 0) ^ 2 + ((A s 0 1) ^ 2 +
        ((A s 1 0) ^ 2 + (A s 1 1) ^ 2))) := by
    filter_upwards [] with s
    simp [matrixFrobeniusSq, Fin.sum_univ_succ]
    ring
  have hfun' : (fun s => (A s 0 0) ^ 2 + ((A s 0 1) ^ 2 +
      ((A s 1 0) ^ 2 + (A s 1 1) ^ 2))) =ᶠ[nhds t]
      (fun s => A s 0 0 * A s 0 0 + (A s 0 1 * A s 0 1 +
        (A s 1 0 * A s 1 0 + A s 1 1 * A s 1 1))) := by
    filter_upwards [] with s
    simp [pow_two]
  have htarget :
      (A' 0 0 * A t 0 0 + A t 0 0 * A' 0 0) +
        ((A' 0 1 * A t 0 1 + A t 0 1 * A' 0 1) +
          ((A' 1 0 * A t 1 0 + A t 1 0 * A' 1 0) +
            (A' 1 1 * A t 1 1 + A t 1 1 * A' 1 1))) =
      2 * ∑ i : Fin 2, ∑ j : Fin 2, A t i j * A' i j := by
    simp [Fin.sum_univ_succ]
    ring
  exact (hsum.congr_of_eventuallyEq (hfun.trans hfun')).congr_deriv htarget

/-- If V=QC and C is symmetric, the Frobenius pairing of Q and V is the
    sum of the two row quadratic forms of C. -/
theorem matrixFrobeniusPairing_eq_rowQuadraticSum
    (Q C V : Matrix (Fin 2) (Fin 2) ℝ)
    (hV : V = Q * C) (hCsym : Matrix.transpose C = C) :
    (∑ i : Fin 2, ∑ j : Fin 2, Q i j * V i j) =
      ∑ i : Fin 2, matrixQuadratic C (fun j => Q i j) := by
  have hsym : ∀ i j, C i j = C j i := by
    intro i j
    have h := congrFun (congrFun hCsym i) j
    simpa [Matrix.transpose_apply] using h.symm
  rw [hV]
  simp [matrixQuadratic, Matrix.mul_apply, Fin.sum_univ_succ, hsym]
  ring

/-- Jacobi inertia along a body-position curve. -/
def jacobiMomentCurve (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  jacobiMoment m (fun i => q i t)

theorem jacobiMoment_eq_matrixFrobeniusSq
    (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    jacobiMoment m q = matrixFrobeniusSq (jacobiMatrix m q) := by
  rw [← jacobiMatrix_trace_mul_transpose_eq_jacobiMoment]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
    matrixFrobeniusSq, Fin.sum_univ_succ]
  ring

/-- Along a Newton solution the Jacobi inertia derivative is twice the
    Frobenius pairing of the position and velocity Jacobi matrices. The static
    identity comes from `eq:massmetric`; this derivative adapter is derived. -/
theorem generalNewton_jacobiMomentCurve_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    HasDerivAt (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s)
      (2 * ∑ i : Fin 2, ∑ j : Fin 2,
        jacobiMatrix m (fun i => (z t).1 i) i j *
          jacobiMatrix m (fun i => (z t).2 i) i j) t := by
  let Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s => jacobiMatrixCurve m (fun i τ => (z τ).1 i) s
  have hQ : ∀ i j, HasDerivAt (fun s => Q s i j)
      (jacobiMatrix m (fun i => (z t).2 i) i j) t := by
    intro i j
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (generalNewton_jacobiPositionMatrix_deriv hsol ht hm0 hm1 hm2) i)) j
  have hderiv := hasDerivAt_matrixFrobeniusSq hQ
  have hfun : (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) =ᶠ[nhds t]
      (fun s => matrixFrobeniusSq (Q s)) := by
    filter_upwards [] with s
    exact (jacobiMoment_eq_matrixFrobeniusSq m (fun i => (z s).1 i))
  simpa [jacobiMomentCurve, Q, jacobiMatrixCurve] using
    hderiv.congr_of_eventuallyEq hfun

theorem matrix_row_ne_zero_of_det_ne_zero
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hdet : Q.det ≠ 0) (i : Fin 2) :
    (fun j => Q i j) ≠ 0 := by
  intro hrow
  have h0 : Q i 0 = 0 := by
    have h := congrFun hrow 0
    simpa using h
  have h1 : Q i 1 = 0 := by
    have h := congrFun hrow 1
    simpa using h
  fin_cases i
  · have h00 : Q 0 0 = 0 := by simpa using h0
    have h01 : Q 0 1 = 0 := by simpa using h1
    simp [Matrix.det_fin_two, h00, h01] at hdet
  · have h10 : Q 1 0 = 0 := by simpa using h0
    have h11 : Q 1 1 = 0 := by simpa using h1
    simp [Matrix.det_fin_two, h10, h11] at hdet

/-- For symmetric `C`, the quadratic form of `C²` is the sum of squares of
    the coordinates of `Cw`. -/
theorem matrixQuadratic_square_eq_sum_squares
    (C : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ)
    (hsym : Matrix.transpose C = C) :
    matrixQuadratic (C * C) w =
      ∑ i : Fin 2, (∑ j : Fin 2, C i j * w j) ^ 2 := by
  have hsym' : ∀ i j, C i j = C j i := by
    intro i j
    have h := congrFun (congrFun hsym i) j
    simpa [Matrix.transpose_apply] using h.symm
  simp [matrixQuadratic, Matrix.mul_apply, Fin.sum_univ_succ, hsym']
  ring

/-- The symmetric Riccati right-hand side `-C²-K` has strictly negative
    quadratic form whenever K is positive definite. This isolates the scalar
    monotonicity input used in the project manuscript's `eq:Cnegative`.
    Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Angular momentum, symmetry, and the Riccati equation", `eq:riccati` and
    `eq:Cnegative`; this pointwise algebra lemma is project-derived. -/
theorem matrixQuadratic_riccati_rhs_neg
    (C K : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ)
    (hsym : Matrix.transpose C = C)
    (hK : 0 < matrixQuadratic K w) :
    matrixQuadratic (-(C * C) - K) w < 0 := by
  have hCnonneg : 0 ≤ matrixQuadratic (C * C) w := by
    rw [matrixQuadratic_square_eq_sum_squares C w hsym]
    positivity
  have hsplit :
      matrixQuadratic (-(C * C) - K) w =
        -matrixQuadratic (C * C) w - matrixQuadratic K w := by
    simp [matrixQuadratic, Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  rw [hsplit]
  linarith

/-- For every nonzero fixed coefficient vector, the Riccati quadratic form
    has strictly negative derivative on the positive-area interval. Source:
    [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Angular momentum, symmetry, and the Riccati equation", `eq:Cnegative`;
    the solution-level derivative adapter is project-derived. -/
theorem generalNewton_jacobiRiccatiQuadratic_deriv_neg
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G) (harea : 0 < signedDoubleArea (z t).1)
    (hrest : ∀ i, (z a).2 i = 0) (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    deriv (fun s => matrixQuadratic (jacobiRiccatiMatrixCurve m z s) w) t < 0 := by
  have hC : ∀ i j, HasDerivAt
      (fun s => jacobiRiccatiMatrixCurve m z s i j)
      (-(jacobiRiccatiMatrixCurve m z t * jacobiRiccatiMatrixCurve m z t +
        jacobiForceMatrix G m (z t).1) i j) t := by
    intro i j
    exact generalNewton_jacobiRiccatiMatrix_deriv hsol ht hm0 hm1 hm2 harea i j
  have hquad := hasDerivAt_matrixQuadratic_curve (w := w) hC
  have hsym := generalNewton_jacobiRiccatiMatrix_symmetric
    hsol hconn ha ht hm0 hm1 hm2 harea hrest
  have hK := jacobiForceMatrix_quadratic_pos G m (z t).1 hG
    hm0 hm1 hm2 (hsol.2 t ht).1 w hw
  have hneg := matrixQuadratic_riccati_rhs_neg
    (jacobiRiccatiMatrixCurve m z t) (jacobiForceMatrix G m (z t).1)
    w hsym hK
  rw [hquad.deriv]
  have hmatrix :
      (fun i j => -(jacobiRiccatiMatrixCurve m z t *
        jacobiRiccatiMatrixCurve m z t + jacobiForceMatrix G m (z t).1) i j) =
        -(jacobiRiccatiMatrixCurve m z t * jacobiRiccatiMatrixCurve m z t) -
          jacobiForceMatrix G m (z t).1 := by
    ext i j
    simp
    ring
  rw [hmatrix]
  exact hneg

/-- On any compact interval that stays before the first zero of area, each
    fixed nonzero Riccati quadratic form is strictly decreasing. -/
theorem generalNewton_jacobiRiccatiQuadratic_strictAntiOn_Icc
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a s t : ℝ} (ha : a ∈ I) (hIcc : Set.Icc s t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G)
    (harea : ∀ x ∈ Set.Icc s t, 0 < signedDoubleArea (z x).1)
    (hrest : ∀ i, (z a).2 i = 0) (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    StrictAntiOn (fun x => matrixQuadratic (jacobiRiccatiMatrixCurve m z x) w)
      (Set.Icc s t) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc s t)
  · intro x hx
    have htime := hIcc hx
    have hC : ∀ i j, HasDerivAt
        (fun u => jacobiRiccatiMatrixCurve m z u i j)
        (-(jacobiRiccatiMatrixCurve m z x * jacobiRiccatiMatrixCurve m z x +
          jacobiForceMatrix G m (z x).1) i j) x := by
      intro i j
      exact generalNewton_jacobiRiccatiMatrix_deriv
        hsol htime hm0 hm1 hm2 (harea x hx) i j
    exact (hasDerivAt_matrixQuadratic_curve (w := w) hC).continuousAt.continuousWithinAt
  · intro x hxInterior
    have hx : x ∈ Set.Icc s t := interior_subset hxInterior
    exact generalNewton_jacobiRiccatiQuadratic_deriv_neg
      hsol hconn ha (hIcc hx) hm0 hm1 hm2 hG (harea x hx) hrest w hw

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Angular momentum, symmetry, and the Riccati equation", `eq:endpointbound`;
    this interior strict-derivative statement is project-derived from the
    Riccati monotonicity and Jacobi trace identity. On an interval of positive
    oriented area after initial rest, the Jacobi inertia has strictly negative
    derivative. -/
theorem generalNewton_jacobiMomentCurve_deriv_neg
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : a < t) (hIcc : Set.Icc a t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G)
    (harea : ∀ x ∈ Set.Icc a t, 0 < signedDoubleArea (z x).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) t < 0 := by
  have hareaT := harea t ⟨le_of_lt ht, le_rfl⟩
  let Q := jacobiMatrix m (fun i => (z t).1 i)
  let V := jacobiMatrix m (fun i => (z t).2 i)
  let C := jacobiRiccatiMatrixCurve m z t
  have hCsym := generalNewton_jacobiRiccatiMatrix_symmetric
    hsol hconn ha (hIcc ⟨le_of_lt ht, le_rfl⟩)
      hm0 hm1 hm2 hareaT hrest
  have hdetpos := jacobiMatrix_det_pos_of_positive_area m (z t).1
    hm0 hm1 hm2 hareaT
  have hdet : Q.det ≠ 0 := ne_of_gt (by simpa [Q] using hdetpos)
  have hVeq : V = Q * C := by
    dsimp [Q, V, C, jacobiRiccatiMatrixCurve]
    have hright := Matrix.mul_nonsing_inv
      (jacobiMatrix m (fun i => (z t).1 i)) (isUnit_iff_ne_zero.mpr hdet)
    calc
      jacobiMatrix m (fun i => (z t).2 i) =
          (jacobiMatrix m (fun i => (z t).1 i) *
            ((jacobiMatrix m (fun i => (z t).1 i))⁻¹)) *
              jacobiMatrix m (fun i => (z t).2 i) := by rw [hright]; simp
      _ = jacobiMatrix m (fun i => (z t).1 i) *
          (((jacobiMatrix m (fun i => (z t).1 i))⁻¹) *
            jacobiMatrix m (fun i => (z t).2 i)) := by rw [Matrix.mul_assoc]
  have hrow0 := matrix_row_ne_zero_of_det_ne_zero Q hdet 0
  have hrow1 := matrix_row_ne_zero_of_det_ne_zero Q hdet 1
  have hAnti0 := generalNewton_jacobiRiccatiQuadratic_strictAntiOn_Icc
    hsol hconn ha hIcc hm0 hm1 hm2 hG harea hrest
      (fun j => Q 0 j) hrow0
  have hAnti1 := generalNewton_jacobiRiccatiQuadratic_strictAntiOn_Icc
    hsol hconn ha hIcc hm0 hm1 hm2 hG harea hrest
      (fun j => Q 1 j) hrow1
  have hC0 : jacobiRiccatiMatrixCurve m z a = 0 := by
    have hvel : (fun i => (z a).2 i) = fun _ => (0 : Point) := by
      funext i
      exact hrest i
    have hV0 : jacobiMatrix m (fun i => (z a).2 i) = 0 := by
      rw [hvel]
      ext r c
      simp [jacobiMatrix, jacobiX, jacobiY, jacobiPairCenter]
    change (jacobiMatrix m (fun i => (z a).1 i))⁻¹ *
      jacobiMatrix m (fun i => (z a).2 i) = 0
    rw [hV0]
    simp
  have hphi0 : matrixQuadratic C (fun j => Q 0 j) < 0 := by
    have h := hAnti0 ⟨le_rfl, le_of_lt ht⟩ ⟨le_of_lt ht, le_rfl⟩ ht
    simpa [C, hC0, matrixQuadratic] using h
  have hphi1 : matrixQuadratic C (fun j => Q 1 j) < 0 := by
    have h := hAnti1 ⟨le_rfl, le_of_lt ht⟩ ⟨le_of_lt ht, le_rfl⟩ ht
    simpa [C, hC0, matrixQuadratic] using h
  have hpair := matrixFrobeniusPairing_eq_rowQuadraticSum Q C V hVeq hCsym
  have hderiv := generalNewton_jacobiMomentCurve_deriv hsol
    (hIcc ⟨le_of_lt ht, le_rfl⟩) hm0 hm1 hm2
  rw [hderiv.deriv, hpair]
  simp [Fin.sum_univ_succ]
  nlinarith

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Angular momentum, symmetry, and the Riccati equation", `eq:endpointbound`.
    The strict derivative estimate above yields a nonincreasing Jacobi moment
    from initial rest on every compact positive-area interval. -/
theorem generalNewton_negJacobiMoment_monotoneOn_Icc
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (ha : a ∈ I) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    MonotoneOn (fun t => -jacobiMomentCurve m (fun i s => (z s).1 i) t)
      (Set.Icc a T) := by
  apply monotoneOn_of_hasDerivAt_nonneg (convex_Icc a T)
  · intro t ht
    exact (generalNewton_jacobiMomentCurve_deriv hsol (hIcc ht) hm0 hm1 hm2).neg
  · intro t ht
    have hderiv := generalNewton_jacobiMomentCurve_deriv hsol (hIcc ht)
      hm0 hm1 hm2
    by_cases hta : t = a
    · subst t
      have hVzero : jacobiMatrix m (fun i => (z a).2 i) = 0 := by
        ext r c
        fin_cases c <;> simp [jacobiMatrix, jacobiX, jacobiY,
          jacobiPairCenter, hrest]
      simp [hVzero]
    · have hlt : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      have hstrict := generalNewton_jacobiMomentCurve_deriv_neg hsol hconn
        ha hlt (fun s hs => hIcc ⟨hs.1, le_trans hs.2 ht.2⟩)
        hm0 hm1 hm2 hG
        (fun s hs => harea s ⟨hs.1, le_trans hs.2 ht.2⟩) hrest
      rw [hderiv.deriv] at hstrict
      linarith

/-- The Jacobi moment remains strictly below every earlier value at a regular
    endpoint of a positive-area interval, even when the endpoint itself is a
    syzygy and the Riccati matrix is singular there. The proof uses continuity
    of the moment on the closed interval and the derivative test only on its
    interior. -/
theorem generalNewton_jacobiMomentCurve_strictDecrease_to_endpoint
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea₀ : 0 < signedDoubleArea (z a).1)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    ∀ t ∈ Set.Ico a T,
      jacobiMomentCurve m (fun i s => (z s).1 i) T <
        jacobiMomentCurve m (fun i s => (z s).1 i) t := by
  let J : ℝ → ℝ := fun t => jacobiMomentCurve m (fun i s => (z s).1 i) t
  have ha : a ∈ I := hIcc ⟨le_rfl, le_of_lt haT⟩
  have hzcont : ContinuousOn z (Set.Icc a T) := by
    intro t ht
    exact (hsol.2 t (hIcc ht)).2.continuousAt.continuousWithinAt
  have hJfield : Continuous (fun q : Phase => jacobiMoment m q.1) := by
    unfold jacobiMoment jacobiX jacobiY jacobiPairCenter
    fun_prop
  have hJcont : ContinuousOn J (Set.Icc a T) := by
    dsimp [J, jacobiMomentCurve]
    exact hJfield.continuousOn.comp hzcont (by
      intro t ht
      exact Set.mem_univ (z t))
  have hJanti : StrictAntiOn J (Set.Icc a T) :=
    strictAntiOn_of_deriv_neg (convex_Icc a T) hJcont (by
      intro t ht
      have htInterior : a < t ∧ t < T := by
        simpa [interior_Icc] using ht
      have htI : t ∈ I := hIcc ⟨le_of_lt htInterior.1, le_of_lt htInterior.2⟩
      have hJnegative := generalNewton_jacobiMomentCurve_deriv_neg hsol hconn
        ha htInterior.1 (fun s hs => hIcc ⟨hs.1, le_trans hs.2 (le_of_lt htInterior.2)⟩)
        hm0 hm1 hm2 hG
        (fun s hs => by
          by_cases hsa : s = a
          · subst s
            simpa using harea₀
          · have has : a < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
            exact hareaPre s ⟨hs.1,
              lt_of_le_of_lt hs.2 htInterior.2⟩)
        hrest
      change deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) t < 0
        at hJnegative
      simpa [J] using hJnegative)
  intro t ht
  have htIcc : t ∈ Set.Icc a T := ⟨ht.1, le_of_lt ht.2⟩
  exact hJanti htIcc (show T ∈ Set.Icc a T from ⟨le_of_lt haT, le_rfl⟩) ht.2

/-- If the center of mass is initially at the origin, the physical mass
    moment about the origin has the same strict endpoint decrease as the
    Jacobi moment. -/
theorem generalNewton_massMomentCurve_strictDecrease_to_endpoint_of_centered
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hcenter : weightedPosition m (z a).1 = 0)
    (harea₀ : 0 < signedDoubleArea (z a).1)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    ∀ t ∈ Set.Ico a T,
      massMomentCurve m (fun i s => (z s).1 i) T <
        massMomentCurve m (fun i s => (z s).1 i) t := by
  have hJacobi := generalNewton_jacobiMomentCurve_strictDecrease_to_endpoint
    hsol hconn haT hIcc hm0 hm1 hm2 hG harea₀ hareaPre hrest
  have ha : a ∈ I := hIcc ⟨le_rfl, le_of_lt haT⟩
  have hcenterAt : ∀ t ∈ Set.Icc a T, weightedPosition m (z t).1 = 0 := by
    intro t ht
    have hcoordinate : ∀ k : Fin 2,
        generalPositionCoordinateCurve m (fun i s => (z s).1 i) k a =
          generalPositionCoordinateCurve m (fun i s => (z s).1 i) k t := by
      intro k
      exact generalPositionCoordinate_eq_on_of_initial_rest
        hsol hconn ha hrest (hIcc ⟨le_rfl, le_of_lt haT⟩) (hIcc ht)
    ext k
    have hstart : generalPositionCoordinateCurve m
        (fun i s => (z s).1 i) k a = 0 := by
      have hcenterK := congrArg (fun p : Point => p k) hcenter
      simpa [generalPositionCoordinateCurve, weightedPosition] using
        hcenterK
    have hnow : generalPositionCoordinateCurve m
        (fun i s => (z s).1 i) k t = 0 :=
      (hcoordinate k).symm.trans hstart
    simpa [generalPositionCoordinateCurve, weightedPosition] using hnow
  intro t ht
  have hTcenter := hcenterAt T ⟨le_of_lt haT, le_rfl⟩
  have htcenter := hcenterAt t ⟨ht.1, le_of_lt ht.2⟩
  have hTmoment := massMoment_eq_jacobiMoment_of_centered m (z T).1
    hm0 hm1 hm2 hTcenter
  have htmoment := massMoment_eq_jacobiMoment_of_centered m (z t).1
    hm0 hm1 hm2 htcenter
  have hstrict := hJacobi t ht
  simpa [massMomentCurve, jacobiMomentCurve, hTmoment, htmoment] using hstrict

end

end DroppingThreeBodies
