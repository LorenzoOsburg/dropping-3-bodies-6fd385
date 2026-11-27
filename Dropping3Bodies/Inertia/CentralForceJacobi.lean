module

public import Dropping3Bodies.Dynamics.CentralForce
public import Dropping3Bodies.Inertia.AbstractJacobi
public import Dropping3Bodies.Inertia.JacobiTensor
public import Dropping3Bodies.Inertia.InitialBranchMonotonicity

@[expose] public section

/-! The physical adapter from symmetric central forces to abstract Jacobi
dynamics. The outer-product weights are physical forces, with no extra masses. -/

namespace DroppingThreeBodies.CentralForce

noncomputable section

/-- Three arbitrary unordered-pair weights in the existing Jacobi convention. -/
def weightedForceMatrix (m : Fin 3 → ℝ) (w01 w02 w12 : ℝ) : AbstractJacobi.Mat :=
  fun a b =>
    w01 * jacobiPairCoeff01 m a * jacobiPairCoeff01 m b +
    w02 * jacobiPairCoeff02 m a * jacobiPairCoeff02 m b +
    w12 * jacobiPairCoeff12 m a * jacobiPairCoeff12 m b

theorem weightedForceMatrix_symmetric (m : Fin 3 → ℝ) (w01 w02 w12 : ℝ) :
    (weightedForceMatrix m w01 w02 w12).transpose =
      weightedForceMatrix m w01 w02 w12 := by
  ext a b
  simp only [Matrix.transpose_apply, weightedForceMatrix]
  ring

theorem weightedForceMatrix_quadratic (m : Fin 3 → ℝ) (w01 w02 w12 : ℝ)
    (w : Fin 2 → ℝ) :
    matrixQuadratic (weightedForceMatrix m w01 w02 w12) w =
      w01 * (jacobiCoeffDot (jacobiPairCoeff01 m) w) ^ 2 +
      w02 * (jacobiCoeffDot (jacobiPairCoeff02 m) w) ^ 2 +
      w12 * (jacobiCoeffDot (jacobiPairCoeff12 m) w) ^ 2 := by
  simp [matrixQuadratic, weightedForceMatrix, jacobiCoeffDot, Fin.sum_univ_succ]
  ring

theorem weightedForceMatrix_quadratic_pos (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (w01 w02 w12 : ℝ) (h01 : 0 < w01) (h02 : 0 < w02) (h12 : 0 < w12)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    0 < matrixQuadratic (weightedForceMatrix m w01 w02 w12) w := by
  rw [weightedForceMatrix_quadratic]
  rcases exists_jacobiPairCoeff_dot_ne_zero m (hm 0) (hm 1) (hm 2) w hw with h | h
  · have hs := sq_pos_of_ne_zero h
    positivity
  · have hs := sq_pos_of_ne_zero h
    positivity

def forceMatrix (κ : Coefficients) (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    AbstractJacobi.Mat :=
  weightedForceMatrix m (weight κ q 0 1) (weight κ q 0 2) (weight κ q 1 2)

theorem forceMatrix_symmetric (κ : Coefficients) (m : Fin 3 → ℝ)
    (q : Fin 3 → Point) : (forceMatrix κ m q).transpose = forceMatrix κ m q :=
  weightedForceMatrix_symmetric _ _ _ _

theorem forceMatrix_quadratic_pos (κ : Coefficients) (hκ : κ.Positive)
    (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i) (q : Fin 3 → Point)
    (hcf : CollisionFree q) (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    0 < matrixQuadratic (forceMatrix κ m q) w := by
  apply weightedForceMatrix_quadratic_pos m hm
  · exact hκ 0 1 (by decide) _ (dist_pos.mpr (hcf 0 1 (by decide)))
  · exact hκ 0 2 (by decide) _ (dist_pos.mpr (hcf 0 2 (by decide)))
  · exact hκ 1 2 (by decide) _ (dist_pos.mpr (hcf 1 2 (by decide)))
  · exact hw

private theorem acceleration_recovery_pairSum (κ : Coefficients)
    (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i) (q : Fin 3 → Point) (r s : Fin 2) :
    (∑ i, m i * acceleration κ m q i r * jacobiBodyCoeff m i s) =
      weight κ q 0 1 * (q 1 - q 0) r *
        (jacobiBodyCoeff m 0 s - jacobiBodyCoeff m 1 s) +
      weight κ q 0 2 * (q 2 - q 0) r *
        (jacobiBodyCoeff m 0 s - jacobiBodyCoeff m 2 s) +
      weight κ q 1 2 * (q 2 - q 1) r *
        (jacobiBodyCoeff m 1 s - jacobiBodyCoeff m 2 s) := by
  simp_rw [mass_mul_acceleration_coord κ m q _ (hm _).ne']
  have h10 := weight_symmetric κ q 1 0
  have h20 := weight_symmetric κ q 2 0
  have h21 := weight_symmetric κ q 2 1
  simp [Fin.sum_univ_succ, h10, h20, h21]
  ring

/-- The exact configuration-level Jacobi equation for any symmetric pair law. -/
theorem jacobi_acceleration_eq (κ : Coefficients) (m : Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (q : Fin 3 → Point) :
    jacobiMatrix m (acceleration κ m q) = -(jacobiMatrix m q * forceMatrix κ m q) := by
  rw [← jacobiBodyRecoveryMatrix_eq_jacobiMatrix m (acceleration κ m q)
    (hm 0) (hm 1) (hm 2)]
  ext r s
  change (∑ i, m i * acceleration κ m q i r * jacobiBodyCoeff m i s) = _
  rw [acceleration_recovery_pairSum κ m hm]
  have h01 := jacobiPairContribution_entry (jacobiMatrix m q) (jacobiPairCoeff01 m)
    (weight κ q 0 1) r s (q 1 - q 0) (jacobiBodyCoeff m 0) (jacobiBodyCoeff m 1)
    (by
      have h := congrArg (fun p : Point => p r)
        (jacobiPairCoeff01_reconstructs m q (hm 0) (hm 1))
      simpa [jacobiCoeffDot, jacobiMatrix_col_zero, jacobiMatrix_col_one] using h.symm)
    (by
      have h := congrFun (jacobiPairCoeff01_eq_bodyDifference m (hm 0) (hm 1) (hm 2)) s
      rw [h]
      ring)
  have h02 := jacobiPairContribution_entry (jacobiMatrix m q) (jacobiPairCoeff02 m)
    (weight κ q 0 2) r s (q 2 - q 0) (jacobiBodyCoeff m 0) (jacobiBodyCoeff m 2)
    (by
      have h := congrArg (fun p : Point => p r)
        (jacobiPairCoeff02_reconstructs m q (hm 0) (hm 1) (hm 2))
      simpa [jacobiCoeffDot, jacobiMatrix_col_zero, jacobiMatrix_col_one] using h.symm)
    (by
      have h := congrFun (jacobiPairCoeff02_eq_bodyDifference m (hm 0) (hm 1) (hm 2)) s
      rw [h]
      ring)
  have h12 := jacobiPairContribution_entry (jacobiMatrix m q) (jacobiPairCoeff12 m)
    (weight κ q 1 2) r s (q 2 - q 1) (jacobiBodyCoeff m 1) (jacobiBodyCoeff m 2)
    (by
      have h := congrArg (fun p : Point => p r)
        (jacobiPairCoeff12_reconstructs m q (hm 0) (hm 1) (hm 2))
      simpa [jacobiCoeffDot, jacobiMatrix_col_zero, jacobiMatrix_col_one] using h.symm)
    (by
      have h := congrFun (jacobiPairCoeff12_eq_bodyDifference m (hm 0) (hm 1) (hm 2)) s
      rw [h]
      ring)
  rw [h01, h02, h12]
  simp [forceMatrix, weightedForceMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The general central-force phase equation supplies the abstract matrix system. -/
theorem jacobiSystem {κ : Coefficients} {m : Fin 3 → ℝ} {z : ℝ → Phase}
    {I : Set ℝ} (hsol : Solution κ m z I) (hm : ∀ i, 0 < m i) :
    AbstractJacobi.System (fun t => jacobiMatrix m (z t).1)
      (fun t => jacobiMatrix m (z t).2) (fun t => forceMatrix κ m (z t).1) I := by
  refine ⟨hsol.1, ?_, ?_⟩
  · intro t ht
    apply hasDerivAt_pi.2
    intro r
    apply hasDerivAt_pi.2
    intro c
    apply hasDerivAt_jacobiMatrixCurve_entry m (fun i s => (z s).1 i)
      (z t).2 t r c (hm 0) (hm 1) (hm 2)
    intro i k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (body_derivatives hsol ht i).1
  · intro t ht
    rw [← jacobi_acceleration_eq κ m hm (z t).1]
    apply hasDerivAt_pi.2
    intro r
    apply hasDerivAt_pi.2
    intro c
    apply hasDerivAt_jacobiMatrixCurve_entry m (fun i s => (z s).2 i)
      (acceleration κ m (z t).1) t r c (hm 0) (hm 1) (hm 2)
    intro i k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (body_derivatives hsol ht i).2

theorem jacobiSystem_positiveForce {κ : Coefficients} {m : Fin 3 → ℝ}
    {z : ℝ → Phase} {I : Set ℝ} (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) :
    AbstractJacobi.PositiveForce (fun t => forceMatrix κ m (z t).1) I := by
  intro t ht
  refine ⟨forceMatrix_symmetric κ m (z t).1, ?_⟩
  intro w hw
  exact forceMatrix_quadratic_pos κ hκ m hm (z t).1 (hsol.2 t ht).1 w hw

theorem jacobi_velocity_zero_of_rest (m : Fin 3 → ℝ) (z : ℝ → Phase) (a : ℝ)
    (hrest : ∀ i, (z a).2 i = 0) : jacobiMatrix m (z a).2 = 0 := by
  ext r c
  simp [jacobiMatrix, jacobiX, jacobiY, jacobiPairCenter, hrest]

/-- The abstract invertible branch is exactly the physical noncollinear branch,
for either orientation and without a center-of-mass normalization. -/
theorem initialBranch_eq (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (z : ℝ → Phase) (I : Set ℝ) (a : ℝ) :
    AbstractJacobi.initialBranch (fun t => jacobiMatrix m (z t).1) I a =
      BeforeFirstCollinearity z I a := by
  have hdet (t : ℝ) : (jacobiMatrix m (z t).1).det ≠ 0 ↔
      signedDoubleArea (z t).1 ≠ 0 := by
    rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z t).1 (hm 0) (hm 1)]
    simp [(sqrt_jacobiMu_pos m (hm 0) (hm 1)).ne',
      (sqrt_jacobiNu_pos m (hm 0) (hm 1) (hm 2)).ne']
  ext t
  simp only [AbstractJacobi.initialBranch, BeforeFirstCollinearity, Set.mem_setOf_eq, hdet]

end
end DroppingThreeBodies.CentralForce
