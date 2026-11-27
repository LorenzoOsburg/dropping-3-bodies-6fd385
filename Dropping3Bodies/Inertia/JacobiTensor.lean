module

public import Dropping3Bodies.Inertia.CenterOfMassMoment
public import NBody.Configuration.Masses
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-! The full spatial second-moment tensor in mass-normalized Jacobi coordinates.
These are static identities and impose no force law or rest hypothesis. -/

namespace DroppingThreeBodies

noncomputable section

theorem jacobiMatrix_mul_transpose_entry
    (m : Fin 3 → ℝ) (q : Fin 3 → Point) (hm : ∀ i, 0 < m i)
    (r s : Fin 2) :
    (jacobiMatrix m q * (jacobiMatrix m q).transpose) r s =
      jacobiMu m * (q 1 - q 0) r * (q 1 - q 0) s +
        jacobiNu m * (q 2 - jacobiPairCenter m q) r *
          (q 2 - jacobiPairCenter m q) s := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    jacobiMatrix, jacobiX, jacobiY]
  ring_nf
  rw [Real.sq_sqrt (jacobiMu_pos m (hm 0) (hm 1)).le,
    Real.sq_sqrt (jacobiNu_pos m (hm 0) (hm 1) (hm 2)).le]
  ring

/-- The spatial tensor equals `QQᵀ` without imposing a center-of-mass normalization. -/
theorem centeredSpatialMoment_eq_jacobiMatrix_mul_transpose
    (m : Fin 3 → ℝ) (q : Fin 3 → Point) (hm : ∀ i, 0 < m i) :
    centeredSpatialMoment m q = jacobiMatrix m q * (jacobiMatrix m q).transpose := by
  ext r s
  rw [jacobiMatrix_mul_transpose_entry m q hm]
  have hS : m 0 + m 1 ≠ 0 := ne_of_gt (add_pos (hm 0) (hm 1))
  have hM : m 0 + (m 1 + m 2) ≠ 0 :=
    ne_of_gt (add_pos (hm 0) (add_pos (hm 1) (hm 2)))
  simp [centeredSpatialMoment, NBody.centerOfMass, NBody.totalMass,
    NBody.weightedPosition, jacobiMu, jacobiNu, jacobiPairMass,
    jacobiPairCenter, totalMass, Fin.sum_univ_succ]
  field_simp [hS, hM]
  ring

theorem centeredSpatialMoment_trace_eq_centerOfMassMoment
    (m : Fin 3 → ℝ) (q : Fin 3 → Point) (hm : ∀ i, 0 < m i) :
    Matrix.trace (centeredSpatialMoment m q) = centerOfMassMoment m q := by
  rw [centeredSpatialMoment_eq_jacobiMatrix_mul_transpose m q hm,
    jacobiMatrix_trace_mul_transpose_eq_jacobiMoment,
    centerOfMassMoment_eq_jacobiMoment m q (hm 0) (hm 1) (hm 2)]

theorem centeredSpatialMoment_symmetric (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    (centeredSpatialMoment m q).transpose = centeredSpatialMoment m q := by
  ext r s
  simp only [Matrix.transpose_apply, centeredSpatialMoment]
  congr 1
  funext i
  ring

end
end DroppingThreeBodies
