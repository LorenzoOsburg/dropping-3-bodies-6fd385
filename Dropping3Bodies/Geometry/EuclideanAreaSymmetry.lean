module

public import Dropping3Bodies.Dynamics.OrthogonalSymmetry
public import Dropping3Bodies.Geometry.Coordinates
public import Dropping3Bodies.EqualMass.IsoscelesReduction
public import Mathlib.Tactic

@[expose] public section

/-! Euclidean and relabelling invariance of collision, distance, and area.-/

namespace DroppingThreeBodies

noncomputable section

/-- A linear isometry preserves vector norm. -/
theorem norm_orthogonalPoint (O : Point ≃ₗᵢ[ℝ] Point) (p : Point) :
    ‖O p‖ = ‖p‖ := O.norm_map p

/-- Euclidean isometries preserve every pairwise distance in a configuration. -/
theorem dist_orthogonalConfiguration
    (O : Point ≃ₗᵢ[ℝ] Point) (q : Fin 3 → Point) (i j : Fin 3) :
    dist (orthogonalConfiguration O q i) (orthogonalConfiguration O q j) =
      dist (q i) (q j) := by
  simp [orthogonalConfiguration, O.dist_map]

/-- Coordinate decomposition in the project convention for `Point`. -/
theorem point_eq_pointXY (p : Point) : p = pointXY (p 0) (p 1) := by
  ext i
  fin_cases i <;> simp [pointXY]

/-- A linear plane map multiplies every oriented cross product by its basis
determinant. -/
theorem cross_linearMap_eq_basisFactor (L : Point →ₗ[ℝ] Point)
    (u v : Point) :
    cross (L u) (L v) =
      cross (L (pointXY 1 0)) (L (pointXY 0 1)) * cross u v := by
  have hu : u = u 0 • pointXY 1 0 + u 1 • pointXY 0 1 := by
    ext i
    fin_cases i <;> simp [pointXY]
  have hv : v = v 0 • pointXY 1 0 + v 1 • pointXY 0 1 := by
    ext i
    fin_cases i <;> simp [pointXY]
  rw [hu, hv]
  simp only [L.map_add, L.map_smul]
  simp [cross]
  ring

/-- The basis determinant of a planar linear isometry is nonzero. -/
theorem cross_isometry_basis_ne_zero (O : Point ≃ₗᵢ[ℝ] Point) :
    cross (O (pointXY 1 0)) (O (pointXY 0 1)) ≠ 0 := by
  have hnorm0 : ‖O (pointXY 1 0)‖ ^ 2 = 1 := by
    rw [O.norm_map]
    simp [pointXY, EuclideanSpace.real_norm_sq_eq]
  have hnorm1 : ‖O (pointXY 0 1)‖ ^ 2 = 1 := by
    rw [O.norm_map]
    simp [pointXY, EuclideanSpace.real_norm_sq_eq]
  have hdot : dot2 (O (pointXY 1 0)) (O (pointXY 0 1)) = 0 := by
    have hinner : inner ℝ (O (pointXY 1 0)) (O (pointXY 0 1)) = 0 := by
      rw [O.inner_map_map]
      simp [pointXY, inner]
    have hd : dot2 (O (pointXY 1 0)) (O (pointXY 0 1)) =
        inner ℝ (O (pointXY 1 0)) (O (pointXY 0 1)) := by
      simp [dot2, inner]
      ring
    rw [hd, hinner]
  intro hc
  have hcross := cross_sq_add_dot2_sq
    (O (pointXY 1 0)) (O (pointXY 0 1))
  rw [hc, hdot] at hcross
  have hnorm0' : ‖O (pointXY 1 0)‖ ^ 2 = 1 := hnorm0
  have hnorm1' : ‖O (pointXY 0 1)‖ ^ 2 = 1 := hnorm1
  rw [hnorm0', hnorm1'] at hcross
  norm_num at hcross

/-- Signed double area transforms by the nonzero determinant of an orthogonal
map. Thus area zero is invariant, including orientation-reversing maps. -/
theorem signedDoubleArea_orthogonalConfiguration_eq_basisFactor
    (O : Point ≃ₗᵢ[ℝ] Point) (q : Fin 3 → Point) :
    signedDoubleArea (orthogonalConfiguration O q) =
      cross (O (pointXY 1 0)) (O (pointXY 0 1)) * signedDoubleArea q := by
  simp only [signedDoubleArea, orthogonalConfiguration]
  rw [← O.map_sub, ← O.map_sub]
  exact cross_linearMap_eq_basisFactor O.toLinearMap _ _

theorem signedDoubleArea_orthogonalConfiguration_eq_zero_iff
    (O : Point ≃ₗᵢ[ℝ] Point) (q : Fin 3 → Point) :
    signedDoubleArea (orthogonalConfiguration O q) = 0 ↔
      signedDoubleArea q = 0 := by
  rw [signedDoubleArea_orthogonalConfiguration_eq_basisFactor]
  constructor
  · intro h
    have hmul : cross (O (pointXY 1 0)) (O (pointXY 0 1)) *
        signedDoubleArea q = 0 := by simpa using h
    exact (mul_eq_zero.mp hmul).resolve_left (cross_isometry_basis_ne_zero O)
  · intro h
    simp [h]

/-- Permuting body labels preserves all pairwise distances. -/
theorem dist_permuteConfiguration
    (σ : Equiv.Perm (Fin 3)) (q : Fin 3 → Point) (i j : Fin 3) :
    dist (permuteConfiguration σ q i) (permuteConfiguration σ q j) =
      dist (q (σ i)) (q (σ j)) := rfl

/-- Signed double area under a body permutation changes at most by sign;
therefore collinearity is invariant under every relabelling. -/
theorem signedDoubleArea_permuteConfiguration_eq_zero_iff
    (σ : Equiv.Perm (Fin 3)) (q : Fin 3 → Point) :
    signedDoubleArea (permuteConfiguration σ q) = 0 ↔
      signedDoubleArea q = 0 := by
  classical
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  simp only [signedDoubleArea, permuteConfiguration]
  generalize σ 0 = i at h01 h02 ⊢
  generalize σ 1 = j at h01 h12 ⊢
  generalize σ 2 = k at h02 h12 ⊢
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [cross] <;>
    constructor <;> intro h <;> nlinarith

end

end DroppingThreeBodies
