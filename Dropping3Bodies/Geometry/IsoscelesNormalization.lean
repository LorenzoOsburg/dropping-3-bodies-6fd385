module

public import Dropping3Bodies.EqualMass.IsoscelesReduction
public import Dropping3Bodies.Dynamics.OrthogonalSymmetry
public import Dropping3Bodies.Geometry.Translation
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Tactic

@[expose] public section

/-! Static normalization of an arbitrary planar isosceles triangle. -/

namespace DroppingThreeBodies

noncomputable section

/-- The ordered three-point configuration with a designated base pair. -/
def orderedTriangle (p q r : Point) : Fin 3 → Point
  | 0 => p
  | 1 => q
  | _ => r

/-- Center a configuration at the midpoint of its first two points. -/
def centerAtBaseMidpoint (p q : Point) (r : Fin 3 → Point) : Fin 3 → Point :=
  fun i => r i - (1 / 2 : ℝ) • (p + q)

/-- If an isometry sends the directed base vector to the positive horizontal
    axis, an isosceles triangle becomes the canonical configuration after
    translating its base midpoint to the origin. -/
theorem isosceles_normalize_of_base_isometry
    (p q r : Point) (hne : p ≠ q) (hbase : dist p r = dist q r)
    (O : Point ≃ₗᵢ[ℝ] Point)
    (hO : O (q - p) = pointXY (dist p q) 0) :
    ∃ u v : ℝ,
      orthogonalConfiguration O (centerAtBaseMidpoint p q (orderedTriangle p q r)) =
        isoscelesConfiguration (dist p q / 2) u v := by
  let d := dist p q
  let x := d / 2
  let b := (1 / 2 : ℝ) • (p + q)
  let Q := orthogonalConfiguration O
    (centerAtBaseMidpoint p q (orderedTriangle p q r))
  let u := (Q 0) 1
  let v := (Q 2) 1
  have hd : 0 < d := dist_pos.mpr hne
  have hrelp : p - b = (-(1 / 2 : ℝ)) • (q - p) := by
    dsimp [b]
    module
  have hrelq : q - b = (1 / 2 : ℝ) • (q - p) := by
    dsimp [b]
    module
  have hpx : (Q 0) 0 = -x := by
    change (O (p - b)) 0 = -x
    rw [hrelp, O.map_smul, hO]
    simp [pointXY]
    dsimp [x, d]
    ring
  have hqx : (Q 1) 0 = x := by
    change (O (q - b)) 0 = x
    rw [hrelq, O.map_smul, hO]
    simp [pointXY]
    dsimp [x, d]
    ring
  have hbaseSub : Q 0 - Q 1 = -pointXY d 0 := by
    change O (p - b) - O (q - b) = -pointXY d 0
    rw [← O.map_sub]
    have hsub : (p - b) - (q - b) = -(q - p) := by abel
    rw [hsub]
    calc
      O (-(q - p)) = -(O (q - p)) := map_neg O (q - p)
      _ = -pointXY d 0 := by rw [hO]
  have hpy : (Q 0) 1 = (Q 1) 1 := by
    have h := congrArg (fun w : Point => w 1) hbaseSub
    simp [pointXY] at h
    linarith
  have hlegsQ : dist (Q 0) (Q 2) = dist (Q 1) (Q 2) := by
    have hp : dist (Q 0) (Q 2) = dist p r := by
      dsimp [Q, orthogonalConfiguration, centerAtBaseMidpoint,
        orderedTriangle]
      rw [O.dist_map]
      simpa [translatePoint, b, sub_eq_add_neg] using
        (translatePoint_dist (-b) p r)
    have hq : dist (Q 1) (Q 2) = dist q r := by
      dsimp [Q, orthogonalConfiguration, centerAtBaseMidpoint,
        orderedTriangle]
      rw [O.dist_map]
      simpa [translatePoint, b, sub_eq_add_neg] using
        (translatePoint_dist (-b) q r)
    rw [hp, hq]
    exact hbase
  have hzero : (Q 2) 0 = 0 := by
    have hsq := congrArg (fun y : ℝ => y ^ 2) hlegsQ
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at hsq
    simp [Fin.sum_univ_succ, Real.dist_eq, hpy] at hsq
    rw [hpx, hqx] at hsq
    have hxpos : 0 < x := by dsimp [x, d]; linarith
    nlinarith [sq_abs (-x - (Q 2) 0), sq_abs (x - (Q 2) 0)]
  refine ⟨u, v, ?_⟩
  funext i
  fin_cases i
  · ext k
    fin_cases k
    · simpa [isoscelesConfiguration, Q, u, x, d, centerAtBaseMidpoint,
        orderedTriangle] using hpx
    · simpa [isoscelesConfiguration, Q, u, centerAtBaseMidpoint,
        orderedTriangle] using hpy
  · ext k
    fin_cases k
    · simpa [isoscelesConfiguration, Q, u, x, d, centerAtBaseMidpoint,
        orderedTriangle] using hqx
    · simpa [isoscelesConfiguration, Q, u, centerAtBaseMidpoint,
        orderedTriangle] using hpy.symm
  · ext k
    fin_cases k
    · simpa [isoscelesConfiguration, Q, v, centerAtBaseMidpoint,
        orderedTriangle] using hzero
    · simp [isoscelesConfiguration, Q, v, centerAtBaseMidpoint,
        orderedTriangle]

/-- A nonzero directed base vector can be carried to the positive horizontal
    axis by a linear isometry. Mathlib's reflection-subspace construction
    supplies such an isometry directly. -/
theorem exists_base_axis_isometry (p q : Point) (hne : p ≠ q) :
    ∃ O : Point ≃ₗᵢ[ℝ] Point,
      O (q - p) = pointXY (dist p q) 0 := by
  let d := dist p q
  have hd : 0 < d := dist_pos.mpr hne
  have htarget : ‖pointXY d 0‖ = d := by
    have hsq : ‖pointXY d 0‖ ^ 2 = d ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [pointXY, Fin.sum_univ_succ]
    have hnonneg : 0 ≤ ‖pointXY d 0‖ := norm_nonneg _
    nlinarith
  have hnorm : ‖q - p‖ = ‖pointXY d 0‖ := by
    calc
      ‖q - p‖ = ‖p - q‖ := norm_sub_rev _ _
      _ = dist p q := (dist_eq_norm p q).symm
      _ = d := rfl
      _ = ‖pointXY d 0‖ := htarget.symm
  refine ⟨Submodule.reflection (ℝ ∙ ((q - p) - pointXY d 0))ᗮ, ?_⟩
  simpa [d] using (Submodule.reflection_sub hnorm)

/-- Every nondegenerate isosceles triangle admits an orthogonal and
    translational normalization to the canonical isosceles configuration. -/
theorem exists_isosceles_normalization
    (p q r : Point) (hne : p ≠ q) (hbase : dist p r = dist q r) :
    ∃ O : Point ≃ₗᵢ[ℝ] Point, ∃ u v : ℝ,
      orthogonalConfiguration O (centerAtBaseMidpoint p q (orderedTriangle p q r)) =
        isoscelesConfiguration (dist p q / 2) u v := by
  obtain ⟨O, hO⟩ := exists_base_axis_isometry p q hne
  obtain ⟨u, v, hnorm⟩ :=
    isosceles_normalize_of_base_isometry p q r hne hbase O hO
  exact ⟨O, u, v, hnorm⟩

/-- The half-base parameter in the canonical normal form is strictly
    positive for every nondegenerate base pair. -/
theorem exists_isosceles_normalization_with_positive_halfBase
    (p q r : Point) (hne : p ≠ q) (hbase : dist p r = dist q r) :
    ∃ O : Point ≃ₗᵢ[ℝ] Point, ∃ u v : ℝ,
      0 < dist p q / 2 ∧
      orthogonalConfiguration O (centerAtBaseMidpoint p q (orderedTriangle p q r)) =
        isoscelesConfiguration (dist p q / 2) u v := by
  obtain ⟨O, u, v, hnorm⟩ :=
    exists_isosceles_normalization p q r hne hbase
  refine ⟨O, u, v, ?_, hnorm⟩
  exact div_pos (dist_pos.mpr hne) (by norm_num)

/-- The normalization adapter also applies after any chosen body
    permutation, so the base and apex may have arbitrary original indices. -/
theorem exists_isosceles_normalization_after_permutation
    (q : Fin 3 → Point) (σ : Equiv.Perm (Fin 3))
    (hne : q (σ 0) ≠ q (σ 1))
    (hbase : dist (q (σ 0)) (q (σ 2)) =
      dist (q (σ 1)) (q (σ 2))) :
    ∃ O : Point ≃ₗᵢ[ℝ] Point, ∃ u v : ℝ,
      orthogonalConfiguration O
          (centerAtBaseMidpoint (q (σ 0)) (q (σ 1))
            (orderedTriangle (q (σ 0)) (q (σ 1)) (q (σ 2)))) =
        isoscelesConfiguration
          (dist (q (σ 0)) (q (σ 1)) / 2) u v := by
  exact exists_isosceles_normalization
    (q (σ 0)) (q (σ 1)) (q (σ 2)) hne hbase

end

end DroppingThreeBodies
