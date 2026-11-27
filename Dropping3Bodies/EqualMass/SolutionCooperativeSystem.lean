module

public import Dropping3Bodies.EqualMass.SolutionGapRatio
public import Dropping3Bodies.EqualMass.SolutionPairRotation

@[expose] public section

namespace DroppingThreeBodies

/-- The sign variable paired with the normalized side gap is minus the cyclic
    pair rotation. -/
noncomputable def sideGapRotationSignCurve
    (q v : Fin 3 → ℝ → Point) (i : Fin 3) (t : ℝ) : ℝ :=
  -sidePairRotationCurve q v i t

/-- At every centered, initially resting, collision-free solution time with
    nonzero signed area, the normalized squared-side gap and negative pair
    rotation satisfy the two Newton-specific cooperative equations. -/
theorem classicalNewton_sideGap_cooperative_derivatives
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I)
    (hrest : ∀ b, (z t₀).2 b = 0)
    (hcenter : (z t₀).1 0 + (z t₀).1 1 + (z t₀).1 2 = 0)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (sideGapRatioCurve (solutionPositionCurve z) i)
      ((3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) /
          (signedDoubleArea (z t).1) ^ 2) *
        sideGapRotationSignCurve (solutionPositionCurve z)
          (solutionVelocityCurve z) i t) t ∧
    HasDerivAt
      (sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i)
      ((signedDoubleArea (z t).1 ^ 2) *
        inverseCubeGapFactor
          (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
          (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) *
        sideGapRatioCurve (solutionPositionCurve z) i t) t := by
  have hX := classicalNewton_sideGapRatio_derivative i hsol hconn
    ht₀ ht hrest hcenter harea
  have hK := hasDerivAt_sidePairRotationCurve i hsol ht
  have hY := hK.neg
  have hratioVal : sideGapRatioCurve (solutionPositionCurve z) i t =
      sideGap (z t).1 i / signedDoubleArea (z t).1 := by
    simpa [solutionPositionCurve] using
      sideGapRatioCurve_eq_sideGap_div_signedDoubleArea
        (solutionPositionCurve z) i t
  constructor
  · apply hX.congr_deriv
    simp [sideGapRotationSignCurve, sidePairRotationCurve, sideVectorCurve,
      solutionPositionCurve, solutionVelocityCurve, framePairRotation]
    field_simp [harea]
  · apply hY.congr_deriv
    rw [hratioVal]
    field_simp [harea]


/-- At an initially resting, positively oriented configuration, the Y
    variable vanishes; a strictly positive initial squared-side gap makes X
    positive. -/
theorem sideGap_initial_cooperative_data
    (q : Fin 3 → Point) (i : Fin 3)
    (hgap : 0 < sideGap q i) (harea : 0 < signedDoubleArea q) :
    0 < sideGap q i / signedDoubleArea q := div_pos hgap harea

/-- Initial rest makes the negative pair-rotation variable zero. -/
theorem sideGapRotationSign_eq_zero_of_rest
    {z : ℝ → Phase} (i : Fin 3) (t : ℝ)
    (hrest : ∀ b, (z t).2 b = 0) :
    sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i t = 0 := by
  fin_cases i <;>
    simp [sideGapRotationSignCurve, sidePairRotationCurve,
      solutionPositionCurve, solutionVelocityCurve, sideVectorCurve,
      sideVector, hrest, cross]

/-- A nonzero frame area forces the equal-mass frame moment to be positive. -/
theorem frameMoment_pos_of_frameArea_ne_zero
    (r s : Point) (hB : frameArea r s ≠ 0) : 0 < frameMoment r s := by
  have hr : r ≠ 0 := by
    intro hr
    apply hB
    simp [frameArea, hr, cross]
  have hrnorm : 0 < ‖r‖ := norm_pos_iff.mpr hr
  unfold frameMoment
  positivity

/-- The two coefficients in the Newton cooperative system are strictly
    positive at every collision-free nonzero-area time. -/
theorem classicalNewton_sideGap_coefficients_pos
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3) {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    0 < 3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) /
        (signedDoubleArea (z t).1) ^ 2 ∧
    0 < (signedDoubleArea (z t).1) ^ 2 *
      inverseCubeGapFactor
        (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
        (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) := by
  have hBval : frameArea (sideVector (z t).1 i) (sideOffset (z t).1 i) =
      signedDoubleArea (z t).1 := by
    simpa [frameArea] using signedDoubleArea_eq_cross_sideFrame (z t).1 i
  have hB : frameArea (sideVector (z t).1 i) (sideOffset (z t).1 i) ≠ 0 := by
    rw [hBval]
    exact harea
  have hIpos := frameMoment_pos_of_frameArea_ne_zero
    (sideVector (z t).1 i) (sideOffset (z t).1 i) hB
  have hdist := (collisionFree_iff_dist_pos (z t).1).mp ((hsol.2 t ht).1)
  have hprev : cyclicPrev i ≠ i := by fin_cases i <;> decide
  have hnext : cyclicNext i ≠ i := by fin_cases i <;> decide
  have hfactor := inverseCubeGapFactor_pos
    (hdist (cyclicPrev i) i hprev) (hdist (cyclicNext i) i hnext)
  constructor <;> positivity

end DroppingThreeBodies

