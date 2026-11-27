module

public import Dropping3Bodies.EqualMass.SolutionSideFrame

@[expose] public section

namespace DroppingThreeBodies

/-- The cyclic squared-side gap normalized by the signed double area. -/
noncomputable def sideGapRatioCurve
    (q : Fin 3 → ℝ → Point) (i : Fin 3) (t : ℝ) : ℝ :=
  frameGapCurve (fun τ => sideVectorCurve q i τ)
      (fun τ => sideOffsetCurve q i τ) t /
    frameAreaCurve (fun τ => sideVectorCurve q i τ)
      (fun τ => sideOffsetCurve q i τ) t

/-- The normalized frame gap evaluates to the physical squared-side gap
    divided by the signed double area. -/
theorem sideGapRatioCurve_eq_sideGap_div_signedDoubleArea
    (q : Fin 3 → ℝ → Point) (i : Fin 3) (t : ℝ) :
    sideGapRatioCurve q i t = sideGap (fun b => q b t) i /
      signedDoubleArea (fun b => q b t) := by
  simp [sideGapRatioCurve, frameGapCurve, frameAreaCurve,
    sideVectorCurve, sideOffsetCurve, sideGap_eq_neg_two_dot_sideFrame,
    signedDoubleArea_eq_cross_sideFrame]

/-- A strictly positive geometric side gap and positive orientation give a
    positive initial cooperative X-variable. -/
theorem sideGapRatio_pos_of_sideGap_pos
    (q : Fin 3 → ℝ → Point) (i : Fin 3) (t : ℝ)
    (hgap : 0 < sideGap (fun b => q b t) i)
    (harea : 0 < signedDoubleArea (fun b => q b t)) :
    0 < sideGapRatioCurve q i t := by
  rw [sideGapRatioCurve_eq_sideGap_div_signedDoubleArea]
  exact div_pos hgap harea

/-- Along a centered, initially resting classical solution, the normalized
    side gap satisfies `X' = -3 I K / B²` at every nonzero-area time. -/
theorem classicalNewton_sideGapRatio_derivative
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I)
    (hrest : ∀ b, (z t₀).2 b = 0)
    (hcenter : (z t₀).1 0 + (z t₀).1 1 + (z t₀).1 2 = 0)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (sideGapRatioCurve (solutionPositionCurve z) i)
      ((-3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) *
          framePairRotation (sideVector (z t).1 i) (sideVector (z t).2 i)) /
        (signedDoubleArea (z t).1) ^ 2) t := by
  have hbody : HasBodyCoordDerivAt (solutionPositionCurve z)
      (fun b => (z t).2 b) t := by
    intro b k
    exact (classicalNewton_body_coordinate_derivatives b hsol ht).1 k
  have hside := hasCoordDerivAt_sideVectorCurve hbody i
  have hoffset := hasCoordDerivAt_sideOffsetCurve hbody i
  have hL := classicalNewton_sideFrame_angularMomentum_eq_zero
    hsol hconn ht₀ hrest hcenter ht i
  have hB : frameArea (sideVector (z t).1 i) (sideOffset (z t).1 i) ≠ 0 := by
    have hareaEq : frameArea (sideVector (z t).1 i) (sideOffset (z t).1 i) =
        signedDoubleArea (z t).1 := by
      simpa [frameArea] using signedDoubleArea_eq_cross_sideFrame (z t).1 i
    rw [hareaEq]
    exact harea
  have hratio := hasDerivAt_frameGapRatioCurve hside hoffset hL hB
  have hBcurve : frameArea (sideVectorCurve (solutionPositionCurve z) i t)
      (sideOffsetCurve (solutionPositionCurve z) i t) = signedDoubleArea (z t).1 := by
    simpa [frameArea, sideVectorCurve, sideOffsetCurve, solutionPositionCurve]
      using signedDoubleArea_eq_cross_sideFrame (z t).1 i
  rw [hBcurve] at hratio
  change HasDerivAt
    (fun τ => frameGapCurve
      (fun σ => sideVectorCurve (solutionPositionCurve z) i σ)
      (fun σ => sideOffsetCurve (solutionPositionCurve z) i σ) τ /
      frameAreaCurve
      (fun σ => sideVectorCurve (solutionPositionCurve z) i σ)
      (fun σ => sideOffsetCurve (solutionPositionCurve z) i σ) τ) _ t
  exact hratio

end DroppingThreeBodies

