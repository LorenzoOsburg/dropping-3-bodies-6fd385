module

public import Dropping3Bodies.Dynamics.GeneralEnergy
public import Dropping3Bodies.EqualMass.SolutionGapRatio
public import Dropping3Bodies.EqualMass.SolutionPairRotation

@[expose] public section

/-! Pair-rotation derivatives for arbitrary masses and gravitational constant. -/

namespace DroppingThreeBodies

noncomputable section

/-- The equal-unit-mass side-frame angular momentum is one third of the sum
    of the three unweighted pair rotations, for every position and velocity
    configuration. -/
theorem frameAngularMomentum_eq_sum_sidePairRotations_div_three
    (q v : Fin 3 → Point) (i : Fin 3) :
    frameAngularMomentum (sideVector q i) (sideOffset q i)
        (sideVector v i) (sideOffset v i) =
      (∑ j : Fin 3, framePairRotation (sideVector q j) (sideVector v j)) / 3 := by
  fin_cases i <;>
    simp [frameAngularMomentum, framePairRotation, sideVector, sideOffset,
      cross, Fin.sum_univ_succ] <;>
    ring

/-- The total-mass angular momentum identity expressed as a weighted sum of
    the three pair rotations. This exposes the unequal-mass constraint on
    those rotations. -/
theorem generalWeightedAngularMomentum_eq_pairRotationSum
    (m : Fin 3 → ℝ) (q v : Fin 3 → Point) :
    totalMass m * (∑ i : Fin 3, m i * cross (q i) (v i)) -
        cross (weightedPosition m q) (weightedPosition m v) =
      ∑ i : Fin 3, m (cyclicPrev i) * m (cyclicNext i) *
        framePairRotation (sideVector q i) (sideVector v i) := by
  simp [totalMass, weightedPosition, framePairRotation, sideVector,
    cyclicPrev, cyclicNext, cross, Fin.sum_univ_succ]
  ring

/-- For arbitrary positive or signed parameters, the cyclic pair-rotation
    derivative is the opposite-side gap times the source mass and `G`. The
    sign conclusion therefore requires `G*m i>0`, but the identity itself
    only requires collision freedom. -/
theorem hasDerivAt_generalSidePairRotationCurve
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (i : Fin 3) {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I) :
    HasDerivAt
      (sidePairRotationCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i)
      (-(G * m i) * signedDoubleArea (z t).1 *
        inverseCubeGapFactor
          (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
          (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) *
        sideGap (z t).1 i) t := by
  have hbodyPos : HasBodyCoordDerivAt (solutionPositionCurve z)
      (fun b => (z t).2 b) t := by
    intro b k
    simpa [solutionPositionCurve, EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (generalNewton_body_vector_derivatives b hsol ht).1
  have hbodyVel : HasBodyCoordDerivAt (solutionVelocityCurve z)
      (fun b => generalAcceleration G m (z t).1 b) t := by
    intro b k
    simpa [solutionVelocityCurve, EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (generalNewton_body_vector_derivatives b hsol ht).2
  have hsidePos := hasCoordDerivAt_sideVectorCurve hbodyPos i
  have hsideVel := hasCoordDerivAt_sideVectorCurve hbodyVel i
  have hrotation := hasDerivAt_frameAreaCurve hsidePos hsideVel
  have hself : cross (sideVector (fun b => (z t).2 b) i)
      (sideVector (fun b => (z t).2 b) i) = 0 := by
    fin_cases i <;> simp [sideVector, cross] <;> ring
  have haccSide : sideVector (fun b => generalAcceleration G m (z t).1 b) i =
      generalAcceleration G m (z t).1 (cyclicPrev i) -
        generalAcceleration G m (z t).1 (cyclicNext i) := by
    fin_cases i <;> rfl
  have hcf : CollisionFree (z t).1 := (hsol.2 t ht).1
  have hdist := (collisionFree_iff_dist_pos (z t).1).mp hcf
  have hprev : cyclicPrev i ≠ i := by fin_cases i <;> decide
  have hnext : cyclicNext i ≠ i := by fin_cases i <;> decide
  have htorque := general_pair_torque_eq_neg_area_gap G m (z t).1 i
    (hdist (cyclicPrev i) i hprev) (hdist (cyclicNext i) i hnext)
  have hrate : frameAreaRate
      (sideVectorCurve (solutionPositionCurve z) i t)
      (sideVectorCurve (solutionVelocityCurve z) i t)
      (sideVector (fun b => (z t).2 b) i)
      (sideVector (fun b => generalAcceleration G m (z t).1 b) i) =
      -(G * m i) * signedDoubleArea (z t).1 *
        inverseCubeGapFactor
          (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
          (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) *
        sideGap (z t).1 i := by
    rw [frameAreaRate]
    have hself' : cross (sideVector (fun b => (z t).2 b) i)
        (sideVectorCurve (solutionVelocityCurve z) i t) = 0 := by
      change cross (sideVector (fun b => (z t).2 b) i)
        (sideVector (fun b => (z t).2 b) i) = 0
      exact hself
    calc
      cross (sideVector (fun b => (z t).2 b) i)
          (sideVectorCurve (solutionVelocityCurve z) i t) +
        cross (sideVectorCurve (solutionPositionCurve z) i t)
          (sideVector (fun b => generalAcceleration G m (z t).1 b) i) =
          0 + cross (sideVector (fun b => (z t).1 b) i)
            (sideVector (fun b => generalAcceleration G m (z t).1 b) i) := by
              rw [hself']
              simp [sideVectorCurve, solutionPositionCurve]
      _ = -(G * m i) * signedDoubleArea (z t).1 *
          inverseCubeGapFactor
            (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
            (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) *
          sideGap (z t).1 i := by
            simpa [haccSide] using htorque
  have hfinal := hrotation.congr_deriv hrate
  change HasDerivAt
    (frameAreaCurve (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
      (fun τ => sideVectorCurve (solutionVelocityCurve z) i τ)) _ t
  exact hfinal

/-- The normalized squared-side gap along a general-mass Newton solution has
    the usual pair-rotation term plus the exact frame-angular-momentum
    correction. This identifies the extra sign issue in the unequal-mass
    cooperative argument. -/
theorem generalNewton_sideGapRatioCurve_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (i : Fin 3) {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (sideGapRatioCurve (solutionPositionCurve z) i)
      ((-3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) *
          framePairRotation (sideVector (z t).1 i) (sideVector (z t).2 i) +
        3 * ‖sideVector (z t).1 i‖ ^ 2 *
          frameAngularMomentum (sideVector (z t).1 i) (sideOffset (z t).1 i)
            (sideVector (z t).2 i) (sideOffset (z t).2 i)) /
        (signedDoubleArea (z t).1) ^ 2) t := by
  have hbody : HasBodyCoordDerivAt (solutionPositionCurve z)
      (fun b => (z t).2 b) t := by
    intro b k
    simpa [solutionPositionCurve, EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (generalNewton_body_vector_derivatives b hsol ht).1
  have hside := hasCoordDerivAt_sideVectorCurve hbody i
  have hoffset := hasCoordDerivAt_sideOffsetCurve hbody i
  have hB : frameArea (sideVector (z t).1 i) (sideOffset (z t).1 i) ≠ 0 := by
    have hareaEq : frameArea (sideVector (z t).1 i) (sideOffset (z t).1 i) =
        signedDoubleArea (z t).1 := by
      simpa [frameArea] using signedDoubleArea_eq_cross_sideFrame (z t).1 i
    rw [hareaEq]
    exact harea
  have hratio := hasDerivAt_frameGapRatioCurve_general hside hoffset hB
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

end

end DroppingThreeBodies
