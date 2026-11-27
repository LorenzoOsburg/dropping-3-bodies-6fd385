module

public import Dropping3Bodies.EqualMass.SolutionSideFrame

@[expose] public section

namespace DroppingThreeBodies

/-- Pair rotation of the cyclic side vector and its relative velocity. -/
noncomputable def sidePairRotationCurve
    (q v : Fin 3 → ℝ → Point) (i : Fin 3) (t : ℝ) : ℝ :=
  cross (sideVectorCurve q i t) (sideVectorCurve v i t)

/-- Along any classical collision-free Newton solution, the derivative of a
    cyclic pair rotation is minus the signed double area times the positive
    inverse-cube factor and the corresponding squared-side gap. -/
theorem hasDerivAt_sidePairRotationCurve
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3) {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt
      (sidePairRotationCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i)
      (-signedDoubleArea (z t).1 *
        inverseCubeGapFactor
          (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
          (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) *
        sideGap (z t).1 i) t := by
  have hbodyPos : HasBodyCoordDerivAt (solutionPositionCurve z)
      (fun b => (z t).2 b) t := by
    intro b k
    exact (classicalNewton_body_coordinate_derivatives b hsol ht).1 k
  have hbodyVel : HasBodyCoordDerivAt (solutionVelocityCurve z)
      (fun b => unitAcceleration (z t).1 b) t := by
    intro b k
    exact (classicalNewton_body_coordinate_derivatives b hsol ht).2 k
  have hsidePos := hasCoordDerivAt_sideVectorCurve hbodyPos i
  have hsideVel := hasCoordDerivAt_sideVectorCurve hbodyVel i
  have hrotation := hasDerivAt_frameAreaCurve hsidePos hsideVel
  have hself : cross (sideVector (fun b => (z t).2 b) i)
      (sideVector (fun b => (z t).2 b) i) = 0 := by
    fin_cases i <;> simp [sideVector, cross] <;> ring
  have haccSide : sideVector (fun b => unitAcceleration (z t).1 b) i =
      unitAcceleration (z t).1 (cyclicPrev i) -
        unitAcceleration (z t).1 (cyclicNext i) := by
    fin_cases i <;> rfl
  have hcf : CollisionFree (z t).1 := (hsol.2 t ht).1
  have hdist := (collisionFree_iff_dist_pos (z t).1).mp hcf
  have hprev : cyclicPrev i ≠ i := by fin_cases i <;> decide
  have hnext : cyclicNext i ≠ i := by fin_cases i <;> decide
  have htorque := unit_pair_torque_eq_neg_area_gap (z t).1 i
    (hdist (cyclicPrev i) i hprev) (hdist (cyclicNext i) i hnext)
  have hrate : frameAreaRate
      (sideVectorCurve (solutionPositionCurve z) i t)
      (sideVectorCurve (solutionVelocityCurve z) i t)
      (sideVector (fun b => (z t).2 b) i)
      (sideVector (fun b => unitAcceleration (z t).1 b) i) =
      -signedDoubleArea (z t).1 *
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
          (sideVector (fun b => unitAcceleration (z t).1 b) i) =
          0 + cross (sideVector (fun b => (z t).1 b) i)
            (sideVector (fun b => unitAcceleration (z t).1 b) i) := by
              rw [hself']
              simp [sideVectorCurve, solutionPositionCurve]
      _ = -signedDoubleArea (z t).1 *
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

end DroppingThreeBodies
