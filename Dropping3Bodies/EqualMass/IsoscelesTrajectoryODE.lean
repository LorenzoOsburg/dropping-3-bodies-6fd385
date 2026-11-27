module

public import Dropping3Bodies.EqualMass.IsoscelesTrajectoryReduction
public import Dropping3Bodies.EqualMass.IsoscelesCurveCalculus
public import Dropping3Bodies.EqualMass.IsoscelesWronskianGeometry
public import Mathlib.Tactic

@[expose] public section

namespace DroppingThreeBodies

noncomputable section

theorem classicalNewton_isosceles_scalar_ode
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (hSym : isoscelesSymmetryPhase (z t) = z t)
    (hx : 0 < isoscelesSolutionX z t) :
    HasDerivAt (isoscelesSolutionXVelocity z)
      (-(1 / (4 * (isoscelesSolutionX z t) ^ 2) +
        isoscelesSolutionX z t * inverseCubeDistance
          (isoscelesConfiguration (isoscelesSolutionX z t)
            (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2)) t ∧
    HasDerivAt (isoscelesSolutionZVelocity z)
      (-3 * isoscelesSolutionZ z t * inverseCubeDistance
        (isoscelesConfiguration (isoscelesSolutionX z t)
          (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2) t := by
  have hacc := classicalNewton_isosceles_scalar_accelerations hsol ht hSym
  constructor
  · exact hacc.1.congr_deriv
      (isoscelesBaseHalfAcceleration_eq
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t) hx)
  · simpa [isoscelesSolutionZ] using hacc.2.congr_deriv
      (isoscelesRelativeHeightAcceleration_eq
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t))

/-- The generic Wronskian and ratio derivative rules apply to the actual
    scalar coordinates of any symmetric classical Newton solution. -/
theorem classicalNewton_isosceles_wrOnskian_and_ratio_derivatives
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (hSym : isoscelesSymmetryPhase (z t) = z t)
    (hx : 0 < isoscelesSolutionX z t) :
    HasDerivAt
      (fun s => scalarWronskianCurve (isoscelesSolutionX z)
        (isoscelesSolutionXVelocity z) (isoscelesSolutionZ z)
        (isoscelesSolutionZVelocity z) s)
      (isoscelesWronskianForce (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t)) t ∧
    HasDerivAt
      (scalarRatioCurve (isoscelesSolutionX z) (isoscelesSolutionZ z))
      (scalarWronskianCurve (isoscelesSolutionX z)
        (isoscelesSolutionXVelocity z) (isoscelesSolutionZ z)
        (isoscelesSolutionZVelocity z) t / (isoscelesSolutionX z t) ^ 2) t := by
  have hacc := classicalNewton_isosceles_scalar_accelerations hsol ht hSym
  let xddot : ℝ → ℝ := fun _ => isoscelesBaseHalfAcceleration
    (isoscelesSolutionX z t) (isoscelesSolutionU z t) (isoscelesSolutionV z t)
  let zddot : ℝ → ℝ := fun _ => isoscelesRelativeHeightAcceleration
    (isoscelesSolutionX z t) (isoscelesSolutionU z t) (isoscelesSolutionV z t)
  have hwr := hasDerivAt_scalarWronskianCurve
    (isoscelesSolutionX z) (isoscelesSolutionXVelocity z) xddot
    (isoscelesSolutionZ z) (isoscelesSolutionZVelocity z) zddot t
    (hasDerivAt_isoscelesSolutionX hsol ht)
    (by simpa [xddot] using hacc.1)
    (hasDerivAt_isoscelesSolutionZ hsol ht)
    (by simpa [zddot] using hacc.2)
  have hwr' : HasDerivAt
      (fun s => scalarWronskianCurve (isoscelesSolutionX z)
        (isoscelesSolutionXVelocity z) (isoscelesSolutionZ z)
        (isoscelesSolutionZVelocity z) s)
      (isoscelesWronskianForce (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t)) t := by
    exact hwr.congr_deriv (by
      simp [isoscelesWronskianForce, isoscelesSolutionZ]
      ring)
  exact ⟨hwr', hasDerivAt_scalarRatioCurve
    (isoscelesSolutionX z) (isoscelesSolutionXVelocity z)
    (isoscelesSolutionZ z) (isoscelesSolutionZVelocity z) t
    (hasDerivAt_isoscelesSolutionX hsol ht)
    (hasDerivAt_isoscelesSolutionZ hsol ht)
    (ne_of_gt hx)⟩

end

end DroppingThreeBodies
