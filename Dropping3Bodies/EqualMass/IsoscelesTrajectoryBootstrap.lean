module

public import Dropping3Bodies.EqualMass.IsoscelesBootstrap
public import Dropping3Bodies.EqualMass.IsoscelesRatioGeometry
public import Dropping3Bodies.EqualMass.IsoscelesTrajectoryODE
public import Dropping3Bodies.EqualMass.IsoscelesInitialSymmetry
public import Dropping3Bodies.Dynamics.ReflectionSymmetry
public import Mathlib.Tactic

@[expose] public section

/-!
# Bootstrap along symmetric equal-mass Newton trajectories

This module combines the abstract compact-interval first-violation lemma with
the scalar ODE and geometric force threshold on a regular symmetric trajectory.
-/

namespace DroppingThreeBodies

noncomputable section

/-- For a symmetric classical Newton trajectory on a regular interval, the
    positive ratio branch above `sqrt 3` is invariant on any compact forward
    segment where the base half-length stays positive. -/
theorem classicalNewton_isosceles_ratio_stays_above_sqrt_three
    {z : ℝ → Phase} {I : Set ℝ} {a b : ℝ}
    (hsol : ClassicalNewtonSolution z I)
    (hsegment : Set.Icc a b ⊆ I)
    (hSym : ∀ t ∈ Set.Icc a b, isoscelesSymmetryPhase (z t) = z t)
    (hx : ∀ t ∈ Set.Icc a b, 0 < isoscelesSolutionX z t)
    (hW0 : scalarWronskianCurve (isoscelesSolutionX z)
      (isoscelesSolutionXVelocity z) (isoscelesSolutionZ z)
      (isoscelesSolutionZVelocity z) a = 0)
    (hratio0 : Real.sqrt 3 < scalarRatioCurve
      (isoscelesSolutionX z) (isoscelesSolutionZ z) a) :
    ∀ t ∈ Set.Icc a b, Real.sqrt 3 < scalarRatioCurve
      (isoscelesSolutionX z) (isoscelesSolutionZ z) t := by
  apply ratio_stays_above_of_wronskian_bootstrap
    (x := isoscelesSolutionX z)
    (W := fun t => scalarWronskianCurve (isoscelesSolutionX z)
      (isoscelesSolutionXVelocity z) (isoscelesSolutionZ z)
      (isoscelesSolutionZVelocity z) t)
    (ratio := scalarRatioCurve (isoscelesSolutionX z) (isoscelesSolutionZ z))
    (Wdot := fun t => isoscelesWronskianForce
      (isoscelesSolutionX z t) (isoscelesSolutionU z t)
      (isoscelesSolutionV z t)) hx hW0 hratio0
  · intro t ht
    exact (classicalNewton_isosceles_wrOnskian_and_ratio_derivatives hsol
      (hsegment ht) (hSym t ht) (hx t ht)).1
  · intro t ht
    exact (classicalNewton_isosceles_wrOnskian_and_ratio_derivatives hsol
      (hsegment ht) (hSym t ht) (hx t ht)).2
  · intro t ht hratio
    have hratio' : Real.sqrt 3 <
        (isoscelesSolutionV z t - isoscelesSolutionU z t) /
          isoscelesSolutionX z t := by
      simpa [scalarRatioCurve, isoscelesSolutionZ] using hratio
    exact isoscelesWronskianForce_pos_of_ratio_gt_sqrt_three
      (isoscelesSolutionX z t) (isoscelesSolutionU z t)
      (isoscelesSolutionV z t) (hx t ht) hratio'

/-- For a symmetric rest start with positive initial ratio above `sqrt 3`,
    uniqueness propagates the reflection symmetry and the geometric threshold
    bootstrap excludes the syzygy threshold on every regular segment with
    positive base half-length. -/
theorem classicalNewton_isosceles_rest_ratio_stays_above_sqrt_three
    {z : ℝ → Phase} {I : Set ℝ} {a b x₀ u₀ v₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    (ha : a ∈ I)
    (hstart : z a =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)))
    (hsegment : Set.Icc a b ⊆ I)
    (hratio₀ : Real.sqrt 3 < (v₀ - u₀) / x₀)
    (hx : ∀ t ∈ Set.Icc a b, 0 < isoscelesSolutionX z t) :
    ∀ t ∈ Set.Icc a b, Real.sqrt 3 < scalarRatioCurve
      (isoscelesSolutionX z) (isoscelesSolutionZ z) t := by
  have hfixed : isoscelesSymmetryPhase (z a) = z a := by
    rw [hstart]
    exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
  have hSym : ∀ t ∈ Set.Icc a b, isoscelesSymmetryPhase (z t) = z t := by
    intro t ht
    exact classicalNewtonSolution_isoscelesSymmetric hsol hconn ha hfixed t
      (hsegment ht)
  have hxdot : isoscelesSolutionXVelocity z a = 0 := by
    simp [isoscelesSolutionXVelocity, hstart]
  have hzdot : isoscelesSolutionZVelocity z a = 0 := by
    simp [isoscelesSolutionZVelocity, hstart]
  have hW0 : scalarWronskianCurve (isoscelesSolutionX z)
      (isoscelesSolutionXVelocity z) (isoscelesSolutionZ z)
      (isoscelesSolutionZVelocity z) a = 0 := by
    simp [scalarWronskianCurve, hxdot, hzdot]
  have hratio0 : Real.sqrt 3 < scalarRatioCurve
      (isoscelesSolutionX z) (isoscelesSolutionZ z) a := by
    simpa [scalarRatioCurve, isoscelesSolutionX, isoscelesSolutionZ,
      isoscelesSolutionU, isoscelesSolutionV, hstart, isoscelesConfiguration,
      pointXY] using hratio₀
  exact classicalNewton_isosceles_ratio_stays_above_sqrt_three
    hsol hsegment hSym hx hW0 hratio0
/-- Vanishing scalar velocities at the initial time imply zero Wronskian. -/
theorem isoscelesWronskian_eq_zero_of_initial_rest
    (z : ℝ → Phase) (a : ℝ)
    (hxdot : isoscelesSolutionXVelocity z a = 0)
    (hzdot : isoscelesSolutionZVelocity z a = 0) :
    scalarWronskianCurve (isoscelesSolutionX z)
      (isoscelesSolutionXVelocity z) (isoscelesSolutionZ z)
      (isoscelesSolutionZVelocity z) a = 0 := by
  simp [scalarWronskianCurve, hxdot, hzdot]

/-- The negative ratio branch follows by reflecting the trajectory across the
    horizontal axis. -/
theorem classicalNewton_isosceles_rest_ratio_stays_below_neg_sqrt_three
    {z : ℝ → Phase} {I : Set ℝ} {a b x₀ u₀ v₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    (ha : a ∈ I)
    (hstart : z a =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)))
    (hsegment : Set.Icc a b ⊆ I)
    (hratio₀ : (v₀ - u₀) / x₀ < -Real.sqrt 3)
    (hx : ∀ t ∈ Set.Icc a b, 0 < isoscelesSolutionX z t) :
    ∀ t ∈ Set.Icc a b, scalarRatioCurve
      (isoscelesSolutionX z) (isoscelesSolutionZ z) t < -Real.sqrt 3 := by
  let zR : ℝ → Phase := fun t => reflectPhase (z t)
  have hsolR : ClassicalNewtonSolution zR I := by
    simpa [zR] using classicalNewtonSolution_reflect hsol
  have hstartR : zR a =
      (isoscelesConfiguration x₀ (-u₀) (-v₀),
        fun _ : Fin 3 => (0 : Point)) := by
    change reflectPhase (z a) = _
    rw [hstart]
    apply Prod.ext
    · funext i
      fin_cases i <;>
        ext k <;> fin_cases k <;>
          simp [reflectPhase, reflectConfiguration, reflectPoint,
            isoscelesConfiguration, pointXY]
    · funext i
      ext k
      simp [reflectPhase, reflectConfiguration, reflectPoint]
  have hratioR : Real.sqrt 3 < ((-v₀) - (-u₀)) / x₀ := by
    have hneg : Real.sqrt 3 < -((v₀ - u₀) / x₀) := by linarith
    convert hneg using 1; ring
  have hxR : ∀ t ∈ Set.Icc a b, 0 < isoscelesSolutionX zR t := by
    intro t ht
    simpa [zR, isoscelesSolutionX, reflectPhase, reflectConfiguration,
      reflectPoint] using hx t ht
  have hpositive := classicalNewton_isosceles_rest_ratio_stays_above_sqrt_three
    hsolR hconn ha hstartR hsegment hratioR hxR
  intro t ht
  have hratioReflect : scalarRatioCurve (isoscelesSolutionX zR)
      (isoscelesSolutionZ zR) t = -scalarRatioCurve
        (isoscelesSolutionX z) (isoscelesSolutionZ z) t := by
    simp [scalarRatioCurve, zR, isoscelesSolutionX, isoscelesSolutionZ,
      isoscelesSolutionU, isoscelesSolutionV, reflectPhase,
      reflectConfiguration, reflectPoint]
    ring
  have hp := hpositive t ht
  rw [hratioReflect] at hp
  linarith
end

end DroppingThreeBodies
