module

public import Dropping3Bodies.EqualMass.IsoscelesSymmetry
public import Dropping3Bodies.EqualMass.IsoscelesReduction
public import Dropping3Bodies.Dynamics.SolutionDerivatives
public import Mathlib.Tactic

@[expose] public section

/-!
# Scalar coordinates along a symmetric Newton trajectory

This module reconstructs a fixed configuration from the vertical reflection
symmetry and extracts the scalar position and velocity derivatives from the
classical Newton equation.
-/

namespace DroppingThreeBodies

noncomputable section

theorem isoscelesConfiguration_eq_of_symmetry_fixed
    (q : Fin 3 → Point)
    (hfix : isoscelesSymmetryConfiguration q = q) :
    q = isoscelesConfiguration (q 1 0) (q 0 1) (q 2 1) := by
  have h0 := congrArg (fun p : Point => p 0) (congrFun hfix 0)
  have h1 := congrArg (fun p : Point => p 1) (congrFun hfix 1)
  have h2 := congrArg (fun p : Point => p 0) (congrFun hfix 2)
  have hq0 : (q 0) 0 = -(q 1) 0 := by
    simpa [isoscelesSymmetryConfiguration, isoscelesIndexSwap,
      verticalReflectPoint, reflectPoint] using h0.symm
  have hq1 : (q 1) 1 = (q 0) 1 := by
    simpa [isoscelesSymmetryConfiguration, isoscelesIndexSwap,
      verticalReflectPoint, reflectPoint] using h1.symm
  have hq2 : (q 2) 0 = 0 := by
    have hneg : -(q 2) 0 = (q 2) 0 := by
      simpa [isoscelesSymmetryConfiguration, isoscelesIndexSwap,
        verticalReflectPoint, reflectPoint] using h2
    linarith
  funext i
  fin_cases i
  · ext k
    fin_cases k
    · simpa [isoscelesConfiguration, pointXY] using hq0
    · simp [isoscelesConfiguration, pointXY]
  · ext k
    fin_cases k
    · simp [isoscelesConfiguration, pointXY]
    · simpa [isoscelesConfiguration, pointXY] using hq1
  · ext k
    fin_cases k
    · simpa [isoscelesConfiguration, pointXY] using hq2
    · simp [isoscelesConfiguration, pointXY]

/-- Base-half acceleration also equals the horizontal acceleration of the
    right base body in an isosceles configuration. -/
theorem isoscelesBaseHalfAcceleration_eq_rightHorizontalAcceleration
    (x u v : ℝ) :
    isoscelesBaseHalfAcceleration x u v =
      (unitAcceleration (isoscelesConfiguration x u v) 1) 0 := by
  have hlegs := isoscelesConfiguration_legs_equidistant x u v
  have hbaseKernel : inverseCubeDistance (isoscelesConfiguration x u v) 1 0 =
      inverseCubeDistance (isoscelesConfiguration x u v) 0 1 := by
    simp [inverseCubeDistance, dist_comm]
  have hlegKernel : inverseCubeDistance (isoscelesConfiguration x u v) 1 2 =
      inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [inverseCubeDistance, hlegs]
  have hleft :
      (unitAcceleration (isoscelesConfiguration x u v) 0) 0 =
        2 * x * inverseCubeDistance (isoscelesConfiguration x u v) 0 1 +
          x * inverseCubeDistance (isoscelesConfiguration x u v) 0 2 := by
    simp [unitAcceleration, isoscelesConfiguration, pointXY]
    ring
  have hright :
      (unitAcceleration (isoscelesConfiguration x u v) 1) 0 =
        -2 * x * inverseCubeDistance (isoscelesConfiguration x u v) 1 0 -
          x * inverseCubeDistance (isoscelesConfiguration x u v) 1 2 := by
    simp [unitAcceleration, isoscelesConfiguration, pointXY]
    ring
  rw [isoscelesBaseHalfAcceleration, hleft, hright, hbaseKernel, hlegKernel]
  ring

def isoscelesSolutionX (z : ℝ → Phase) (t : ℝ) : ℝ := ((z t).1 1) 0
def isoscelesSolutionU (z : ℝ → Phase) (t : ℝ) : ℝ := ((z t).1 0) 1
def isoscelesSolutionV (z : ℝ → Phase) (t : ℝ) : ℝ := ((z t).1 2) 1
def isoscelesSolutionZ (z : ℝ → Phase) (t : ℝ) : ℝ :=
  isoscelesSolutionV z t - isoscelesSolutionU z t
def isoscelesSolutionXVelocity (z : ℝ → Phase) (t : ℝ) : ℝ := ((z t).2 1) 0
def isoscelesSolutionZVelocity (z : ℝ → Phase) (t : ℝ) : ℝ :=
  ((z t).2 2) 1 - ((z t).2 0) 1

theorem hasDerivAt_isoscelesSolutionX
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (isoscelesSolutionX z) (isoscelesSolutionXVelocity z t) t := by
  change HasDerivAt (fun s => ((z s).1 1) 0) (((z t).2 1) 0) t
  exact (classicalNewton_body_coordinate_derivatives 1 hsol ht).1 0

theorem hasDerivAt_isoscelesSolutionZ
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (isoscelesSolutionZ z) (isoscelesSolutionZVelocity z t) t := by
  have h2 := (classicalNewton_body_coordinate_derivatives 2 hsol ht).1 1
  have h0 := (classicalNewton_body_coordinate_derivatives 0 hsol ht).1 1
  have h := h2.sub h0
  change HasDerivAt (fun s => ((z s).1 2) 1 - ((z s).1 0) 1)
    (((z t).2 2) 1 - ((z t).2 0) 1) t
  exact h

theorem hasDerivAt_isoscelesSolutionXVelocity
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (isoscelesSolutionXVelocity z)
      ((unitAcceleration (z t).1 1) 0) t := by
  change HasDerivAt (fun s => ((z s).2 1) 0)
    ((unitAcceleration (z t).1 1) 0) t
  exact (classicalNewton_body_coordinate_derivatives 1 hsol ht).2 0

theorem hasDerivAt_isoscelesSolutionZVelocity
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (isoscelesSolutionZVelocity z)
      ((unitAcceleration (z t).1 2) 1 -
        (unitAcceleration (z t).1 0) 1) t := by
  have h2 := (classicalNewton_body_coordinate_derivatives 2 hsol ht).2 1
  have h0 := (classicalNewton_body_coordinate_derivatives 0 hsol ht).2 1
  have h := h2.sub h0
  change HasDerivAt (fun s => ((z s).2 2) 1 - ((z s).2 0) 1)
    ((unitAcceleration (z t).1 2) 1 - (unitAcceleration (z t).1 0) 1) t
  exact h

theorem classicalNewton_isosceles_scalar_accelerations
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (hSym : isoscelesSymmetryPhase (z t) = z t) :
    HasDerivAt (isoscelesSolutionXVelocity z)
      (isoscelesBaseHalfAcceleration
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t)) t ∧
    HasDerivAt (isoscelesSolutionZVelocity z)
      (isoscelesRelativeHeightAcceleration
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t)) t := by
  have hconfig : (z t).1 = isoscelesConfiguration
      (isoscelesSolutionX z t) (isoscelesSolutionU z t) (isoscelesSolutionV z t) :=
    isoscelesConfiguration_eq_of_symmetry_fixed (z t).1 (congrArg Prod.fst hSym)
  have hbase : (unitAcceleration (z t).1 1) 0 =
      isoscelesBaseHalfAcceleration
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t) := by
    rw [hconfig]
    exact (isoscelesBaseHalfAcceleration_eq_rightHorizontalAcceleration
      (isoscelesSolutionX z t) (isoscelesSolutionU z t)
      (isoscelesSolutionV z t)).symm
  have hheight : (unitAcceleration (z t).1 2) 1 -
      (unitAcceleration (z t).1 0) 1 =
      isoscelesRelativeHeightAcceleration
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t) := by
    rw [hconfig]
    rfl
  exact ⟨(hasDerivAt_isoscelesSolutionXVelocity hsol ht).congr_deriv hbase,
    (hasDerivAt_isoscelesSolutionZVelocity hsol ht).congr_deriv hheight⟩

end

end DroppingThreeBodies
