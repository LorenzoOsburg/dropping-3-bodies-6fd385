module

public import Dropping3Bodies.Dynamics.GeneralEnergy
public import Dropping3Bodies.Dynamics.ReflectionSymmetry
public import Dropping3Bodies.Geometry.Reflection
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# Reflection symmetry for arbitrary-mass Newton solutions

This is the orientation-reversal bridge needed to state the general-mass
moment monotonicity theorem without choosing an orientation convention.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Reflect both position and velocity in a general Newton phase point. -/
def reflectGeneralPhase (z : Phase) : Phase :=
  (reflectConfiguration z.1, reflectConfiguration z.2)

theorem inverseCubeDistance_reflectConfiguration_general
    (q : Fin 3 → Point) (i j : Fin 3) :
    inverseCubeDistance (reflectConfiguration q) i j = inverseCubeDistance q i j := by
  simp [inverseCubeDistance, dist_reflectConfiguration]

theorem generalAcceleration_reflectConfiguration
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) (i : Fin 3) :
    reflectPoint (generalAcceleration G m q i) =
      generalAcceleration G m (reflectConfiguration q) i := by
  fin_cases i <;>
    simp [generalAcceleration, Fin.sum_univ_succ,
      inverseCubeDistance_reflectConfiguration_general,
      reflectConfiguration, reflectPoint_add, reflectPoint_smul, reflectPoint_sub]

theorem generalNewtonField_reflectGeneralPhase (G : ℝ) (m : Fin 3 → ℝ)
    (z : Phase) :
    generalNewtonField G m (reflectGeneralPhase z) =
      reflectGeneralPhase (generalNewtonField G m z) := by
  cases z with
  | mk q v =>
      apply Prod.ext
      · rfl
      · funext i
        exact (generalAcceleration_reflectConfiguration G m q i).symm

/-- A reflected general-mass collision-free classical solution is again a
    solution on the same interval. -/
theorem generalClassicalNewtonSolution_reflect
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) :
    GeneralClassicalNewtonSolution G m (fun t => reflectGeneralPhase (z t)) I := by
  refine ⟨hsol.1, fun t ht => ?_⟩
  have hregular := hsol.2 t ht
  constructor
  · intro i j hij
    apply dist_pos.mp
    change 0 < dist (reflectPoint ((z t).1 i)) (reflectPoint ((z t).1 j))
    rw [reflectPoint_dist]
    exact dist_pos.mpr (hregular.1 i j hij)
  · have hderiv :=
      (HasFDerivAt.comp t reflectPhaseCLM.hasFDerivAt
        hregular.2.hasFDerivAt).hasDerivAt
    have hderiv' : HasDerivAt (fun s => reflectGeneralPhase (z s))
        (reflectGeneralPhase (generalNewtonField G m (z t))) t := by
      simpa [reflectGeneralPhase, reflectPhase, reflectPhaseCLM, reflectPhaseLinear,
        Function.comp_def] using hderiv
    rw [← generalNewtonField_reflectGeneralPhase G m (z t)] at hderiv'
    exact hderiv'

end

end DroppingThreeBodies
