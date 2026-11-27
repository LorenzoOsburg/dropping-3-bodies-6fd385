module

public import Dropping3Bodies.Dynamics.Newton
public import Dropping3Bodies.Geometry.Reflection
public import Mathlib.Tactic

@[expose] public section

/-!
# Reflection symmetry of the equal-mass Newton vector field
-/

namespace DroppingThreeBodies

noncomputable section

def reflectPhase (z : Phase) : Phase :=
  (reflectConfiguration z.1, reflectConfiguration z.2)

def reflectPhaseLinear : Phase →ₗ[ℝ] Phase where
  toFun := reflectPhase
  map_add' z w := by
    rcases z with ⟨q, v⟩
    rcases w with ⟨q', v'⟩
    apply Prod.ext
    · funext i
      exact reflectPoint_add (q i) (q' i)
    · funext i
      exact reflectPoint_add (v i) (v' i)
  map_smul' c z := by
    rcases z with ⟨q, v⟩
    apply Prod.ext
    · funext i
      exact reflectPoint_smul c (q i)
    · funext i
      exact reflectPoint_smul c (v i)

noncomputable def reflectPhaseCLM : Phase →L[ℝ] Phase :=
  reflectPhaseLinear.toContinuousLinearMap

theorem inverseCubeDistance_reflectConfiguration
    (q : Fin 3 → Point) (i j : Fin 3) :
    inverseCubeDistance (reflectConfiguration q) i j = inverseCubeDistance q i j := by
  simp [inverseCubeDistance, dist_reflectConfiguration]

theorem unitAcceleration_reflectConfiguration
    (q : Fin 3 → Point) (i : Fin 3) :
    reflectPoint (unitAcceleration q i) =
      unitAcceleration (reflectConfiguration q) i := by
  fin_cases i <;>
    simp [unitAcceleration, reflectConfiguration, reflectPoint_add,
      reflectPoint_smul, reflectPoint_sub, inverseCubeDistance]

theorem unitNewtonField_reflectPhase (z : Phase) :
    unitNewtonField (reflectPhase z) = reflectPhase (unitNewtonField z) := by
  cases z with
  | mk q v =>
      apply Prod.ext
      · rfl
      · funext i
        simpa [reflectPhase, unitNewtonField, reflectConfiguration] using
          (unitAcceleration_reflectConfiguration q i).symm

/-- Reflection sends every classical collision-free solution to another
    solution on the same interval. -/
theorem classicalNewtonSolution_reflect {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) :
    ClassicalNewtonSolution (fun t => reflectPhase (z t)) I := by
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
    have hderiv' : HasDerivAt (fun s => reflectPhase (z s))
        (reflectPhase (unitNewtonField (z t))) t := by
      simpa [reflectPhaseCLM, reflectPhaseLinear, Function.comp_def] using hderiv
    rw [← unitNewtonField_reflectPhase (z t)] at hderiv'
    exact hderiv'

end

end DroppingThreeBodies
