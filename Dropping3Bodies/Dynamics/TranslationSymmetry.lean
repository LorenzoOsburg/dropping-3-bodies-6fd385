module

public import Dropping3Bodies.Dynamics.Newton
public import Dropping3Bodies.Geometry.Translation
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic

@[expose] public section

/-! Translation symmetry of the unit-mass Newton equation. -/

namespace DroppingThreeBodies

noncomputable section

def translatePhase (c : Point) (z : Phase) : Phase :=
  (translateConfiguration c z.1, z.2)

def translationPhaseShift (c : Point) : Phase :=
  (fun _ => c, fun _ => 0)

theorem inverseCubeDistance_translateConfiguration
    (c : Point) (q : Fin 3 → Point) (i j : Fin 3) :
    inverseCubeDistance (translateConfiguration c q) i j = inverseCubeDistance q i j := by
  simp [inverseCubeDistance, dist_translateConfiguration]

theorem unitAcceleration_translateConfiguration
    (c : Point) (q : Fin 3 → Point) (i : Fin 3) :
    unitAcceleration (translateConfiguration c q) i = unitAcceleration q i := by
  fin_cases i <;>
    simp [unitAcceleration, inverseCubeDistance_translateConfiguration,
      translateConfiguration, translatePoint, add_sub_add_right_eq_sub]

theorem unitNewtonField_translatePhase (c : Point) (z : Phase) :
    unitNewtonField (translatePhase c z) = unitNewtonField z := by
  cases z with
  | mk q v =>
      apply Prod.ext
      · rfl
      · funext i
        exact unitAcceleration_translateConfiguration c q i

theorem translatePhase_eq_add_shift (c : Point) (z : Phase) :
    translatePhase c z = z + translationPhaseShift c := by
  apply Prod.ext
  · funext i
    simp [translatePhase, translationPhaseShift, translateConfiguration, translatePoint]
  · funext i
    simp [translatePhase, translationPhaseShift]

theorem classicalNewtonSolution_translate {z : ℝ → Phase} {I : Set ℝ}
    (c : Point) (hsol : ClassicalNewtonSolution z I) :
    ClassicalNewtonSolution (fun t => translatePhase c (z t)) I := by
  refine ⟨hsol.1, fun t ht => ?_⟩
  have hregular := hsol.2 t ht
  constructor
  · intro i j hij
    apply dist_pos.mp
    change 0 < dist (translatePoint c ((z t).1 i)) (translatePoint c ((z t).1 j))
    rw [translatePoint_dist]
    exact dist_pos.mpr (hregular.1 i j hij)
  · have hshift : HasDerivAt (fun _ : ℝ => translationPhaseShift c) 0 t :=
      hasDerivAt_const t (translationPhaseShift c)
    have hsum := hregular.2.add hshift
    have hfield := unitNewtonField_translatePhase c (z t)
    have hsum' : HasDerivAt (z + fun _ : ℝ => translationPhaseShift c)
        (unitNewtonField (z t)) t := by
      simpa using hsum
    have hcurve : (fun s => translatePhase c (z s)) =
        z + fun _ : ℝ => translationPhaseShift c := by
      funext s
      exact translatePhase_eq_add_shift c (z s)
    rw [hcurve]
    change HasDerivAt (z + fun _ : ℝ => translationPhaseShift c)
      (unitNewtonField (z t + translationPhaseShift c)) t
    rw [← translatePhase_eq_add_shift c (z t), hfield]
    exact hsum'

end

end DroppingThreeBodies
