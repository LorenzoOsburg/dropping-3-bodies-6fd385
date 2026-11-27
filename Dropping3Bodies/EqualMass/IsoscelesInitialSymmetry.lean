module

public import Dropping3Bodies.EqualMass.IsoscelesSymmetry
public import Dropping3Bodies.EqualMass.IsoscelesReduction
public import Mathlib.Tactic

@[expose] public section

namespace DroppingThreeBodies

noncomputable section

theorem isoscelesConfiguration_fixed_by_symmetry (x u v : ℝ) :
    isoscelesSymmetryConfiguration (isoscelesConfiguration x u v) =
      isoscelesConfiguration x u v := by
  funext i
  fin_cases i
  all_goals
    ext k
    fin_cases k <;>
      simp [isoscelesSymmetryConfiguration, isoscelesConfiguration,
        isoscelesIndexSwap, verticalReflectPoint, reflectPoint, pointXY]

theorem isoscelesRestPhase_fixed_by_symmetry (x u v : ℝ) :
    isoscelesSymmetryPhase
      (isoscelesConfiguration x u v, fun _ : Fin 3 => (0 : Point)) =
      (isoscelesConfiguration x u v, fun _ : Fin 3 => (0 : Point)) := by
  apply Prod.ext
  · exact isoscelesConfiguration_fixed_by_symmetry x u v
  · funext i
    simp [isoscelesSymmetryPhase, isoscelesSymmetryConfiguration,
      verticalReflectPoint]

end

end DroppingThreeBodies
