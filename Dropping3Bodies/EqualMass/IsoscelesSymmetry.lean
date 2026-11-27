module

public import Dropping3Bodies.Dynamics.Newton
public import Dropping3Bodies.Dynamics.RegularDomain
public import Dropping3Bodies.Geometry.Reflection
public import Mathlib.Tactic

@[expose] public section

/-!
# Vertical reflection symmetry of the equal-mass three-body equation

The symmetry relevant to an isosceles triangle reflects across the vertical
axis and exchanges the two base-body labels.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Reflection across the vertical axis, obtained from the existing horizontal
    reflection by central inversion. -/
def verticalReflectPoint (p : Point) : Point := -reflectPoint p

theorem verticalReflectPoint_add (p q : Point) :
    verticalReflectPoint (p + q) = verticalReflectPoint p + verticalReflectPoint q := by
  ext i
  fin_cases i
  all_goals simp [verticalReflectPoint, reflectPoint]
  all_goals abel

theorem verticalReflectPoint_sub (p q : Point) :
    verticalReflectPoint (p - q) = verticalReflectPoint p - verticalReflectPoint q := by
  ext i
  fin_cases i
  all_goals simp [verticalReflectPoint, reflectPoint]
  all_goals abel

theorem verticalReflectPoint_smul (c : ℝ) (p : Point) :
    verticalReflectPoint (c • p) = c • verticalReflectPoint p := by
  simp [verticalReflectPoint, reflectPoint_smul]

theorem verticalReflectPoint_dist (p q : Point) :
    dist (verticalReflectPoint p) (verticalReflectPoint q) = dist p q := by
  change dist (-reflectPoint p) (-reflectPoint q) = dist p q
  rw [dist_eq_norm, dist_eq_norm]
  rw [show -reflectPoint p - -reflectPoint q =
      -(reflectPoint p - reflectPoint q) by abel]
  rw [norm_neg, ← reflectPoint_sub, reflectPoint_norm]

/-- Exchange bodies 0 and 1 while fixing body 2. -/
def isoscelesIndexSwap : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 0
  | i => i

theorem isoscelesIndexSwap_involutive (i : Fin 3) :
    isoscelesIndexSwap (isoscelesIndexSwap i) = i := by
  fin_cases i <;> rfl

/-- Configuration action of vertical reflection together with the base-body
    exchange. -/
def isoscelesSymmetryConfiguration (q : Fin 3 → Point) : Fin 3 → Point :=
  fun i => verticalReflectPoint (q (isoscelesIndexSwap i))

theorem isoscelesSymmetryConfiguration_dist (q : Fin 3 → Point) (i j : Fin 3) :
    dist (isoscelesSymmetryConfiguration q i)
        (isoscelesSymmetryConfiguration q j) =
      dist (q (isoscelesIndexSwap i)) (q (isoscelesIndexSwap j)) := by
  exact verticalReflectPoint_dist _ _

theorem inverseCubeDistance_isoscelesSymmetryConfiguration
    (q : Fin 3 → Point) (i j : Fin 3) :
    inverseCubeDistance (isoscelesSymmetryConfiguration q) i j =
      inverseCubeDistance q (isoscelesIndexSwap i) (isoscelesIndexSwap j) := by
  simp [inverseCubeDistance, isoscelesSymmetryConfiguration_dist]

/-- The acceleration law commutes with this label-preserving geometric
    symmetry. -/
theorem unitAcceleration_isoscelesSymmetryConfiguration
    (q : Fin 3 → Point) (i : Fin 3) :
    verticalReflectPoint (unitAcceleration q (isoscelesIndexSwap i)) =
      unitAcceleration (isoscelesSymmetryConfiguration q) i := by
  fin_cases i
  all_goals simp [unitAcceleration, isoscelesSymmetryConfiguration, isoscelesIndexSwap, verticalReflectPoint_add, verticalReflectPoint_sub, verticalReflectPoint_smul, inverseCubeDistance, verticalReflectPoint_dist]
  all_goals abel

/-- The induced action on position-velocity phase space. -/
def isoscelesSymmetryPhase (z : Phase) : Phase :=
  (isoscelesSymmetryConfiguration z.1, isoscelesSymmetryConfiguration z.2)

def isoscelesSymmetryPhaseLinear : Phase →ₗ[ℝ] Phase where
  toFun := isoscelesSymmetryPhase
  map_add' z w := by
    rcases z with ⟨q, v⟩
    rcases w with ⟨q', v'⟩
    apply Prod.ext
    · funext i
      exact verticalReflectPoint_add (q (isoscelesIndexSwap i))
        (q' (isoscelesIndexSwap i))
    · funext i
      exact verticalReflectPoint_add (v (isoscelesIndexSwap i))
        (v' (isoscelesIndexSwap i))
  map_smul' c z := by
    rcases z with ⟨q, v⟩
    apply Prod.ext
    · funext i
      exact verticalReflectPoint_smul c (q (isoscelesIndexSwap i))
    · funext i
      exact verticalReflectPoint_smul c (v (isoscelesIndexSwap i))

noncomputable def isoscelesSymmetryPhaseCLM : Phase →L[ℝ] Phase :=
  isoscelesSymmetryPhaseLinear.toContinuousLinearMap

theorem unitNewtonField_isoscelesSymmetryPhase (z : Phase) :
    unitNewtonField (isoscelesSymmetryPhase z) =
      isoscelesSymmetryPhase (unitNewtonField z) := by
  cases z with
  | mk q v =>
      apply Prod.ext
      · rfl
      · funext i
        exact (unitAcceleration_isoscelesSymmetryConfiguration q i).symm

/-- The geometric symmetry sends classical equal-mass Newton solutions to
    solutions on the same open time set. -/
theorem classicalNewtonSolution_isoscelesSymmetry
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) :
    ClassicalNewtonSolution (fun t => isoscelesSymmetryPhase (z t)) I := by
  refine ⟨hsol.1, fun t ht => ?_⟩
  have hregular := hsol.2 t ht
  constructor
  · intro i j hij
    apply dist_pos.mp
    change 0 < dist
      (verticalReflectPoint ((z t).1 (isoscelesIndexSwap i)))
      (verticalReflectPoint ((z t).1 (isoscelesIndexSwap j)))
    rw [verticalReflectPoint_dist]
    apply dist_pos.mpr
    have hswap : isoscelesIndexSwap i ≠ isoscelesIndexSwap j := by
      intro heq
      apply hij
      calc
        i = isoscelesIndexSwap (isoscelesIndexSwap i) :=
          (isoscelesIndexSwap_involutive i).symm
        _ = isoscelesIndexSwap (isoscelesIndexSwap j) := congrArg isoscelesIndexSwap heq
        _ = j := isoscelesIndexSwap_involutive j
    exact hregular.1 (isoscelesIndexSwap i) (isoscelesIndexSwap j) hswap
  · have hderiv :=
      (HasFDerivAt.comp t isoscelesSymmetryPhaseCLM.hasFDerivAt
        hregular.2.hasFDerivAt).hasDerivAt
    have hderiv' : HasDerivAt (fun s => isoscelesSymmetryPhase (z s))
        (isoscelesSymmetryPhase (unitNewtonField (z t))) t := by
      simpa [isoscelesSymmetryPhaseCLM, isoscelesSymmetryPhaseLinear,
        Function.comp_def] using hderiv
    rw [← unitNewtonField_isoscelesSymmetryPhase (z t)] at hderiv'
    exact hderiv'

/-- Uniqueness propagates a fixed symmetric initial state over a connected
    classical Newton solution interval. -/
theorem classicalNewtonSolution_isoscelesSymmetric
    {z : ℝ → Phase} {I : Set ℝ} {t₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    (ht₀ : t₀ ∈ I)
    (hfixed : isoscelesSymmetryPhase (z t₀) = z t₀) :
    ∀ t ∈ I, isoscelesSymmetryPhase (z t) = z t := by
  have hmirror := classicalNewtonSolution_isoscelesSymmetry hsol
  have hconn' : IsPreconnected (I ∩ I) := by simpa using hconn
  have ht₀' : t₀ ∈ I ∩ I := ⟨ht₀, ht₀⟩
  have hinit : z t₀ = isoscelesSymmetryPhase (z t₀) := hfixed.symm
  have heq := classicalNewton_eq_on_of_preconnected_overlap
    hsol hmirror hconn' ht₀' hinit
  intro t ht
  exact (heq t ⟨ht, ht⟩).symm

end

end DroppingThreeBodies
