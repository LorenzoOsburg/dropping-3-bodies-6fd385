module

public import Dropping3Bodies.Dynamics.GeneralEnergy
public import Dropping3Bodies.Dynamics.MaximalTranslation
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Tactic

@[expose] public section

/-! Positive changes of Newton's gravitational constant are time rescalings. -/

namespace DroppingThreeBodies

noncomputable section

def timeScalePhase (κ : ℝ) (z : Phase) : Phase :=
  (z.1, fun i => κ • z.2 i)

def timeScalePhaseLinear (κ : ℝ) : Phase →ₗ[ℝ] Phase where
  toFun := timeScalePhase κ
  map_add' z w := by
    apply Prod.ext
    · rfl
    · funext i
      simp [timeScalePhase, smul_add]
  map_smul' c z := by
    apply Prod.ext
    · simp [timeScalePhase]
    · funext i
      simp [timeScalePhase, smul_smul, mul_comm]

noncomputable def timeScalePhaseCLM (κ : ℝ) : Phase →L[ℝ] Phase :=
  (timeScalePhaseLinear κ).toContinuousLinearMap

def gravityRescaledTrajectory (κ : ℝ) (z : ℝ → Phase) : ℝ → Phase :=
  fun t => timeScalePhase κ (z (κ * t))

def gravityRescaledDomain (κ : ℝ) (I : Set ℝ) : Set ℝ :=
  (fun t : ℝ => κ * t) ⁻¹' I

theorem generalAcceleration_equalMass_eq_scalar_unit (G : ℝ)
    (q : Fin 3 → Point) (i : Fin 3) :
    generalAcceleration G (fun _ : Fin 3 => (1 : ℝ)) q i =
      G • unitAcceleration q i := by
  fin_cases i <;>
    simp [generalAcceleration, unitAcceleration, inverseCubeDistance,
      Fin.sum_univ_succ] <;> module

theorem timeScalePhaseCLM_derivative_identity (κ : ℝ) (z : Phase) :
    timeScalePhaseCLM κ (κ • unitNewtonField z) =
      generalNewtonField (κ ^ 2) (fun _ : Fin 3 => (1 : ℝ)) (timeScalePhase κ z) := by
  apply Prod.ext
  · rfl
  · funext i
    simp [timeScalePhaseCLM, timeScalePhaseLinear, timeScalePhase,
      unitNewtonField, generalNewtonField, generalAcceleration_equalMass_eq_scalar_unit,
      smul_smul, pow_two]

theorem classicalNewtonSolution_timeRescale
    {z : ℝ → Phase} {I : Set ℝ} (κ : ℝ)
    (hsol : ClassicalNewtonSolution z I) :
    GeneralClassicalNewtonSolution (κ ^ 2) (fun _ : Fin 3 => (1 : ℝ))
      (gravityRescaledTrajectory κ z) (gravityRescaledDomain κ I) := by
  have htimeCont : Continuous (fun t : ℝ => κ * t) := continuous_const_mul κ
  refine ⟨hsol.1.preimage htimeCont, ?_⟩
  intro t ht
  have ht' : κ * t ∈ I := ht
  have hregular := hsol.2 (κ * t) ht'
  constructor
  · exact hregular.1
  · have htime : HasDerivAt (fun t : ℝ => κ * t) κ t :=
      hasDerivAt_const_mul (x := t) κ
    have hcomp : HasDerivAt (fun s => z (κ * s))
        (κ • unitNewtonField (z (κ * t))) t := by
      simpa [Function.comp_def] using HasDerivAt.scomp t hregular.2 htime
    have hscaled :=
      (HasFDerivAt.comp t (timeScalePhaseCLM κ).hasFDerivAt
        hcomp.hasFDerivAt).hasDerivAt
    have hcurve : gravityRescaledTrajectory κ z =
        fun s => timeScalePhaseCLM κ (z (κ * s)) := by
      funext s
      rfl
    rw [hcurve]
    have hderiv : HasDerivAt (fun s => timeScalePhaseCLM κ (z (κ * s)))
        (timeScalePhaseCLM κ (κ • unitNewtonField (z (κ * t)))) t := by
      simpa [timeScalePhaseCLM, timeScalePhaseLinear, Function.comp_def] using hscaled
    change HasDerivAt (fun s => timeScalePhaseCLM κ (z (κ * s)))
      (generalNewtonField (κ ^ 2) (fun _ : Fin 3 => (1 : ℝ))
        (timeScalePhase κ (z (κ * t)))) t
    rw [← timeScalePhaseCLM_derivative_identity κ (z (κ * t))]
    exact hderiv

/-- The strict-longest-side equal-mass conclusion is independent of the
    positive value of Newton's gravitational constant. -/
theorem exists_generalNewton_firstSyzygy_middleBody_of_equalMass_strictLongest
    (G : ℝ) (hG : 0 < G) (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (harea₀ : signedDoubleArea z₀.1 ≠ 0)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ (z : ℝ → Phase) (I : Set ℝ) (T : ℝ),
      GeneralClassicalNewtonSolution G (fun _ : Fin 3 => (1 : ℝ)) z I ∧
      T ∈ I ∧ 0 < T ∧
      Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i) ((z T).1 (cyclicNext i)) := by
  let κ := Real.sqrt G
  have hκpos : 0 < κ := Real.sqrt_pos.2 hG
  have hκsq : κ ^ 2 = G := Real.sq_sqrt (le_of_lt hG)
  let zUnit := maximalNewtonUnionTrajectory z₀
  let DUnit := maximalNewtonUnionDomain z₀
  obtain ⟨TUnit, hTUnit, hTUnitPos, hbetweenUnit⟩ :=
    maximalNewtonUnion_body_between_at_first_syzygy_of_uncentered_strictLongest
      z₀ hcf hrest harea₀ i hlongPrev hlongNext
  let zG := gravityRescaledTrajectory κ zUnit
  let IG := gravityRescaledDomain κ DUnit
  let TG := TUnit / κ
  have hsolUnit : ClassicalNewtonSolution zUnit DUnit :=
    maximalNewtonUnionTrajectory_solution z₀
  have hsolG' := classicalNewtonSolution_timeRescale κ hsolUnit
  have hsolG : GeneralClassicalNewtonSolution G
      (fun _ : Fin 3 => (1 : ℝ)) zG IG := by
    change GeneralClassicalNewtonSolution G (fun _ : Fin 3 => (1 : ℝ))
      (gravityRescaledTrajectory κ zUnit) (gravityRescaledDomain κ DUnit)
    rw [← hκsq]
    exact hsolG'
  have htime : κ * TG = TUnit := by
    dsimp [TG]
    field_simp [ne_of_gt hκpos]
  have hTGdomain : TG ∈ IG := by
    change κ * TG ∈ DUnit
    rw [htime]
    exact hTUnit
  have hTGpos : 0 < TG := div_pos hTUnitPos hκpos
  have hbetweenG :
      Sbtw ℝ ((zG TG).1 (cyclicPrev i)) ((zG TG).1 i) ((zG TG).1 (cyclicNext i)) := by
    simpa [zG, gravityRescaledTrajectory, timeScalePhase, htime] using hbetweenUnit
  exact ⟨zG, IG, TG, hsolG, hTGdomain, hTGpos, hbetweenG⟩

end

end DroppingThreeBodies
