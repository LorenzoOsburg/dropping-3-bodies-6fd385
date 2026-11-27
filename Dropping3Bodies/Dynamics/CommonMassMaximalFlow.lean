module

public import Dropping3Bodies.Dynamics.CompleteEqualMassResult
public import Dropping3Bodies.Dynamics.GravityRescaling
public import Dropping3Bodies.Dynamics.MaximalInterval
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Tactic

@[expose] public section

/-! A maximal common-mass flow is the gravity-time-rescaling of the existing
unit-mass maximal union. We prove the converse rescaling as well, so every
local common-mass solution interval embeds in this domain. -/

namespace DroppingThreeBodies

noncomputable section

set_option maxHeartbeats 1000000

/-- Reverse the positive gravity rescaling: a solution for the equal-mass
field with coefficient `κ²` becomes a unit-field solution. -/
theorem timeScalePhaseCLM_inverse_derivative_identity {κ : ℝ} (hκ : κ ≠ 0)
    (z : Phase) :
    timeScalePhaseCLM κ⁻¹
      (κ⁻¹ • generalNewtonField (κ ^ 2) (fun _ : Fin 3 => (1 : ℝ)) z) =
      unitNewtonField (timeScalePhase κ⁻¹ z) := by
  apply Prod.ext
  · funext i
    rfl
  · funext i
    change κ⁻¹ • (κ⁻¹ • generalAcceleration (κ ^ 2)
      (fun _ : Fin 3 => (1 : ℝ)) z.1 i) = unitAcceleration z.1 i
    rw [generalAcceleration_equalMass_eq_scalar_unit]
    rw [smul_smul, smul_smul]
    have hcoef : κ⁻¹ * κ⁻¹ * κ ^ 2 = 1 := by
      field_simp [hκ]
    rw [hcoef]
    simp

/-- A solution of the common-mass field, with effective coefficient `κ²`,
can be pulled back to a unit-mass solution on the inverse-rescaled interval. -/
theorem generalNewtonSolution_reverseGravityRescale
    {κ : ℝ} (hκ : 0 < κ) {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution (κ ^ 2)
      (fun _ : Fin 3 => (1 : ℝ)) z I) :
    ClassicalNewtonSolution (gravityRescaledTrajectory κ⁻¹ z)
      (gravityRescaledDomain κ⁻¹ I) := by
  have htimeCont : Continuous (fun t : ℝ => κ⁻¹ * t) := continuous_const_mul _
  refine ⟨hsol.1.preimage htimeCont, ?_⟩
  intro t ht
  have ht' : κ⁻¹ * t ∈ I := ht
  have hregular := hsol.2 (κ⁻¹ * t) ht'
  refine ⟨hregular.1, ?_⟩
  have htime : HasDerivAt (fun s : ℝ => κ⁻¹ * s) κ⁻¹ t :=
    hasDerivAt_const_mul (x := t) κ⁻¹
  have hcomp : HasDerivAt (fun s => z (κ⁻¹ * s))
      (κ⁻¹ • generalNewtonField (κ ^ 2)
        (fun _ : Fin 3 => (1 : ℝ)) (z (κ⁻¹ * t))) t := by
    simpa [Function.comp_def] using HasDerivAt.scomp t hregular.2 htime
  have hscaled :=
    (HasFDerivAt.comp t (timeScalePhaseCLM κ⁻¹).hasFDerivAt
      hcomp.hasFDerivAt).hasDerivAt
  have hcurve : gravityRescaledTrajectory κ⁻¹ z =
      fun s => timeScalePhaseCLM κ⁻¹ (z (κ⁻¹ * s)) := by
    funext s
    rfl
  rw [hcurve]
  have hderiv : HasDerivAt
      (fun s => timeScalePhaseCLM κ⁻¹ (z (κ⁻¹ * s)))
      (timeScalePhaseCLM κ⁻¹
        (κ⁻¹ • generalNewtonField (κ ^ 2)
          (fun _ : Fin 3 => (1 : ℝ)) (z (κ⁻¹ * t)))) t := by
    simpa [timeScalePhaseCLM, timeScalePhaseLinear, Function.comp_def] using hscaled
  change HasDerivAt _ (unitNewtonField
    (timeScalePhase κ⁻¹ (z (κ⁻¹ * t)))) t
  rw [← timeScalePhaseCLM_inverse_derivative_identity hκ.ne' (z (κ⁻¹ * t))]
  exact hderiv

/-- The effective-gravity identity lets an arbitrary common positive mass
be handled by the same time scale `sqrt (G*μ)`. -/
theorem generalNewtonSolution_commonMass_reverseGravityRescale
    (G μ κ : ℝ) (hκ : 0 < κ) (hκsq : κ ^ 2 = G * μ)
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ) z I) :
    ClassicalNewtonSolution (gravityRescaledTrajectory κ⁻¹ z)
      (gravityRescaledDomain κ⁻¹ I) := by
  have hsolEff : GeneralClassicalNewtonSolution (κ ^ 2)
      (fun _ : Fin 3 => (1 : ℝ)) z I := by
    refine ⟨hsol.1, ?_⟩
    intro t ht
    obtain ⟨hcf, hderiv⟩ := hsol.2 t ht
    rw [generalNewtonField_commonMass_eq_effectiveGravity G μ (z t)] at hderiv
    rw [← hκsq] at hderiv
    exact ⟨hcf, hderiv⟩
  exact generalNewtonSolution_reverseGravityRescale hκ hsolEff

/-- Actual maximal domain for equal positive masses and positive gravity,
identified by the positive rescaling of the unit-mass maximal union. -/
noncomputable def commonMassMaximalNewtonDomain (G μ : ℝ)
    (z₀ : Phase) : Set ℝ :=
  gravityRescaledDomain (Real.sqrt (G * μ)) (maximalNewtonUnionDomain z₀)

/-- The corresponding actual maximal trajectory, with positions unchanged and
velocities scaled by `sqrt (G*μ)`. -/
noncomputable def commonMassMaximalNewtonTrajectory (G μ : ℝ)
    (z₀ : Phase) : ℝ → Phase :=
  gravityRescaledTrajectory (Real.sqrt (G * μ))
    (maximalNewtonUnionTrajectory z₀)

/-- The scaled unit union is a solution of the common-mass Newton field. -/
theorem commonMassMaximalNewtonTrajectory_solution
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ) (z₀ : Phase) :
    GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ)
      (commonMassMaximalNewtonTrajectory G μ z₀)
      (commonMassMaximalNewtonDomain G μ z₀) := by
  let κ := Real.sqrt (G * μ)
  have hκ : 0 < κ := Real.sqrt_pos.2 (mul_pos hG hμ)
  have hκsq : κ ^ 2 = G * μ := Real.sq_sqrt (le_of_lt (mul_pos hG hμ))
  have hunit : ClassicalNewtonSolution (maximalNewtonUnionTrajectory z₀)
      (maximalNewtonUnionDomain z₀) := maximalNewtonUnionTrajectory_solution z₀
  have hscaled := classicalNewtonSolution_timeRescale κ hunit
  have hscaledEff : GeneralClassicalNewtonSolution (G * μ)
      (fun _ : Fin 3 => (1 : ℝ))
      (gravityRescaledTrajectory κ (maximalNewtonUnionTrajectory z₀))
      (gravityRescaledDomain κ (maximalNewtonUnionDomain z₀)) := by
    simpa [hκsq] using hscaled
  change GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ)
    (gravityRescaledTrajectory κ (maximalNewtonUnionTrajectory z₀))
    (gravityRescaledDomain κ (maximalNewtonUnionDomain z₀))
  refine ⟨hscaledEff.1, ?_⟩
  intro t ht
  obtain ⟨hcf, hderiv⟩ := hscaledEff.2 t ht
  rw [generalNewtonField_commonMass_eq_effectiveGravity G μ
    (gravityRescaledTrajectory κ (maximalNewtonUnionTrajectory z₀) t)]
  exact ⟨hcf, hderiv⟩

/-- Initial-value agreement for the common-mass maximal trajectory. -/
theorem commonMassMaximalNewtonTrajectory_initial
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ) (z₀ : Phase)
    (hcf : CollisionFree z₀.1) (hrest : ∀ i, z₀.2 i = 0) :
    commonMassMaximalNewtonTrajectory G μ z₀ 0 = z₀ := by
  let κ := Real.sqrt (G * μ)
  have hκ : 0 < κ := Real.sqrt_pos.2 (mul_pos hG hμ)
  have hinit := maximalNewtonUnionTrajectory_initial z₀ hcf
  change timeScalePhase κ (maximalNewtonUnionTrajectory z₀ (κ * 0)) = z₀
  rw [mul_zero, hinit]
  apply Prod.ext
  · rfl
  · funext i
    simp [timeScalePhase, hrest i]

/-- A local interval witness for fixed equal positive masses and gravity. -/
structure CommonMassNewtonInitialIntervalWitness
    (G μ : ℝ) (z₀ : Phase) where
  left : ℝ
  right : ℝ
  trajectory : ℝ → Phase
  left_lt_zero : left < 0
  zero_lt_right : 0 < right
  initial : trajectory 0 = z₀
  solution : GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ)
    trajectory (Set.Ioo left right)

/-- Pulling the inverse time change over an open interval gives the scaled
open interval. -/
theorem gravityRescaledDomain_inverse_Ioo {κ : ℝ} (hκ : 0 < κ)
    (a b : ℝ) :
    gravityRescaledDomain κ⁻¹ (Set.Ioo a b) = Set.Ioo (κ * a) (κ * b) := by
  ext t
  simp only [gravityRescaledDomain, Set.mem_preimage, Set.mem_Ioo]
  have hmul : κ * (κ⁻¹ * t) = t := by
    field_simp [hκ.ne']
  constructor
  · intro ht
    constructor
    · calc
        κ * a < κ * (κ⁻¹ * t) := mul_lt_mul_of_pos_left ht.1 hκ
        _ = t := hmul
    · calc
        t = κ * (κ⁻¹ * t) := hmul.symm
        _ < κ * b := mul_lt_mul_of_pos_left ht.2 hκ
  · intro ht
    constructor
    · have h := mul_lt_mul_of_pos_left ht.1 (inv_pos.mpr hκ)
      simpa [hκ.ne'] using h
    · have h := mul_lt_mul_of_pos_left ht.2 (inv_pos.mpr hκ)
      simpa [hκ.ne'] using h

/-- Every local equal-common-mass solution interval is contained in the
rescaled unit maximal domain. Thus the displayed flow is domain-maximal among
all regular interval solutions with the prescribed rest initial value. -/
theorem commonMassMaximalNewtonDomain_contains_intervalWitness
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ) (z₀ : Phase)
    (hrest : ∀ i, z₀.2 i = 0)
    (w : CommonMassNewtonInitialIntervalWitness G μ z₀) :
    Set.Ioo w.left w.right ⊆ commonMassMaximalNewtonDomain G μ z₀ := by
  let κ := Real.sqrt (G * μ)
  have hκ : 0 < κ := Real.sqrt_pos.2 (mul_pos hG hμ)
  have hκsq : κ ^ 2 = G * μ := Real.sq_sqrt (le_of_lt (mul_pos hG hμ))
  let zU := gravityRescaledTrajectory κ⁻¹ w.trajectory
  have hsolU0 := generalNewtonSolution_commonMass_reverseGravityRescale
    G μ κ hκ hκsq w.solution
  have hsolU : ClassicalNewtonSolution zU (Set.Ioo (κ * w.left) (κ * w.right)) := by
    simpa [zU, gravityRescaledDomain_inverse_Ioo hκ] using hsolU0
  have hinitU : zU 0 = z₀ := by
    have hphase : timeScalePhase κ⁻¹ (w.trajectory 0) = z₀ := by
      rw [w.initial]
      apply Prod.ext
      · rfl
      · funext i
        simp [timeScalePhase, hrest i]
    simpa [zU, gravityRescaledTrajectory, timeScalePhase] using hphase
  let wU : NewtonInitialIntervalWitness z₀ :=
    ⟨κ * w.left, κ * w.right, zU,
      by
        have hpos : 0 < κ * (-w.left) :=
          mul_pos hκ (neg_pos.mpr w.left_lt_zero)
        nlinarith [hpos],
      mul_pos hκ w.zero_lt_right, hinitU, hsolU⟩
  intro t ht
  change κ * t ∈ maximalNewtonUnionDomain z₀
  apply maximalNewtonWitness_interval_subset z₀ wU
  constructor
  · exact mul_lt_mul_of_pos_left ht.1 hκ
  · exact mul_lt_mul_of_pos_left ht.2 hκ
/-- Forward rescaling of an open interval by a positive time factor. -/
theorem gravityRescaledDomain_pos_Ioo {κ : ℝ} (hκ : 0 < κ)
    (a b : ℝ) :
    gravityRescaledDomain κ (Set.Ioo a b) =
      Set.Ioo (κ⁻¹ * a) (κ⁻¹ * b) := by
  simpa [inv_inv] using
    (gravityRescaledDomain_inverse_Ioo (κ := κ⁻¹) (inv_pos.mpr hκ) a b)

/-- The union of all local common-mass interval witnesses at the given
initial phase. -/
noncomputable def commonMassNewtonUnionDomain (G μ : ℝ) (z₀ : Phase) : Set ℝ :=
  ⋃₀ {s : Set ℝ | ∃ w : CommonMassNewtonInitialIntervalWitness G μ z₀,
    s = Set.Ioo w.left w.right}

/-- The rescaled unit maximal domain agrees exactly with the union of every
regular general-mass interval witness from the same rest initial phase. -/
theorem commonMassNewtonUnionDomain_eq_maximalDomain
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ) (z₀ : Phase)
    (hrest : ∀ i, z₀.2 i = 0) :
    commonMassNewtonUnionDomain G μ z₀ =
      commonMassMaximalNewtonDomain G μ z₀ := by
  let κ := Real.sqrt (G * μ)
  have hκ : 0 < κ := Real.sqrt_pos.2 (mul_pos hG hμ)
  have hκsq : κ ^ 2 = G * μ := Real.sq_sqrt (le_of_lt (mul_pos hG hμ))
  apply Set.ext
  intro t
  constructor
  · intro ht
    rcases Set.mem_sUnion.mp ht with ⟨s, ⟨w, rfl⟩, ht⟩
    exact commonMassMaximalNewtonDomain_contains_intervalWitness
      G μ hG hμ z₀ hrest w ht
  · intro ht
    change κ * t ∈ maximalNewtonUnionDomain z₀ at ht
    obtain ⟨wU, htU⟩ := maximalNewtonUnionDomain_covered z₀ ht
    let zG := gravityRescaledTrajectory κ wU.trajectory
    let DG := Set.Ioo (κ⁻¹ * wU.left) (κ⁻¹ * wU.right)
    have hsolEff := classicalNewtonSolution_timeRescale κ wU.solution
    have hsolEff' : GeneralClassicalNewtonSolution (G * μ)
        (fun _ : Fin 3 => (1 : ℝ)) zG DG := by
      simpa [zG, DG, hκsq, gravityRescaledDomain_pos_Ioo hκ] using hsolEff
    have hsolG : GeneralClassicalNewtonSolution G
        (fun _ : Fin 3 => μ) zG DG := by
      refine ⟨hsolEff'.1, ?_⟩
      intro s hs
      obtain ⟨hcfS, hderiv⟩ := hsolEff'.2 s hs
      rw [generalNewtonField_commonMass_eq_effectiveGravity G μ (zG s)]
      exact ⟨hcfS, hderiv⟩
    have hinitG : zG 0 = z₀ := by
      change timeScalePhase κ (wU.trajectory (κ * 0)) = z₀
      rw [mul_zero, wU.initial]
      apply Prod.ext
      · rfl
      · funext i
        simp [timeScalePhase, hrest i]
    let wG : CommonMassNewtonInitialIntervalWitness G μ z₀ :=
      ⟨κ⁻¹ * wU.left, κ⁻¹ * wU.right, zG,
        mul_neg_of_pos_of_neg (inv_pos.mpr hκ) (by linarith [wU.left_lt_zero]),
        mul_pos (inv_pos.mpr hκ) wU.zero_lt_right,
        hinitG,
        hsolG⟩
    have htG : t ∈ Set.Ioo wG.left wG.right := by
      change t ∈ Set.Ioo (κ⁻¹ * wU.left) (κ⁻¹ * wU.right)
      rw [← gravityRescaledDomain_pos_Ioo hκ]
      change κ * t ∈ Set.Ioo wU.left wU.right
      exact htU
    exact Set.mem_sUnion.mpr ⟨Set.Ioo wG.left wG.right,
      ⟨wG, rfl⟩, htG⟩
end

end DroppingThreeBodies
