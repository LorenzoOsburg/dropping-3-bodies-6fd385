module

public import Dropping3Bodies.Dynamics.Newton
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Tactic

@[expose] public section

/-!
# Equal-mass equilateral homothety

Algebraic force identity for the exceptional equilateral rest configuration.
The scalar collapse trajectory is treated separately in the X02 plan.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- Time as a function of the auxiliary homothety angle. -/
def homotheticTimeParameter (K θ : ℝ) : ℝ :=
  K * (θ / 2 + Real.sin (2 * θ) / 4)

/-- The parameter-time derivative is `K cos² θ`. -/
theorem hasDerivAt_homotheticTimeParameter (K θ : ℝ) :
    HasDerivAt (homotheticTimeParameter K) (K * Real.cos θ ^ 2) θ := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id' θ).const_mul 2
  have hsin := (Real.hasDerivAt_sin (2 * θ)).comp θ hlinear
  have hleft : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ := by
    simpa using (hasDerivAt_id' θ).div_const 2
  have hright : HasDerivAt (fun x : ℝ => Real.sin (2 * x) / 4)
      (2 * Real.cos (2 * θ) / 4) θ := by
    simpa [mul_comm] using hsin.div_const 4
  have hbase := hleft.add hright
  have hscaled := hbase.const_mul K
  have hcoeff : K * (1 / 2 + 2 * Real.cos (2 * θ) / 4) =
      K * Real.cos θ ^ 2 := by
    rw [Real.cos_two_mul]
    ring
  change HasDerivAt (fun x : ℝ => K * (x / 2 + Real.sin (2 * x) / 4))
    (K * Real.cos θ ^ 2) θ
  exact hscaled.congr_deriv hcoeff

/-- The time-parametrization endpoints enclose time zero strictly. -/
theorem homotheticTimeParameter_left_lt_zero_right
    (K : ℝ) (hK : 0 < K) :
    homotheticTimeParameter K (-(Real.pi / 4)) < 0 ∧
      0 < homotheticTimeParameter K (Real.pi / 2) := by
  have hsin : Real.sin (-(Real.pi / 2)) = -1 := by simp
  have hleft : homotheticTimeParameter K (-(Real.pi / 4)) =
      K * (-(Real.pi / 8) - 1 / 4) := by
    calc
      homotheticTimeParameter K (-(Real.pi / 4)) =
          K * ((-(Real.pi / 4)) / 2 + Real.sin (2 * (-(Real.pi / 4))) / 4) := rfl
      _ = K * (-(Real.pi / 8) - 1 / 4) := by
        rw [show 2 * (-(Real.pi / 4)) = -(Real.pi / 2) by ring, hsin]
        congr 1
        ring
  have hright : homotheticTimeParameter K (Real.pi / 2) =
      K * (Real.pi / 4) := by
    calc
      homotheticTimeParameter K (Real.pi / 2) =
          K * ((Real.pi / 2) / 2 + Real.sin (2 * (Real.pi / 2)) / 4) := rfl
      _ = K * (Real.pi / 4) := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        congr 1
        ring
  constructor
  · rw [hleft]
    have hinner : -(Real.pi / 8) - 1 / 4 < 0 := by linarith [Real.pi_pos]
    exact mul_neg_of_pos_of_neg hK hinner
  · rw [hright]
    exact mul_pos hK (by positivity)

/-- A continuous local inverse of the homothetic time parameter has the
    reciprocal derivative wherever `K cos² θ` is nonzero. -/
theorem hasDerivAt_homotheticAngle_of_local_inverse
    {K : ℝ} {θ : ℝ → ℝ} {t : ℝ}
    (hK : K ≠ 0) (hcos : Real.cos (θ t) ≠ 0)
    (hcont : ContinuousAt θ t)
    (hinv : ∀ᶠ s in 𝓝 t, homotheticTimeParameter K (θ s) = s) :
    HasDerivAt θ ((K * Real.cos (θ t) ^ 2)⁻¹) t := by
  have htime := hasDerivAt_homotheticTimeParameter K (θ t)
  have hne : K * Real.cos (θ t) ^ 2 ≠ 0 := mul_ne_zero hK (pow_ne_zero 2 hcos)
  exact htime.of_local_left_inverse hcont hne hinv

/-- The increasing time parametrization is a homeomorphism from the auxiliary
    angle interval onto its endpoint time interval. -/
noncomputable def homotheticTimeHomeomorph (K : ℝ) (hK : 0 < K) :
    Set.Icc (-(Real.pi / 4)) (Real.pi / 2) ≃ₜ
      Set.Icc (homotheticTimeParameter K (-(Real.pi / 4)))
        (homotheticTimeParameter K (Real.pi / 2)) := by
  let a : ℝ := -(Real.pi / 4)
  let b : ℝ := Real.pi / 2
  let f : ℝ → ℝ := homotheticTimeParameter K
  have hab : a < b := by dsimp [a, b]; linarith [Real.pi_pos]
  have hfcontinuous : Continuous f := by
    change Continuous (fun θ : ℝ => K * (θ / 2 + Real.sin (2 * θ) / 4))
    fun_prop
  have hfcont : ContinuousOn f (Set.Icc a b) := hfcontinuous.continuousOn
  have hfderiv : ∀ x ∈ interior (Set.Icc a b), 0 < deriv f x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by simpa [interior_Icc] using hx
    have hlow : -(Real.pi / 2) < x := by
      have hquarter : -(Real.pi / 2) < -(Real.pi / 4) := by
        nlinarith [Real.pi_pos]
      exact lt_trans hquarter hx'.1
    have hxcos : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨hlow, by simpa [b] using hx'.2⟩
    have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxcos
    have hparam : HasDerivAt f (K * Real.cos x ^ 2) x := by
      simpa [f] using hasDerivAt_homotheticTimeParameter K x
    rw [hparam.deriv]
    exact mul_pos hK (sq_pos_of_ne_zero hcos.ne')
  have hfmono : StrictMonoOn f (Set.Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hfcont hfderiv
  have hfmap : ∀ x : Set.Icc a b, f x ∈ Set.Icc (f a) (f b) := by
    intro x
    have hx := x.property
    constructor
    · by_cases hax : (x : ℝ) = a
      · rw [hax]
      · have hne : a ≠ (x : ℝ) := fun h => hax h.symm
        have hlt : a < (x : ℝ) := lt_of_le_of_ne hx.1 hne
        exact (le_of_lt (hfmono ⟨le_rfl, hab.le⟩ x.property hlt))
    · by_cases hxb : (x : ℝ) = b
      · rw [hxb]
      · have hlt : (x : ℝ) < b := lt_of_le_of_ne hx.2 hxb
        exact le_of_lt (hfmono x.property ⟨hab.le, le_rfl⟩ hlt)
  let g : Set.Icc a b → Set.Icc (f a) (f b) := fun x => ⟨f x, hfmap x⟩
  have hfgcontinuous : Continuous f := by
    exact hfcontinuous
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hval : f (x : ℝ) = f (y : ℝ) := congrArg Subtype.val hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (hfmono x.property y.property hlt)) hval
    · exact (ne_of_gt (hfmono y.property x.property hgt)) hval
  have hgsurj : Function.Surjective g := by
    intro y
    have hIV := intermediate_value_Icc (le_of_lt hab) hfcont
    obtain ⟨x, hx, hfx⟩ := hIV y.property
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hfx
  letI : CompactSpace (Set.Icc a b) :=
    (isCompact_iff_compactSpace (s := Set.Icc a b)).mp isCompact_Icc
  have hghome : IsHomeomorph g :=
    (isHomeomorph_iff_continuous_bijective).2 ⟨hgcont, hginj, hgsurj⟩
  simpa [a, b, f] using hghome.homeomorph

/-- Extend the inverse angle continuously to all real times by clamping time
    to the closed interval covered by the parametrization. -/
noncomputable def homotheticAngleFromTime (K : ℝ) (hK : 0 < K) (t : ℝ) : ℝ :=
  (homotheticTimeHomeomorph K hK).symm
    (Set.projIcc
      (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))
      (le_of_lt (lt_trans (homotheticTimeParameter_left_lt_zero_right K hK).1
        (homotheticTimeParameter_left_lt_zero_right K hK).2))
      t)

theorem continuous_homotheticAngleFromTime (K : ℝ) (hK : 0 < K) :
    Continuous (homotheticAngleFromTime K hK) := by
  unfold homotheticAngleFromTime
  fun_prop

theorem homotheticTimeParameter_angleFromTime
    (K : ℝ) (hK : 0 < K) (t : ℝ)
    (ht : t ∈ Set.Icc (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) :
    homotheticTimeParameter K (homotheticAngleFromTime K hK t) = t := by
  have hproj := Set.projIcc_of_mem
    (a := homotheticTimeParameter K (-(Real.pi / 4)))
    (b := homotheticTimeParameter K (Real.pi / 2))
    (h := le_of_lt (lt_trans (homotheticTimeParameter_left_lt_zero_right K hK).1
      (homotheticTimeParameter_left_lt_zero_right K hK).2)) ht
  have hinv := (homotheticTimeHomeomorph K hK).apply_symm_apply ⟨t, ht⟩
  have hval := congrArg (fun x : Set.Icc _ _ => (x : ℝ)) hinv
  change homotheticTimeParameter K
    ((homotheticTimeHomeomorph K hK).symm ⟨t, ht⟩ : ℝ) = t at hval
  unfold homotheticAngleFromTime
  rw [hproj]
  exact hval

theorem homotheticTimeParameter_angleFromTime_eventually
    (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) :
    ∀ᶠ s in 𝓝 t, homotheticTimeParameter K (homotheticAngleFromTime K hK s) = s := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact homotheticTimeParameter_angleFromTime K hK s
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩

/-- The inverse angle is zero at physical time zero. -/
theorem homotheticAngleFromTime_zero (K : ℝ) (hK : 0 < K) :
    homotheticAngleFromTime K hK 0 = 0 := by
  have hend := homotheticTimeParameter_left_lt_zero_right K hK
  have htmem : (0 : ℝ) ∈ Set.Icc
      (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2)) :=
    ⟨le_of_lt hend.1, le_of_lt hend.2⟩
  have htime := homotheticTimeParameter_angleFromTime K hK 0 htmem
  have hzero : homotheticTimeParameter K 0 = 0 := by
    simp [homotheticTimeParameter]
  have hθmem : homotheticAngleFromTime K hK 0 ∈
      Set.Icc (-(Real.pi / 4)) (Real.pi / 2) := by
    unfold homotheticAngleFromTime
    exact ((homotheticTimeHomeomorph K hK).symm
      (Set.projIcc
        (homotheticTimeParameter K (-(Real.pi / 4)))
        (homotheticTimeParameter K (Real.pi / 2))
        (le_of_lt (lt_trans hend.1 hend.2)) 0)).property
  have hzeroAngle : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hinj := (homotheticTimeHomeomorph K hK).injective
  have hsub : (⟨homotheticAngleFromTime K hK 0, hθmem⟩ :
      Set.Icc (-(Real.pi / 4)) (Real.pi / 2)) = ⟨0, hzeroAngle⟩ := by
    apply hinj
    apply Subtype.ext
    change homotheticTimeParameter K (homotheticAngleFromTime K hK 0) =
      homotheticTimeParameter K 0
    exact htime.trans hzero.symm
  exact congrArg (fun x : Set.Icc (-(Real.pi / 4)) (Real.pi / 2) => (x : ℝ)) hsub

theorem homotheticAngleFromTime_cos_pos
    (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) :
    0 < Real.cos (homotheticAngleFromTime K hK t) := by
  let θ := (homotheticTimeHomeomorph K hK).symm
    (Set.projIcc
      (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))
      (le_of_lt (lt_trans (homotheticTimeParameter_left_lt_zero_right K hK).1
        (homotheticTimeParameter_left_lt_zero_right K hK).2))
      t)
  have hθmem : (θ : ℝ) ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 2) := θ.property
  have htime := homotheticTimeParameter_angleFromTime K hK t
    ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  change homotheticTimeParameter K (θ : ℝ) = t at htime
  have hθlt : (θ : ℝ) < Real.pi / 2 := by
    by_contra hn
    have heq : (θ : ℝ) = Real.pi / 2 := le_antisymm hθmem.2 (le_of_not_gt hn)
    rw [heq] at htime
    exact (ne_of_gt ht.2).symm htime.symm
  have hθlo : -(Real.pi / 2) < (θ : ℝ) := by
    have hquarter : -(Real.pi / 2) < -(Real.pi / 4) := by
      nlinarith [Real.pi_pos]
    exact lt_of_lt_of_le hquarter hθmem.1
  change 0 < Real.cos (θ : ℝ)
  exact Real.cos_pos_of_mem_Ioo ⟨hθlo, hθlt⟩

/-- The collapsing scale `cos² θ(t)` has the first derivative dictated by
    the inverse time parametrization. -/
def homotheticScale (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.cos (θ t) * Real.cos (θ t)

theorem hasDerivAt_homotheticScale
    {K : ℝ} {θ : ℝ → ℝ} {t : ℝ}
    (hK : K ≠ 0) (hcos : Real.cos (θ t) ≠ 0)
    (hcont : ContinuousAt θ t)
    (hinv : ∀ᶠ s in 𝓝 t, homotheticTimeParameter K (θ s) = s) :
    HasDerivAt (homotheticScale θ) (-(2 / K) * Real.tan (θ t)) t := by
  have hθ := hasDerivAt_homotheticAngle_of_local_inverse hK hcos hcont hinv
  have hcosCurve := (Real.hasDerivAt_cos (θ t)).comp t hθ
  have hprod := hcosCurve.mul hcosCurve
  have hcoeff :
      (-Real.sin (θ t) * (K * Real.cos (θ t) ^ 2)⁻¹) * Real.cos (θ t) +
        Real.cos (θ t) * (-Real.sin (θ t) * (K * Real.cos (θ t) ^ 2)⁻¹) =
      -(2 / K) * Real.tan (θ t) := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hK, hcos]
    ring
  have hfinal := hprod.congr_deriv hcoeff
  change HasDerivAt (Real.cos ∘ θ * Real.cos ∘ θ)
    (-(2 / K) * Real.tan (θ t)) t
  exact hfinal

/-- The derivative of the scale rate gives the scalar collapse equation
    with coefficient `2/K²`. -/
theorem hasDerivAt_homotheticScaleRate
    {K : ℝ} {θ : ℝ → ℝ} {t : ℝ}
    (hK : K ≠ 0) (hcos : Real.cos (θ t) ≠ 0)
    (hcont : ContinuousAt θ t)
    (hinv : ∀ᶠ s in 𝓝 t, homotheticTimeParameter K (θ s) = s) :
    HasDerivAt (fun s : ℝ => -(2 / K) * Real.tan (θ s))
      (-(2 / K ^ 2) * (Real.cos (θ t) ^ 4)⁻¹) t := by
  have hθ := hasDerivAt_homotheticAngle_of_local_inverse hK hcos hcont hinv
  have htan := (Real.hasDerivAt_tan hcos).comp t hθ
  have hscaled := htan.const_mul (-(2 / K))
  have hcoeff : (-(2 / K)) * ((1 / Real.cos (θ t) ^ 2) *
      (K * Real.cos (θ t) ^ 2)⁻¹) =
      -(2 / K ^ 2) * (Real.cos (θ t) ^ 4)⁻¹ := by
    field_simp [hK, hcos]
  exact hscaled.congr_deriv hcoeff

/-- The scale evaluated on the canonical inverse time curve. -/
def homotheticScaleFromTime (K : ℝ) (hK : 0 < K) (t : ℝ) : ℝ :=
  homotheticScale (homotheticAngleFromTime K hK) t

/-- The rate of the canonical scale curve. -/
def homotheticScaleRateFromTime (K : ℝ) (hK : 0 < K) (t : ℝ) : ℝ :=
  -(2 / K) * Real.tan (homotheticAngleFromTime K hK t)

/-- The canonical scale has the expected velocity at every interior time. -/
theorem hasDerivAt_homotheticScaleFromTime
    (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) :
    HasDerivAt (homotheticScaleFromTime K hK)
      (homotheticScaleRateFromTime K hK t) t := by
  have hcos := homotheticAngleFromTime_cos_pos K hK ht
  have hcont := (continuous_homotheticAngleFromTime K hK).continuousAt (x := t)
  have hinv := homotheticTimeParameter_angleFromTime_eventually K hK ht
  have hderiv := hasDerivAt_homotheticScale hK.ne' hcos.ne' hcont hinv
  change HasDerivAt (homotheticScale (homotheticAngleFromTime K hK))
    (-(2 / K) * Real.tan (homotheticAngleFromTime K hK t)) t
  exact hderiv

/-- The scale rate satisfies the scalar inverse-square equation, with
    coefficient `2/K²`, throughout the regular time interval. -/
theorem hasDerivAt_homotheticScaleRateFromTime
    (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) :
    HasDerivAt (homotheticScaleRateFromTime K hK)
      (-(2 / K ^ 2) * (homotheticScaleFromTime K hK t ^ 2)⁻¹) t := by
  have hcos := homotheticAngleFromTime_cos_pos K hK ht
  have hcont := (continuous_homotheticAngleFromTime K hK).continuousAt (x := t)
  have hinv := homotheticTimeParameter_angleFromTime_eventually K hK ht
  have hderiv := hasDerivAt_homotheticScaleRate hK.ne' hcos.ne' hcont hinv
  have hcos_sq : homotheticScaleFromTime K hK t = Real.cos
      (homotheticAngleFromTime K hK t) ^ 2 := by
    simp [homotheticScaleFromTime, homotheticScale, pow_two]
  rw [hcos_sq]
  convert hderiv using 1
  · rfl
  · congr 1
    rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num]

/-- Positivity of the homothetic scale is exactly the absence of a collision
    before the terminal endpoint. -/
theorem homotheticScaleFromTime_pos
    (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) :
    0 < homotheticScaleFromTime K hK t := by
  rw [homotheticScaleFromTime, homotheticScale]
  exact mul_self_pos.mpr (ne_of_gt (homotheticAngleFromTime_cos_pos K hK ht))

/-- Homothetic positions centered at the initial equal-mass centroid. -/
def homotheticConfiguration (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K)
    (t : ℝ) : Fin 3 → Point :=
  fun i => configurationCentroid q +
    homotheticScaleFromTime K hK t • (q i - configurationCentroid q)

/-- The corresponding velocity field along the homothetic ansatz. -/
def homotheticVelocity (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K)
    (t : ℝ) : Fin 3 → Point :=
  fun i => homotheticScaleRateFromTime K hK t •
    (q i - configurationCentroid q)

/-- The phase curve associated with a reference configuration. -/
def homotheticPhase (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K)
    (t : ℝ) : Phase :=
  (homotheticConfiguration q K hK t, homotheticVelocity q K hK t)

/-- The derivative of each homothetic position is its prescribed velocity. -/
theorem hasDerivAt_homotheticConfiguration
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) (i : Fin 3) :
    HasDerivAt (fun s => homotheticConfiguration q K hK s i)
      (homotheticVelocity q K hK t i) t := by
  have hscale := hasDerivAt_homotheticScaleFromTime K hK ht
  have hscaled := hscale.smul_const (q i - configurationCentroid q)
  have hcenter := hasDerivAt_const t (configurationCentroid q)
  have hsum := hcenter.add hscaled
  change HasDerivAt ((fun _ : ℝ => configurationCentroid q) +
    (fun s => homotheticScaleFromTime K hK s • (q i - configurationCentroid q)))
    (homotheticScaleRateFromTime K hK t •
      (q i - configurationCentroid q)) t
  have hfun : (fun x : ℝ => configurationCentroid q) +
      (fun s => homotheticScaleFromTime K hK s •
        (q i - configurationCentroid q)) =ᶠ[𝓝 t]
      (fun s => configurationCentroid q +
        homotheticScaleFromTime K hK s • (q i - configurationCentroid q)) := by
    filter_upwards [] with s
    rfl
  have hnew := hsum.congr_of_eventuallyEq hfun
  exact hnew.congr_deriv (by simp)

/-- The derivative of the homothetic velocity is its scalar acceleration
    multiplied by the fixed centered reference position. -/
theorem hasDerivAt_homotheticVelocity
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) (i : Fin 3) :
    HasDerivAt (fun s => homotheticVelocity q K hK s i)
      ((-(2 / K ^ 2) * (homotheticScaleFromTime K hK t ^ 2)⁻¹) •
        (q i - configurationCentroid q)) t := by
  have hrate := hasDerivAt_homotheticScaleRateFromTime K hK ht
  simpa [homotheticVelocity] using
    hrate.smul_const (q i - configurationCentroid q)

/-- The homothetic scale starts at one. -/
theorem homotheticScaleFromTime_zero (K : ℝ) (hK : 0 < K) :
    homotheticScaleFromTime K hK 0 = 1 := by
  simp [homotheticScaleFromTime, homotheticScale, homotheticAngleFromTime_zero K hK]

/-- The homothetic scale starts at rest. -/
theorem homotheticScaleRateFromTime_zero (K : ℝ) (hK : 0 < K) :
    homotheticScaleRateFromTime K hK 0 = 0 := by
  simp [homotheticScaleRateFromTime, homotheticAngleFromTime_zero K hK]

/-- The finite right endpoint of the canonical collapse interval. -/
def homotheticCollapseTime (K : ℝ) : ℝ := K * (Real.pi / 4)

/-- The time scale selected by an equilateral reference side length. -/
def equilateralHomotheticTimeScale (d : ℝ) : ℝ :=
  Real.sqrt ((2 / 3) * d ^ 3)

theorem equilateralHomotheticTimeScale_pos {d : ℝ} (hd : 0 < d) :
    0 < equilateralHomotheticTimeScale d := by
  unfold equilateralHomotheticTimeScale
  apply Real.sqrt_pos.2
  positivity

theorem equilateralHomotheticTimeScale_normalized {d : ℝ} (hd : 0 < d) :
    3 * d ^ (-3 : ℤ) = 2 / equilateralHomotheticTimeScale d ^ 2 := by
  have hKpos := equilateralHomotheticTimeScale_pos hd
  have hKsq : equilateralHomotheticTimeScale d ^ 2 = (2 / 3) * d ^ 3 := by
    unfold equilateralHomotheticTimeScale
    rw [Real.sq_sqrt]
    positivity
  have hpow : d ^ (-3 : ℤ) = (d ^ 3)⁻¹ := by
    rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg]
    rfl
  rw [hpow]
  rw [hKsq]
  field_simp [hd.ne']

theorem equilateralHomotheticTimeScale_collapseTime_pos {d : ℝ}
    (hd : 0 < d) : 0 < homotheticCollapseTime
      (equilateralHomotheticTimeScale d) :=
  mul_pos (equilateralHomotheticTimeScale_pos hd) (by positivity)

theorem homotheticTimeParameter_right_eq_collapseTime (K : ℝ) :
    homotheticTimeParameter K (Real.pi / 2) = homotheticCollapseTime K := by
  unfold homotheticTimeParameter homotheticCollapseTime
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  ring

/-- The inverse angle reaches the terminal value `π/2` at the finite
    collapse time. -/
theorem homotheticAngleFromTime_collapseTime (K : ℝ) (hK : 0 < K) :
    homotheticAngleFromTime K hK (homotheticCollapseTime K) = Real.pi / 2 := by
  have hend := homotheticTimeParameter_left_lt_zero_right K hK
  rw [← homotheticTimeParameter_right_eq_collapseTime K]
  have htime := homotheticTimeParameter_angleFromTime K hK
      (homotheticTimeParameter K (Real.pi / 2))
      ⟨le_of_lt (lt_trans hend.1 hend.2), le_rfl⟩
  have hθmem : homotheticAngleFromTime K hK
      (homotheticTimeParameter K (Real.pi / 2)) ∈
      Set.Icc (-(Real.pi / 4)) (Real.pi / 2) := by
    unfold homotheticAngleFromTime
    exact ((homotheticTimeHomeomorph K hK).symm
      (Set.projIcc
        (homotheticTimeParameter K (-(Real.pi / 4)))
        (homotheticTimeParameter K (Real.pi / 2))
        (le_of_lt (lt_trans hend.1 hend.2))
        (homotheticTimeParameter K (Real.pi / 2)))).property
  have hendpoint : (Real.pi / 2 : ℝ) ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hinj := (homotheticTimeHomeomorph K hK).injective
  have hsub : (⟨homotheticAngleFromTime K hK
      (homotheticTimeParameter K (Real.pi / 2)), hθmem⟩ :
      Set.Icc (-(Real.pi / 4)) (Real.pi / 2)) = ⟨Real.pi / 2, hendpoint⟩ := by
    apply hinj
    apply Subtype.ext
    change homotheticTimeParameter K
      (homotheticAngleFromTime K hK (homotheticTimeParameter K (Real.pi / 2))) =
        homotheticTimeParameter K (Real.pi / 2)
    exact htime
  exact congrArg (fun x : Set.Icc (-(Real.pi / 4)) (Real.pi / 2) => (x : ℝ)) hsub

/-- The scale vanishes at the terminal triple-collision time. -/
theorem homotheticScaleFromTime_collapseTime (K : ℝ) (hK : 0 < K) :
    homotheticScaleFromTime K hK (homotheticCollapseTime K) = 0 := by
  simp [homotheticScaleFromTime, homotheticScale,
    homotheticAngleFromTime_collapseTime K hK]

/-- The scalar scale tends to zero at its finite right endpoint. -/
theorem tendsto_homotheticScaleFromTime_collapseTime
    (K : ℝ) (hK : 0 < K) :
    Tendsto (homotheticScaleFromTime K hK)
      (𝓝 (homotheticCollapseTime K)) (𝓝 0) := by
  have hcont : Continuous (homotheticScaleFromTime K hK) := by
    change Continuous (fun t => Real.cos (homotheticAngleFromTime K hK t) *
      Real.cos (homotheticAngleFromTime K hK t))
    exact (Real.continuous_cos.comp (continuous_homotheticAngleFromTime K hK)).mul
      (Real.continuous_cos.comp (continuous_homotheticAngleFromTime K hK))
  have hlim := hcont.continuousAt.tendsto
    (x := homotheticCollapseTime K)
  simpa [homotheticScaleFromTime_collapseTime K hK] using hlim

/-- Pairwise distances scale by the positive homothety factor. -/
theorem homotheticConfiguration_dist
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) (i j : Fin 3) :
    dist (homotheticConfiguration q K hK t i)
      (homotheticConfiguration q K hK t j) =
        homotheticScaleFromTime K hK t * dist (q i) (q j) := by
  rw [dist_eq_norm, dist_eq_norm]
  have hvec : homotheticConfiguration q K hK t i -
      homotheticConfiguration q K hK t j =
      homotheticScaleFromTime K hK t • (q i - q j) := by
    simp [homotheticConfiguration]
    module
  rw [hvec, norm_smul, Real.norm_eq_abs,
    abs_of_pos (homotheticScaleFromTime_pos K hK ht)]

/-- The homothety preserves the centroid. -/
theorem configurationCentroid_homotheticConfiguration
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) (t : ℝ) :
    configurationCentroid (homotheticConfiguration q K hK t) =
      configurationCentroid q := by
  ext k
  simp [configurationCentroid, homotheticConfiguration]
  ring

/-- Every body tends to the common centroid at the terminal collapse time. -/
theorem tendsto_homotheticConfiguration_collapseTime
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) (i : Fin 3) :
    Tendsto (fun t => homotheticConfiguration q K hK t i)
      (𝓝 (homotheticCollapseTime K)) (𝓝 (configurationCentroid q)) := by
  have hscale := tendsto_homotheticScaleFromTime_collapseTime K hK
  have hdisp := hscale.smul_const (q i - configurationCentroid q)
  have hcenter : Tendsto (fun _ : ℝ => configurationCentroid q)
      (𝓝 (homotheticCollapseTime K)) (𝓝 (configurationCentroid q)) := tendsto_const_nhds
  have hsum := hcenter.add hdisp
  simpa [homotheticConfiguration] using hsum

/-- A homothety by the positive scale remains collision-free on the open
    pre-collapse interval whenever its reference configuration is collision-free. -/
theorem homotheticConfiguration_collisionFree
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2)))
    (hq : CollisionFree q) :
    CollisionFree (homotheticConfiguration q K hK t) := by
  rw [collisionFree_iff_dist_pos]
  intro i j hij
  rw [homotheticConfiguration_dist q K hK ht i j]
  exact mul_pos (homotheticScaleFromTime_pos K hK ht)
    (dist_pos.mpr (hq i j hij))

/-- The homothetic positions agree with the reference configuration at time zero. -/
theorem homotheticConfiguration_zero
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) (i : Fin 3) :
    homotheticConfiguration q K hK 0 i = q i := by
  simp [homotheticConfiguration, homotheticScaleFromTime_zero K hK]

/-- The homothetic velocity vanishes at time zero. -/
theorem homotheticVelocity_zero
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) (i : Fin 3) :
    homotheticVelocity q K hK 0 i = 0 := by
  simp [homotheticVelocity, homotheticScaleRateFromTime_zero K hK]

/-- The phase derivative along the homothetic ansatz is the pair consisting
    of its velocity and its explicitly computed scalar acceleration. -/
theorem hasDerivAt_homotheticPhase
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2))) :
    HasDerivAt (homotheticPhase q K hK)
      (homotheticVelocity q K hK t,
        fun i => (-(2 / K ^ 2) * (homotheticScaleFromTime K hK t ^ 2)⁻¹) •
          (q i - configurationCentroid q)) t := by
  have hpos : HasDerivAt (fun s => homotheticConfiguration q K hK s)
      (homotheticVelocity q K hK t) t := by
    apply (hasDerivAt_pi).2
    intro i
    exact hasDerivAt_homotheticConfiguration q K hK ht i
  have hvel : HasDerivAt (fun s => homotheticVelocity q K hK s)
      (fun i => (-(2 / K ^ 2) *
        (homotheticScaleFromTime K hK t ^ 2)⁻¹) •
          (q i - configurationCentroid q)) t := by
    apply (hasDerivAt_pi).2
    intro i
    exact hasDerivAt_homotheticVelocity q K hK ht i
  change HasDerivAt (fun s =>
    (homotheticConfiguration q K hK s, homotheticVelocity q K hK s))
    (homotheticVelocity q K hK t,
      fun i => (-(2 / K ^ 2) * (homotheticScaleFromTime K hK t ^ 2)⁻¹) •
        (q i - configurationCentroid q)) t
  exact hpos.prodMk hvel

/-- In an equilateral configuration, the equal-mass Newton acceleration is
    a negative scalar multiple of the displacement from the centroid.
    This is the central-configuration identity needed for the X02 homothety. -/
theorem unitAcceleration_equilateral_eq_centroid
    (q : Fin 3 → Point) (d : ℝ)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d)
    (i : Fin 3) :
    unitAcceleration q i =
      (-(3 * d ^ (-3 : ℤ))) • (q i - configurationCentroid q) := by
  have hd : ∀ i j : Fin 3, i ≠ j → dist (q i) (q j) = d := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (False.elim (hij rfl))
    · exact h01
    · exact h02
    · rw [dist_comm]
      exact h01
    · exact (False.elim (hij rfl))
    · exact h12
    · rw [dist_comm]
      exact h02
    · rw [dist_comm]
      exact h12
    · exact (False.elim (hij rfl))
  have hforce : ∀ i : Fin 3,
      unitAcceleration q i =
        d ^ (-3 : ℤ) •
          ((q (cyclicPrev i) - q i) + (q (cyclicNext i) - q i)) := by
    intro i
    fin_cases i <;>
      simp [unitAcceleration, inverseCubeDistance, cyclicPrev, cyclicNext,
        hd] <;> module
  rw [hforce i]
  fin_cases i <;>
    ext k <;> fin_cases k <;>
      simp [configurationCentroid, cyclicPrev, cyclicNext] <;> ring

/-- On an equilateral reference configuration, the homothetic acceleration
    equals the Newton force whenever the time scale is normalized by the
    central-configuration coefficient. -/
theorem unitAcceleration_homotheticConfiguration
    (q : Fin 3 → Point) (d K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2)))
    (hd : 0 < d)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d)
    (hscale : 3 * d ^ (-3 : ℤ) = 2 / K ^ 2) (i : Fin 3) :
    unitAcceleration (homotheticConfiguration q K hK t) i =
      (-(2 / K ^ 2) * (homotheticScaleFromTime K hK t ^ 2)⁻¹) •
        (q i - configurationCentroid q) := by
  let scale := homotheticScaleFromTime K hK t
  have hscale_pos : 0 < scale := homotheticScaleFromTime_pos K hK ht
  have h01' : dist (homotheticConfiguration q K hK t 0)
      (homotheticConfiguration q K hK t 1) = scale * d := by
    rw [homotheticConfiguration_dist q K hK ht, h01]
  have h02' : dist (homotheticConfiguration q K hK t 0)
      (homotheticConfiguration q K hK t 2) = scale * d := by
    rw [homotheticConfiguration_dist q K hK ht, h02]
  have h12' : dist (homotheticConfiguration q K hK t 1)
      (homotheticConfiguration q K hK t 2) = scale * d := by
    rw [homotheticConfiguration_dist q K hK ht, h12]
  have hforce := unitAcceleration_equilateral_eq_centroid
    (homotheticConfiguration q K hK t) (scale * d) h01' h02' h12' i
  rw [configurationCentroid_homotheticConfiguration] at hforce
  have hdisp : homotheticConfiguration q K hK t i - configurationCentroid q =
      scale • (q i - configurationCentroid q) := by
    simp [homotheticConfiguration, scale]
  rw [hforce, hdisp, smul_smul]
  have hdne : d ≠ 0 := ne_of_gt hd
  have hscalene : scale ≠ 0 := ne_of_gt hscale_pos
  have hscale' : 3 / d ^ 3 = 2 / K ^ 2 := by
    exact hscale
  have hscale'' : 3 * K ^ 2 = 2 * d ^ 3 := by
    field_simp [hdne, hK.ne'] at hscale'
    nlinarith [hscale']
  have hcoef : -(3 * (scale * d) ^ (-3 : ℤ)) * scale =
      -(2 / K ^ 2) * (scale ^ 2)⁻¹ := by
    simp [zpow_neg]
    field_simp [hdne, hscalene, hK.ne']
    nlinarith [hscale'']
  rw [hcoef]

/-- Homothety multiplies signed double area by the square of its scale. -/
theorem signedDoubleArea_homotheticConfiguration
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) (t : ℝ) :
    signedDoubleArea (homotheticConfiguration q K hK t) =
      homotheticScaleFromTime K hK t ^ 2 * signedDoubleArea q := by
  let scaleFactor := homotheticScaleFromTime K hK t
  have h01 : homotheticConfiguration q K hK t 1 -
      homotheticConfiguration q K hK t 0 = scaleFactor • (q 1 - q 0) := by
    simp [homotheticConfiguration, scaleFactor]
    module
  have h02 : homotheticConfiguration q K hK t 2 -
      homotheticConfiguration q K hK t 0 = scaleFactor • (q 2 - q 0) := by
    simp [homotheticConfiguration, scaleFactor]
    module
  rw [signedDoubleArea, h01, h02, cross]
  simp [signedDoubleArea, cross, scaleFactor]
  ring_nf

/-- An initially noncollinear equilateral homothetic drop stays noncollinear
    at every regular time before its triple-collision endpoint. -/
theorem signedDoubleArea_ne_zero_homotheticConfiguration
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Ioo
      (homotheticTimeParameter K (-(Real.pi / 4)))
      (homotheticTimeParameter K (Real.pi / 2)))
    (harea : signedDoubleArea q ≠ 0) :
    signedDoubleArea (homotheticConfiguration q K hK t) ≠ 0 := by
  rw [signedDoubleArea_homotheticConfiguration]
  have hscale : 0 < homotheticScaleFromTime K hK t :=
    homotheticScaleFromTime_pos K hK ht
  exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hscale)) harea
/-- Three positive equal side lengths characterize a collision-free
    equilateral reference configuration. -/
theorem collisionFree_of_equilateral
    (q : Fin 3 → Point) (d : ℝ) (hd : 0 < d)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d) : CollisionFree q := by
  rw [collisionFree_iff_dist_pos]
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (False.elim (hij rfl))
  · change 0 < dist (q 0) (q 1)
    rw [h01]
    exact hd
  · change 0 < dist (q 0) (q 2)
    rw [h02]
    exact hd
  · change 0 < dist (q 1) (q 0)
    rw [dist_comm, h01]
    exact hd
  · exact (False.elim (hij rfl))
  · change 0 < dist (q 1) (q 2)
    rw [h12]
    exact hd
  · change 0 < dist (q 2) (q 0)
    rw [dist_comm, h02]
    exact hd
  · change 0 < dist (q 2) (q 1)
    rw [dist_comm, h12]
    exact hd
  · exact (False.elim (hij rfl))

/-- The inverse-angle time interval containing the rest time. -/
def homotheticSolutionInterval (K : ℝ) : Set ℝ :=
  Set.Ioo (homotheticTimeParameter K (-(Real.pi / 4)))
    (homotheticTimeParameter K (Real.pi / 2))

/-- The homothetic ansatz is an actual classical collision-free Newton
    solution on the open interval from a negative time through the finite
    triple-collision endpoint, with the endpoint itself excluded. -/
theorem classicalNewtonSolution_homothetic_equilateral
    (q : Fin 3 → Point) (d K : ℝ) (hK : 0 < K) (hd : 0 < d)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d)
    (hscale : 3 * d ^ (-3 : ℤ) = 2 / K ^ 2) :
    ClassicalNewtonSolution (homotheticPhase q K hK)
      (homotheticSolutionInterval K) := by
  constructor
  · exact isOpen_Ioo
  · intro t ht
    have hI := homotheticTimeParameter_left_lt_zero_right K hK
    have ht' : t ∈ Set.Ioo
        (homotheticTimeParameter K (-(Real.pi / 4)))
        (homotheticTimeParameter K (Real.pi / 2)) := ht
    constructor
    · exact homotheticConfiguration_collisionFree q K hK ht'
        (collisionFree_of_equilateral q d hd h01 h02 h12)
    · have hderiv := hasDerivAt_homotheticPhase q K hK ht'
      have hfield : unitNewtonField (homotheticPhase q K hK t) =
          (homotheticVelocity q K hK t,
            fun i => (-(2 / K ^ 2) *
              (homotheticScaleFromTime K hK t ^ 2)⁻¹) •
                (q i - configurationCentroid q)) := by
        apply Prod.ext
        · rfl
        · funext i
          exact unitAcceleration_homotheticConfiguration q d K hK ht' hd
            h01 h02 h12 hscale i
      rw [hfield]
      exact hderiv

/-- At time zero the constructed solution is the prescribed equal-mass
    equilateral configuration with zero velocity. -/
theorem homotheticPhase_zero
    (q : Fin 3 → Point) (K : ℝ) (hK : 0 < K) :
    homotheticPhase q K hK 0 = (q, fun _ => (0 : Point)) := by
  apply Prod.ext
  · funext i
    exact homotheticConfiguration_zero q K hK i
  · funext i
    exact homotheticVelocity_zero q K hK i

/-- For every positive equilateral side length, there is an explicit
    classical Newton trajectory from the equal-mass rest data up to a finite triple
    collision. -/
theorem exists_homothetic_equilateral_drop
    (q : Fin 3 → Point) (d : ℝ) (hd : 0 < d)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d) :
    ∃ K : ℝ, ∃ hK : 0 < K,
      ClassicalNewtonSolution (homotheticPhase q K hK)
        (homotheticSolutionInterval K) ∧
      homotheticPhase q K hK 0 = (q, fun _ => (0 : Point)) ∧
      0 < homotheticCollapseTime K ∧
      ∀ i : Fin 3,
        Tendsto (fun t => homotheticConfiguration q K hK t i)
          (𝓝 (homotheticCollapseTime K)) (𝓝 (configurationCentroid q)) := by
  let K := equilateralHomotheticTimeScale d
  have hK : 0 < K := by
    exact equilateralHomotheticTimeScale_pos hd
  refine ⟨K, hK, ?_, ?_, ?_, ?_⟩
  · exact classicalNewtonSolution_homothetic_equilateral q d K hK hd
      h01 h02 h12 (equilateralHomotheticTimeScale_normalized hd)
  · exact homotheticPhase_zero q K hK
  · exact equilateralHomotheticTimeScale_collapseTime_pos hd
  · intro i
    exact tendsto_homotheticConfiguration_collapseTime q K hK i

end

end DroppingThreeBodies
