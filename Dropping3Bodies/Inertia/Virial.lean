module

public import Dropping3Bodies.Dynamics.GeneralEnergy
public import Dropping3Bodies.Inertia.CenterOfMassMoment
public import Mathlib.Tactic

@[expose] public section

namespace DroppingThreeBodies

noncomputable section

open scoped Topology RealInnerProductSpace

/-- If a real function vanishes at a point and has strictly negative
    derivative there, it is negative on a sufficiently short interval to the
    right. -/
theorem exists_rightInterval_neg_of_hasDerivAt_neg
    {f : ℝ → ℝ} {a d : ℝ} (hf : f a = 0)
    (hderiv : HasDerivAt f d a) (hd : d < 0) :
    ∃ ε > 0, ∀ x, a < x → x < a + ε → f x < 0 := by
  have hslope : ∀ᶠ x in nhdsWithin a {a}ᶜ, slope f a x < 0 :=
    hderiv.tendsto_slope.eventually (Iio_mem_nhds hd)
  obtain ⟨u, hu, huNeg⟩ := hslope.exists_mem
  obtain ⟨v, hv, hvSub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨ε, hε, ?_⟩
  intro x hax hxa
  have hxball : x ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hxne : x ≠ a := ne_of_gt hax
  have hxu : x ∈ u := hvSub ⟨hball hxball, hxne⟩
  have hslope' := huNeg x hxu
  rw [slope_def_field, hf, div_lt_iff₀ (by linarith : 0 < x - a)] at hslope'
  linarith

/-- The product-rule derivative of `massMomentRate`, kept in the exact inner
    product order delivered by `HasDerivAt.inner`. -/
def massMomentRateDerivative (m : Fin 3 → ℝ) (q v v' a : Fin 3 → Point) : ℝ :=
  m 0 * (2 * (inner ℝ (q 0) (a 0) + inner ℝ (v' 0) (v 0))) +
    (m 1 * (2 * (inner ℝ (q 1) (a 1) + inner ℝ (v' 1) (v 1))) +
      m 2 * (2 * (inner ℝ (q 2) (a 2) + inner ℝ (v' 2) (v 2))))

/-- Differentiate the mass-moment rate when position and velocity have
    derivatives `v'` and `a`. -/
theorem hasDerivAt_massMomentRate
    (m : Fin 3 → ℝ) {q v : Fin 3 → ℝ → Point}
    {v' a : Fin 3 → Point} {t : ℝ}
    (hq : ∀ i, HasDerivAt (fun s => q i s) (v' i) t)
    (hv : ∀ i, HasDerivAt (fun s => v i s) (a i) t) :
    HasDerivAt (fun s => massMomentRate m q (fun i => v i s) s)
      (massMomentRateDerivative m (fun i => q i t) (fun i => v i t) v' a) t := by
  have h0 : HasDerivAt (fun s => m 0 *
      (2 * inner ℝ (q 0 s) (v 0 s)))
      (m 0 * (2 * (inner ℝ (q 0 t) (a 0) + inner ℝ (v' 0) (v 0 t)))) t := by
    have h := HasDerivAt.inner ℝ (hq 0) (hv 0)
    exact (HasDerivAt.const_mul 2 h).const_mul (m 0)
  have h1 : HasDerivAt (fun s => m 1 *
      (2 * inner ℝ (q 1 s) (v 1 s)))
      (m 1 * (2 * (inner ℝ (q 1 t) (a 1) + inner ℝ (v' 1) (v 1 t)))) t := by
    have h := HasDerivAt.inner ℝ (hq 1) (hv 1)
    exact (HasDerivAt.const_mul 2 h).const_mul (m 1)
  have h2 : HasDerivAt (fun s => m 2 *
      (2 * inner ℝ (q 2 s) (v 2 s)))
      (m 2 * (2 * (inner ℝ (q 2 t) (a 2) + inner ℝ (v' 2) (v 2 t)))) t := by
    have h := HasDerivAt.inner ℝ (hq 2) (hv 2)
    exact (HasDerivAt.const_mul 2 h).const_mul (m 2)
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : (fun s => massMomentRate m q (fun i => v i s) s) =ᶠ[𝓝 t]
      (fun s => m 0 * (2 * inner ℝ (q 0 s) (v 0 s)) +
        (m 1 * (2 * inner ℝ (q 1 s) (v 1 s)) +
          m 2 * (2 * inner ℝ (q 2 s) (v 2 s)))) := by
    filter_upwards [] with s
    simp [massMomentRate, Fin.sum_univ_succ]
  simpa [massMomentRateDerivative] using hs.congr_of_eventuallyEq hfun

/-- Along a classical general-mass Newton solution, the derivative of the
    mass-moment derivative exists and is given by the usual kinetic-plus-force
    expression. This is a curve-level second-derivative adapter; no sign or
    initial-rest condition is assumed. -/
theorem generalNewton_massMomentCurve_secondDerivative
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I) :
    HasDerivAt
      (fun s => deriv (massMomentCurve m (fun i τ => (z τ).1 i)) s)
      (massMomentRateDerivative m (fun i => (z t).1 i)
        (fun i => (z t).2 i) (fun i => (z t).2 i)
        (fun i => generalAcceleration G m (z t).1 i)) t := by
  let q : Fin 3 → ℝ → Point := fun i s => (z s).1 i
  let v : Fin 3 → ℝ → Point := fun i s => (z s).2 i
  have hq : ∀ i, HasDerivAt (fun s => q i s) ((z t).2 i) t := by
    intro i
    simpa [q] using (generalNewton_body_vector_derivatives i hsol ht).1
  have hv : ∀ i, HasDerivAt (fun s => v i s)
      (generalAcceleration G m (z t).1 i) t := by
    intro i
    simpa [v] using (generalNewton_body_vector_derivatives i hsol ht).2
  have hrate := hasDerivAt_massMomentRate m hq hv
  have hnear :
      (fun s => deriv (massMomentCurve m q) s) =ᶠ[𝓝 t]
        (fun s => massMomentRate m q (fun i => (z s).2 i) s) := by
    filter_upwards [hsol.1.mem_nhds ht] with s hs
    have hqs : ∀ i, HasDerivAt (fun u => q i u) ((z s).2 i) s := by
      intro i
      simpa [q] using (generalNewton_body_vector_derivatives i hsol hs).1
    have hfirst := hasDerivAt_massMomentCurve m hqs
    simpa [q] using hfirst.deriv
  simpa [q, v] using hrate.congr_of_eventuallyEq hnear

/-- At zero velocity, the second derivative formula reduces to twice the
    weighted position/acceleration pairing. -/
theorem massMomentRateDerivative_eq_two_weightedPositionAcceleration_of_rest
    (m : Fin 3 → ℝ) (q v v' a : Fin 3 → Point)
    (hv : ∀ i, v i = 0) (hv' : ∀ i, v' i = 0) :
    massMomentRateDerivative m q v v' a =
      2 * ∑ i : Fin 3, m i * inner ℝ (q i) (a i) := by
  simp [massMomentRateDerivative, hv, hv', Fin.sum_univ_succ]
  ring

/-- Along the diagonal position/velocity pair, the derivative of the positive
    Newtonian potential is its negative value. This is the configuration-level
    Newtonian virial identity. -/
theorem generalPotentialRate_self_eq_negPotential
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (h01 : q 0 ≠ q 1) (h02 : q 0 ≠ q 2) (h12 : q 1 ≠ q 2) :
    generalPotentialRate G m q q = - generalGravitationalPotential G m q := by
  have hd01 : dist (q 0) (q 1) ≠ 0 := (dist_pos.mpr h01).ne'
  have hd02 : dist (q 0) (q 2) ≠ 0 := (dist_pos.mpr h02).ne'
  have hd12 : dist (q 1) (q 2) ≠ 0 := (dist_pos.mpr h12).ne'
  have hi01 : inner ℝ (q 0 - q 1) (q 0 - q 1) = dist (q 0) (q 1) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  have hi02 : inner ℝ (q 0 - q 2) (q 0 - q 2) = dist (q 0) (q 2) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  have hi12 : inner ℝ (q 1 - q 2) (q 1 - q 2) = dist (q 1) (q 2) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  unfold generalPotentialRate generalGravitationalPotential inverseCubeDistance
  rw [hi01, hi02, hi12]
  simp only [zpow_neg, zpow_ofNat]
  field_simp [hd01, hd02, hd12]
  ring

/-- The mass-weighted position/acceleration pairing is the negative of the
    positive gravitational potential magnitude. This follows by grouping the
    six directed forces into three unordered pairs. -/
theorem generalNewton_weighted_position_acceleration_eq_negPotential
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (h01 : q 0 ≠ q 1) (h02 : q 0 ≠ q 2) (h12 : q 1 ≠ q 2) :
    (∑ i : Fin 3, m i * inner ℝ (q i) (generalAcceleration G m q i)) =
      - generalGravitationalPotential G m q := by
  rw [generalNewton_weighted_work_eq_potentialRate G m q q,
    generalPotentialRate_self_eq_negPotential G m q h01 h02 h12]

/-- For positive masses and positive G, the weighted position/acceleration
    pairing is strictly negative at every collision-free configuration. -/
theorem generalNewton_weighted_position_acceleration_neg
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hG : 0 < G) (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (h01 : q 0 ≠ q 1) (h02 : q 0 ≠ q 2) (h12 : q 1 ≠ q 2) :
    (∑ i : Fin 3, m i * inner ℝ (q i) (generalAcceleration G m q i)) < 0 := by
  rw [generalNewton_weighted_position_acceleration_eq_negPotential
    G m q h01 h02 h12]
  have hd01 : 0 < dist (q 0) (q 1) := dist_pos.mpr h01
  have hd02 : 0 < dist (q 0) (q 2) := dist_pos.mpr h02
  have hd12 : 0 < dist (q 1) (q 2) := dist_pos.mpr h12
  have hpot : 0 < generalGravitationalPotential G m q := by
    unfold generalGravitationalPotential
    positivity
  exact neg_neg_iff_pos.mpr hpot

/-- For a classical general-mass Newton solution starting at rest, the
    second derivative of the mass moment at the initial time equals minus
    twice the positive gravitational potential. This is a local virial
    statement, not a monotonicity theorem for later times. -/
theorem generalNewton_massMomentCurve_secondDerivative_neg_at_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) {a : ℝ} (ha : a ∈ I)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => deriv (massMomentCurve m (fun i τ => (z τ).1 i)) s) a =
      -2 * generalGravitationalPotential G m (z a).1 := by
  have hsec := generalNewton_massMomentCurve_secondDerivative hsol ha
  have hcf := (hsol.2 a ha).1
  have h01 : (z a).1 0 ≠ (z a).1 1 := hcf 0 1 (by decide)
  have h02 : (z a).1 0 ≠ (z a).1 2 := hcf 0 2 (by decide)
  have h12 : (z a).1 1 ≠ (z a).1 2 := hcf 1 2 (by decide)
  have hvirial := generalNewton_weighted_position_acceleration_eq_negPotential
    G m (z a).1 h01 h02 h12
  have hrate := massMomentRateDerivative_eq_two_weightedPositionAcceleration_of_rest
    m (z a).1 (z a).2 (z a).2
      (fun i => generalAcceleration G m (z a).1 i) hrest hrest
  rw [hsec.deriv, hrate, hvirial]
  ring

/-- Along a solution starting at rest, the weighted center of mass is constant;
    hence the physical center-of-mass moment differs from the origin moment by
    a fixed constant. -/
theorem generalNewton_centerOfMassMomentCurve_eq_massMoment_sub_initial_constant
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hrest : ∀ i, (z a).2 i = 0) :
    centerOfMassMomentCurve m (fun i s => (z s).1 i) t =
      massMomentCurve m (fun i s => (z s).1 i) t -
        ‖weightedPosition m (z a).1‖ ^ 2 / totalMass m := by
  have h0 := generalPositionCoordinate_eq_on_of_initial_rest
    hsol hconn ha hrest ht ha (k := (0 : Fin 2))
  have h1 := generalPositionCoordinate_eq_on_of_initial_rest
    hsol hconn ha hrest ht ha (k := (1 : Fin 2))
  have hcenter : weightedPosition m (z t).1 = weightedPosition m (z a).1 := by
    ext k
    fin_cases k
    · simpa [weightedPosition, generalPositionCoordinateCurve] using h0
    · simpa [weightedPosition, generalPositionCoordinateCurve] using h1
  rw [centerOfMassMomentCurve_eq_jacobiMomentCurve m
    (fun i s => (z s).1 i) hm0 hm1 hm2 t]
  change jacobiMoment m (z t).1 = _
  rw [← centerOfMassMoment_eq_jacobiMoment m (z t).1 hm0 hm1 hm2]
  unfold centerOfMassMoment massMomentCurve
  rw [hcenter]

/-- The derivative of the center-of-mass moment derivative along a classical
    solution is given by the same kinetic-plus-force expression as for the
    origin moment. -/
theorem generalNewton_centerOfMassMomentCurve_secondDerivative
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hrest : ∀ i, (z a).2 i = 0) :
    HasDerivAt (fun s => deriv (centerOfMassMomentCurve m
      (fun i τ => (z τ).1 i)) s)
      (massMomentRateDerivative m (fun i => (z a).1 i)
        (fun i => (z a).2 i) (fun i => (z a).2 i)
        (fun i => generalAcceleration G m (z a).1 i)) a := by
  have hsec := generalNewton_massMomentCurve_secondDerivative hsol ha
  let C := ‖weightedPosition m (z a).1‖ ^ 2 / totalMass m
  have hderivEq : ∀ s ∈ I,
      deriv (centerOfMassMomentCurve m (fun i τ => (z τ).1 i)) s =
        deriv (massMomentCurve m (fun i τ => (z τ).1 i)) s := by
    intro s hs
    have hcurve := generalNewton_centerOfMassMomentCurve_eq_massMoment_sub_initial_constant
      hsol hconn ha hs hm0 hm1 hm2 hrest
    have hq : ∀ i, HasDerivAt (fun u => (z u).1 i) ((z s).2 i) s := by
      intro i
      exact (generalNewton_body_vector_derivatives i hsol hs).1
    have hmoment := hasDerivAt_massMomentCurve m hq
    have hlocal : centerOfMassMomentCurve m (fun i τ => (z τ).1 i) =ᶠ[𝓝 s]
        (fun u => massMomentCurve m (fun i τ => (z τ).1 i) u - C) := by
      filter_upwards [hsol.1.mem_nhds hs] with u hu
      exact generalNewton_centerOfMassMomentCurve_eq_massMoment_sub_initial_constant
        hsol hconn ha hu hm0 hm1 hm2 hrest
    have hcm := hmoment.sub_const C |>.congr_of_eventuallyEq hlocal
    rw [hcm.deriv, hmoment.deriv]
  have hnear :
      (fun s => deriv (centerOfMassMomentCurve m
        (fun i τ => (z τ).1 i)) s) =ᶠ[𝓝 a]
        (fun s => deriv (massMomentCurve m (fun i τ => (z τ).1 i)) s) := by
    filter_upwards [hsol.1.mem_nhds ha] with s hs
    exact hderivEq s hs
  have hcmsec := hsec.congr_of_eventuallyEq hnear
  simpa using hcmsec

/-- The physical center-of-mass moment has zero first derivative at an
    initial-rest time. -/
theorem generalNewton_centerOfMassMomentCurve_deriv_eq_zero_at_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (centerOfMassMomentCurve m (fun i τ => (z τ).1 i)) a = 0 := by
  let C := ‖weightedPosition m (z a).1‖ ^ 2 / totalMass m
  have hq : ∀ i, HasDerivAt (fun u => (z u).1 i) ((z a).2 i) a := by
    intro i
    exact (generalNewton_body_vector_derivatives i hsol ha).1
  have hmoment := hasDerivAt_massMomentCurve m hq
  have hlocal : centerOfMassMomentCurve m (fun i τ => (z τ).1 i) =ᶠ[𝓝 a]
      (fun u => massMomentCurve m (fun i τ => (z τ).1 i) u - C) := by
    filter_upwards [hsol.1.mem_nhds ha] with u hu
    exact generalNewton_centerOfMassMomentCurve_eq_massMoment_sub_initial_constant
      hsol hconn ha hu hm0 hm1 hm2 hrest
  have hcm := hmoment.sub_const C |>.congr_of_eventuallyEq hlocal
  rw [hcm.deriv]
  simp [massMomentRate, hrest]

/-- The derivative of the physical center-of-mass moment is strictly negative
    for every sufficiently small time to the right of a rest start. -/
theorem generalNewton_centerOfMassMomentCurve_deriv_neg_right_of_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hrest : ∀ i, (z a).2 i = 0) :
    ∃ ε > 0, ∀ t, a < t → t < a + ε →
      deriv (centerOfMassMomentCurve m (fun i τ => (z τ).1 i)) t < 0 := by
  let F : ℝ → ℝ := centerOfMassMomentCurve m (fun i τ => (z τ).1 i)
  let g : ℝ → ℝ := fun t => deriv F t
  have hsec := generalNewton_centerOfMassMomentCurve_secondDerivative
    hsol hconn ha hm0 hm1 hm2 hrest
  have h0 := generalNewton_centerOfMassMomentCurve_deriv_eq_zero_at_rest
    hsol hconn ha hm0 hm1 hm2 hrest
  have hderiv : HasDerivAt g
      (massMomentRateDerivative m (fun i => (z a).1 i)
        (fun i => (z a).2 i) (fun i => (z a).2 i)
        (fun i => generalAcceleration G m (z a).1 i)) a := by
    simpa [F, g] using hsec
  have hd : massMomentRateDerivative m (fun i => (z a).1 i)
      (fun i => (z a).2 i) (fun i => (z a).2 i)
      (fun i => generalAcceleration G m (z a).1 i) < 0 := by
    have hcf := (hsol.2 a ha).1
    have h01 : (z a).1 0 ≠ (z a).1 1 := hcf 0 1 (by decide)
    have h02 : (z a).1 0 ≠ (z a).1 2 := hcf 0 2 (by decide)
    have h12 : (z a).1 1 ≠ (z a).1 2 := hcf 1 2 (by decide)
    have hforce := generalNewton_weighted_position_acceleration_neg
      G m (z a).1 hG hm0 hm1 hm2 h01 h02 h12
    have hvirial := generalNewton_weighted_position_acceleration_eq_negPotential
      G m (z a).1 h01 h02 h12
    rw [hvirial] at hforce
    have hpot : 0 < generalGravitationalPotential G m (z a).1 := by linarith
    have hrate := massMomentRateDerivative_eq_two_weightedPositionAcceleration_of_rest
      m (z a).1 (z a).2 (z a).2
        (fun i => generalAcceleration G m (z a).1 i) hrest hrest
    rw [hrate, hvirial]
    nlinarith
  have hga : g a = 0 := by simpa [F, g] using h0
  simpa [F, g] using exists_rightInterval_neg_of_hasDerivAt_neg hga hderiv hd

/-- The physical center-of-mass moment is strictly decreasing on some
    nontrivial initial interval to the right of a zero-velocity start. -/
theorem generalNewton_centerOfMassMomentCurve_strictAntiOn_near_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hrest : ∀ i, (z a).2 i = 0) :
    ∃ T, a < T ∧ Set.Icc a T ⊆ I ∧
      StrictAntiOn (centerOfMassMomentCurve m (fun i s => (z s).1 i))
        (Set.Icc a T) := by
  let F : ℝ → ℝ := centerOfMassMomentCurve m (fun i s => (z s).1 i)
  obtain ⟨ε, hε, hFderiv⟩ :=
    generalNewton_centerOfMassMomentCurve_deriv_neg_right_of_rest
      hsol hconn ha hm0 hm1 hm2 hG hrest
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hsol.1.mem_nhds ha)
  let δ : ℝ := min (ε / 2) (r / 2)
  let T : ℝ := a + δ
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδε : δ < ε := by
    dsimp [δ]
    have : 0 < ε / 2 := half_pos hε
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδr : δ < r := by
    dsimp [δ]
    have : 0 < r / 2 := half_pos hr
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have haT : a < T := by dsimp [T]; linarith
  have hIcc : Set.Icc a T ⊆ I := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have htpos : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have htab : t - a ≤ δ := by
      have hupper := ht.2
      dsimp [T] at hupper
      linarith
    rw [abs_of_nonneg htpos]
    linarith
  have hFfield : Continuous (fun p : Phase => centerOfMassMoment m p.1) := by
    have hM : totalMass m ≠ 0 :=
      ne_of_gt (totalMass_pos_of_positive m hm0 hm1 hm2)
    unfold centerOfMassMoment massMoment weightedPosition totalMass
    fun_prop
  have hzcont : ContinuousOn z (Set.Icc a T) := by
    intro t ht
    exact (hsol.2 t (hIcc ht)).2.continuousAt.continuousWithinAt
  have hFcont : ContinuousOn F (Set.Icc a T) := by
    dsimp [F, centerOfMassMomentCurve]
    exact hFfield.continuousOn.comp hzcont (by
      intro t ht
      exact Set.mem_univ (z t))
  have hFanti : StrictAntiOn F (Set.Icc a T) :=
    strictAntiOn_of_deriv_neg (convex_Icc a T) hFcont (by
      intro t ht
      have htInterior : a < t ∧ t < T := by
        simpa [interior_Icc] using ht
      have htaε : t < a + ε := by dsimp [T] at htInterior; linarith
      exact hFderiv t htInterior.1 htaε)
  exact ⟨T, haT, hIcc, by simpa [F] using hFanti⟩

/-- The second derivative of the physical moment about the center of mass at
    an initial-rest time agrees with the origin-moment virial value. -/
theorem generalNewton_centerOfMassMomentCurve_secondDerivative_neg_at_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => deriv (centerOfMassMomentCurve m
      (fun i τ => (z τ).1 i)) s) a =
      -2 * generalGravitationalPotential G m (z a).1 := by
  have hmass := generalNewton_massMomentCurve_secondDerivative_neg_at_rest
    hsol ha hrest
  have hsec := generalNewton_centerOfMassMomentCurve_secondDerivative
    hsol hconn ha hm0 hm1 hm2 hrest
  rw [hsec.deriv]
  exact (generalNewton_massMomentCurve_secondDerivative hsol ha).deriv.symm.trans hmass

/-- With positive masses and gravity, the physical center-of-mass moment has
    strictly negative second derivative at a collision-free rest start. -/
theorem generalNewton_centerOfMassMomentCurve_secondDerivative_lt_zero_at_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => deriv (centerOfMassMomentCurve m
      (fun i τ => (z τ).1 i)) s) a < 0 := by
  rw [generalNewton_centerOfMassMomentCurve_secondDerivative_neg_at_rest
    hsol hconn ha hm0 hm1 hm2 hrest]
  have hcf := (hsol.2 a ha).1
  have h01 : (z a).1 0 ≠ (z a).1 1 := hcf 0 1 (by decide)
  have h02 : (z a).1 0 ≠ (z a).1 2 := hcf 0 2 (by decide)
  have h12 : (z a).1 1 ≠ (z a).1 2 := hcf 1 2 (by decide)
  have hforce := generalNewton_weighted_position_acceleration_neg
    G m (z a).1 hG hm0 hm1 hm2 h01 h02 h12
  have hvirial := generalNewton_weighted_position_acceleration_eq_negPotential
    G m (z a).1 h01 h02 h12
  rw [hvirial] at hforce
  have hpot : 0 < generalGravitationalPotential G m (z a).1 := by linarith
  linarith

end

end DroppingThreeBodies
