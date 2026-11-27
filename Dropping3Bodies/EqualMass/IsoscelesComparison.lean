module

public import Dropping3Bodies.EqualMass.IsoscelesTrajectoryODE
public import Dropping3Bodies.EqualMass.IsoscelesInitialSymmetry
public import Dropping3Bodies.Dynamics.Energy
public import Dropping3Bodies.Support.SecondOrderComparison
public import Mathlib.Tactic

@[expose] public section

/-!
# Pointwise acceleration estimates for the isosceles comparison

This file extracts the differential inequalities needed by the quantitative
high-isosceles collision comparison. It does not yet assert a collision time.
-/

namespace DroppingThreeBodies

noncomputable section

theorem isosceles_inverseCubeDistance_le_inv_height_cube
    (x u v : ℝ) (hx : 0 < x) (hz : 0 < v - u) :
    inverseCubeDistance (isoscelesConfiguration x u v) 0 2 ≤
      ((v - u) ^ 3)⁻¹ := by
  let d := dist (isoscelesConfiguration x u v 0)
    (isoscelesConfiguration x u v 2)
  have hdnonneg : 0 ≤ d := dist_nonneg
  have hdsq := isoscelesConfiguration_leftLeg_dist_sq x u v
  have hsq : (v - u) ^ 2 < d ^ 2 := by
    rw [hdsq]
    nlinarith [sq_pos_of_pos hx]
  have hheight_lt : v - u < d :=
    (sq_lt_sq₀ (le_of_lt hz) hdnonneg).1 hsq
  have hcube : (v - u) ^ 3 ≤ d ^ 3 := by
    have hfactor : 0 < (d - (v - u)) *
        (d ^ 2 + d * (v - u) + (v - u) ^ 2) :=
      mul_pos (sub_pos.mpr hheight_lt) (by positivity)
    nlinarith [hfactor]
  have hinv := one_div_le_one_div_of_le (pow_pos hz 3) hcube
  rw [inverseCubeDistance_eq_inv_distance_cube]
  simpa [d, one_div] using hinv

/-- A point fixed by the isosceles reflection has a collision-free reconstructed
    isosceles configuration whenever the Newton state is collision-free. -/
theorem classicalNewton_isosceles_reconstructed_configuration_collisionFree
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (hSym : isoscelesSymmetryPhase (z t) = z t) :
    CollisionFree (isoscelesConfiguration (isoscelesSolutionX z t)
      (isoscelesSolutionU z t) (isoscelesSolutionV z t)) := by
  have hconfig := isoscelesConfiguration_eq_of_symmetry_fixed (z t).1
    (congrArg Prod.fst hSym)
  have hconfigIso : (z t).1 = isoscelesConfiguration
      (isoscelesSolutionX z t) (isoscelesSolutionU z t)
      (isoscelesSolutionV z t) := by
    simpa [isoscelesSolutionX, isoscelesSolutionU, isoscelesSolutionV] using hconfig
  intro i j hij
  simpa [hconfigIso] using (hsol.2 t ht).1 i j hij

/-- The base-half acceleration is strictly negative on every regular symmetric
    state with positive base half-length. -/
theorem classicalNewton_isosceles_base_half_acceleration_neg
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (hSym : isoscelesSymmetryPhase (z t) = z t)
    (hx : 0 < isoscelesSolutionX z t) :
    deriv (isoscelesSolutionXVelocity z) t < 0 := by
  have hode := classicalNewton_isosceles_scalar_ode hsol ht hSym hx
  have hcf := classicalNewton_isosceles_reconstructed_configuration_collisionFree
    hsol ht hSym
  have hd : 0 < dist
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t) 0)
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t) 2) :=
    dist_pos.mpr (hcf 0 2 (by decide))
  have hk : 0 < inverseCubeDistance
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2 := by
    rw [inverseCubeDistance_eq_inv_distance_cube]
    positivity
  rw [hode.1.deriv]
  have hfirst : 0 < 1 / (4 * (isoscelesSolutionX z t) ^ 2) := by
    positivity
  have hsecond : 0 < isoscelesSolutionX z t * inverseCubeDistance
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2 :=
    mul_pos hx hk
  linarith

/-- Since the base half-length decreases from rest, its acceleration is at
    most `-1/(4*x₀²)` whenever it has not exceeded its initial value. -/
theorem classicalNewton_isosceles_base_second_derivative_le_of_le_initial
    {z : ℝ → Phase} {I : Set ℝ} {t x₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (hSym : isoscelesSymmetryPhase (z t) = z t)
    (hx : 0 < isoscelesSolutionX z t)
    (hxt : isoscelesSolutionX z t ≤ x₀) (hx₀ : 0 < x₀) :
    deriv (isoscelesSolutionXVelocity z) t ≤ -(1 / (4 * x₀ ^ 2)) := by
  have hode := classicalNewton_isosceles_scalar_ode hsol ht hSym hx
  have hxsq : (isoscelesSolutionX z t) ^ 2 ≤ x₀ ^ 2 := by
    have hprod : 0 ≤ (x₀ - isoscelesSolutionX z t) *
        (x₀ + isoscelesSolutionX z t) :=
      mul_nonneg (sub_nonneg.mpr hxt) (le_of_lt (add_pos hx₀ hx))
    nlinarith [hprod]
  have hrecip := one_div_le_one_div_of_le (sq_pos_of_pos hx) hxsq
  have hscaled : 1 / (4 * x₀ ^ 2) ≤ 1 / (4 * (isoscelesSolutionX z t) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hrecip (by norm_num : 0 ≤ (1 / 4 : ℝ))
    simpa [one_div] using hm
  have hcf := classicalNewton_isosceles_reconstructed_configuration_collisionFree
    hsol ht hSym
  have hd : 0 < dist
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t) 0)
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t) 2) :=
    dist_pos.mpr (hcf 0 2 (by decide))
  have hk : 0 < inverseCubeDistance
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2 := by
    rw [inverseCubeDistance_eq_inv_distance_cube]
    positivity
  rw [hode.1.deriv]
  have hforce : 0 ≤ isoscelesSolutionX z t * inverseCubeDistance
      (isoscelesConfiguration (isoscelesSolutionX z t)
        (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2 :=
    le_of_lt (mul_pos hx hk)
  nlinarith [hscaled, hforce]

/-- Positive isosceles height controls the inverse-cube kernel by the vertical
    separation alone. -/
theorem classicalNewton_isosceles_height_second_derivative_ge_of_height_ge_half
    {z : ℝ → Phase} {I : Set ℝ} {t H : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (hSym : isoscelesSymmetryPhase (z t) = z t)
    (hx : 0 < isoscelesSolutionX z t) (hH : 0 < H)
    (hh : H / 2 ≤ isoscelesSolutionZ z t) :
    -(12 / H ^ 2) ≤ deriv (isoscelesSolutionZVelocity z) t := by
  have hode := classicalNewton_isosceles_scalar_ode hsol ht hSym hx
  have hz : 0 < isoscelesSolutionZ z t := by linarith
  have hkBound := isosceles_inverseCubeDistance_le_inv_height_cube
    (isoscelesSolutionX z t) (isoscelesSolutionU z t)
    (isoscelesSolutionV z t) hx (by simpa [isoscelesSolutionZ] using hz)
  have hforce : -(3 / (isoscelesSolutionZ z t) ^ 2) ≤
      -3 * isoscelesSolutionZ z t * inverseCubeDistance
        (isoscelesConfiguration (isoscelesSolutionX z t)
          (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2 := by
    have hmul := mul_le_mul_of_nonneg_left hkBound
      (by positivity : 0 ≤ 3 * isoscelesSolutionZ z t)
    have hEq : 3 * isoscelesSolutionZ z t *
        ((isoscelesSolutionZ z t) ^ 3)⁻¹ =
          3 / (isoscelesSolutionZ z t) ^ 2 := by
      field_simp [ne_of_gt hz]
    have hmul' : 3 * isoscelesSolutionZ z t *
        inverseCubeDistance
          (isoscelesConfiguration (isoscelesSolutionX z t)
            (isoscelesSolutionU z t) (isoscelesSolutionV z t)) 0 2 ≤
        3 * isoscelesSolutionZ z t *
          ((isoscelesSolutionZ z t) ^ 3)⁻¹ := by
      simpa [isoscelesSolutionZ] using hmul
    nlinarith [hmul', hEq]
  have hsq : (H / 2) ^ 2 ≤ (isoscelesSolutionZ z t) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (le_of_lt hz)).2 hh
  have hinv := one_div_le_one_div_of_le (sq_pos_of_pos (by positivity : 0 < H / 2)) hsq
  have hscaled : 3 / (isoscelesSolutionZ z t) ^ 2 ≤ 12 / H ^ 2 := by
    calc
      3 / (isoscelesSolutionZ z t) ^ 2 =
          3 * ((isoscelesSolutionZ z t) ^ 2)⁻¹ := by ring
      _ ≤ 3 * ((H / 2) ^ 2)⁻¹ :=
        by
          have hm := mul_le_mul_of_nonneg_left hinv (by norm_num : 0 ≤ (3 : ℝ))
          simpa [one_div] using hm
      _ = 12 / H ^ 2 := by field_simp [ne_of_gt hH]; ring
  rw [hode.2.deriv]
  linarith

end


/-- Quantitative comparison core: if the base half-length is concave, has the
    stated strong acceleration below its initial value, and a positive height
    starts with zero velocity and the stated lower acceleration, then the two
    coordinates cannot both stay positive to `sqrt (8*x₀^3)` when `H^3` is
    larger than `96*x₀^3`. -/
theorem isosceles_tall_segment_impossible_of_scalar_bounds
    {T x₀ H : ℝ} {x x' x'' h h' h'' : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hH : 0 < H)
    (htall : H ^ 3 > 96 * x₀ ^ 3)
    (hT : T = Real.sqrt (8 * x₀ ^ 3))
    (hxd : ∀ t ∈ Set.Icc 0 T, HasDerivAt x (x' t) t)
    (hx'd : ∀ t ∈ Set.Icc 0 T, HasDerivAt x' (x'' t) t)
    (hhd : ∀ t ∈ Set.Icc 0 T, HasDerivAt h (h' t) t)
    (hh'd : ∀ t ∈ Set.Icc 0 T, HasDerivAt h' (h'' t) t)
    (hconcave : ∀ t ∈ Set.Icc 0 T, x'' t ≤ 0)
    (hforce : ∀ t ∈ Set.Icc 0 T, x t ≤ x₀ → x'' t ≤ -(1 / (4*x₀^2)))
    (hheight : ∀ t ∈ Set.Icc 0 T, H/2 ≤ h t → -(12/H^2) ≤ h'' t)
    (hx0 : x 0 = x₀) (hx'0 : x' 0 = 0)
    (hh0 : h 0 = H) (hh'0 : h' 0 = 0)
    (hxpos : ∀ t ∈ Set.Icc 0 T, 0 < x t) : False := by
  have hTnonneg : 0 ≤ T := by rw [hT]; positivity
  have hC : 0 ≤ 12 / H ^ 2 := by positivity
  have hmargin : H/2 < H - (12/H^2) * T^2 / 2 := by
    have hT2 : T^2 = 8*x₀^3 := by rw [hT, Real.sq_sqrt (by positivity)]
    rw [hT2]
    field_simp [ne_of_gt hH]
    nlinarith [htall]
  have hmargin' : H / 2 < h 0 - (12 / H ^ 2) * T ^ 2 / 2 := by
    rw [hh0]
    exact hmargin
  have hbar := lower_barrier_preserved_of_second_deriv_bound
    hTnonneg hhd hh'd hC hheight (by rw [hh0]; linarith) hh'0 hmargin'
  exact no_positive_segment_to_sqrt_eight_scale hx₀ hT hxd hx'd
    hconcave hforce hx0 hx'0 hxpos

/-- The scalar comparison applies to an actual equal-mass Newton solution
    from a sufficiently tall isosceles rest start, as long as the solution is
    defined and has positive base half-length throughout the comparison
    interval. Symmetry is supplied by uniqueness on the connected domain. -/
theorem classicalNewton_isosceles_tall_rest_segment_impossible
    {z : ℝ → Phase} {I : Set ℝ} {T x₀ u₀ v₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    (hzero : (0 : ℝ) ∈ I)
    (hstart : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)))
    (hsegment : Set.Icc 0 T ⊆ I)
    (hx : ∀ t ∈ Set.Icc 0 T, 0 < isoscelesSolutionX z t)
    (hx₀ : 0 < x₀) (hH : 0 < v₀ - u₀)
    (htall : (v₀ - u₀) ^ 3 > 96 * x₀ ^ 3)
    (hT : T = Real.sqrt (8 * x₀ ^ 3)) : False := by
  let H := v₀ - u₀
  have hH' : 0 < H := hH
  have htall' : H ^ 3 > 96 * x₀ ^ 3 := by simpa [H] using htall
  have hfixed : isoscelesSymmetryPhase (z 0) = z 0 := by
    rw [hstart]
    exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
  have hSym : ∀ t ∈ Set.Icc 0 T, isoscelesSymmetryPhase (z t) = z t := by
    intro t ht
    exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
      hfixed t (hsegment ht)
  have hX0 : isoscelesSolutionX z 0 = x₀ := by
    simp [isoscelesSolutionX, hstart, isoscelesConfiguration, pointXY]
  have hXvel0 : isoscelesSolutionXVelocity z 0 = 0 := by
    simp [isoscelesSolutionXVelocity, hstart]
  have hZ0 : isoscelesSolutionZ z 0 = H := by
    simp [H, isoscelesSolutionZ, isoscelesSolutionV,
      isoscelesSolutionU, hstart, isoscelesConfiguration, pointXY]
  have hZvel0 : isoscelesSolutionZVelocity z 0 = 0 := by
    simp [isoscelesSolutionZVelocity, hstart]
  have hXderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionX z)
        (isoscelesSolutionXVelocity z t) t := by
    intro t ht
    exact hasDerivAt_isoscelesSolutionX hsol (hsegment ht)
  have hZderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionZ z)
        (isoscelesSolutionZVelocity z t) t := by
    intro t ht
    exact hasDerivAt_isoscelesSolutionZ hsol (hsegment ht)
  have hXacc : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionXVelocity z)
        (deriv (isoscelesSolutionXVelocity z) t) t := by
    intro t ht
    have hode := classicalNewton_isosceles_scalar_ode hsol (hsegment ht)
      (hSym t ht) (hx t ht)
    simpa only [← hode.1.deriv] using hode.1
  have hZacc : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionZVelocity z)
        (deriv (isoscelesSolutionZVelocity z) t) t := by
    intro t ht
    have hode := classicalNewton_isosceles_scalar_ode hsol (hsegment ht)
      (hSym t ht) (hx t ht)
    simpa only [← hode.2.deriv] using hode.2
  have hconcave : ∀ t ∈ Set.Icc 0 T,
      deriv (isoscelesSolutionXVelocity z) t ≤ 0 := by
    intro t ht
    exact le_of_lt (classicalNewton_isosceles_base_half_acceleration_neg
      hsol (hsegment ht) (hSym t ht) (hx t ht))
  have hforce : ∀ t ∈ Set.Icc 0 T,
      isoscelesSolutionX z t ≤ x₀ →
        deriv (isoscelesSolutionXVelocity z) t ≤ -(1 / (4*x₀^2)) := by
    intro t ht hxt
    exact classicalNewton_isosceles_base_second_derivative_le_of_le_initial
      hsol (hsegment ht) (hSym t ht) (hx t ht) hxt hx₀
  have hheight : ∀ t ∈ Set.Icc 0 T,
      H/2 ≤ isoscelesSolutionZ z t →
        -(12/H^2) ≤ deriv (isoscelesSolutionZVelocity z) t := by
    intro t ht hh
    exact classicalNewton_isosceles_height_second_derivative_ge_of_height_ge_half
      hsol (hsegment ht) (hSym t ht) (hx t ht) hH' hh
  exact isosceles_tall_segment_impossible_of_scalar_bounds
    hx₀ hH' htall' hT hXderiv hXacc hZderiv hZacc hconcave hforce
    hheight hX0 hXvel0 hZ0 hZvel0 hx

/-- On a symmetric collision-free interval, the reconstructed base half-length
    cannot change sign. If it starts positive, continuity and the noncollision
    of the base pair keep it positive throughout. -/
theorem classicalNewton_isosceles_base_half_positive_on_segment
    {z : ℝ → Phase} {I : Set ℝ} {T x₀ u₀ v₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I)
    (hstart : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)))
    (hsegment : Set.Icc 0 T ⊆ I)
    (hSym : ∀ t ∈ Set.Icc 0 T, isoscelesSymmetryPhase (z t) = z t)
    (hx₀ : 0 < x₀) :
    ∀ t ∈ Set.Icc 0 T, 0 < isoscelesSolutionX z t := by
  intro t ht
  let X : ℝ → ℝ := isoscelesSolutionX z
  have hXcont : ContinuousOn X (Set.Icc 0 t) := by
    intro s hs
    have hderiv := hasDerivAt_isoscelesSolutionX hsol (hsegment ⟨hs.1,
      le_trans hs.2 ht.2⟩)
    exact hderiv.continuousAt.continuousWithinAt
  have hX0 : X 0 = x₀ := by
    simp [X, isoscelesSolutionX, hstart, isoscelesConfiguration, pointXY]
  have hXnonzero : ∀ s ∈ Set.Icc 0 t, X s ≠ 0 := by
    intro s hs hzero
    have hcf := classicalNewton_isosceles_reconstructed_configuration_collisionFree
      hsol (hsegment ⟨hs.1, le_trans hs.2 ht.2⟩) (hSym s ⟨hs.1, le_trans hs.2 ht.2⟩)
    have hdist := hcf 0 1 (by decide)
    apply hdist
    simp [X, isoscelesConfiguration, pointXY, hzero]
  by_contra hnotpos
  have hXt : X t ≤ 0 := not_lt.mp hnotpos
  have hzeroImage : (0 : ℝ) ∈ X '' Set.Icc 0 t := by
    apply (intermediate_value_Icc' ht.1 hXcont)
    exact ⟨hXt, le_of_lt (by rw [hX0]; exact hx₀)⟩
  rcases hzeroImage with ⟨s, hs, hXs⟩
  exact hXnonzero s hs hXs

/-- On every shorter regular segment of a sufficiently tall isosceles rest
    trajectory, the base half-length stays at most its initial value and the
    vertical separation stays strictly above half its initial value. -/
theorem classicalNewton_isosceles_tall_coordinate_bounds_on_segment
    {z : ℝ → Phase} {I : Set ℝ} {T x₀ u₀ v₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I)
    (hstart : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)))
    (hsegment : Set.Icc 0 T ⊆ I)
    (hSym : ∀ t ∈ Set.Icc 0 T, isoscelesSymmetryPhase (z t) = z t)
    (hx : ∀ t ∈ Set.Icc 0 T, 0 < isoscelesSolutionX z t)
    (hT : 0 ≤ T) (hx₀ : 0 < x₀) (hH : 0 < v₀-u₀)
    (htall : (v₀-u₀)^3 > 96*x₀^3)
    (hTle : T ≤ Real.sqrt (8*x₀^3)) :
    ∀ t ∈ Set.Icc 0 T,
      isoscelesSolutionX z t ≤ x₀ ∧
      (v₀-u₀)/2 < isoscelesSolutionZ z t := by
  let H := v₀-u₀
  have hH' : 0 < H := hH
  have hT0sq : (Real.sqrt (8*x₀^3))^2 = 8*x₀^3 :=
    Real.sq_sqrt (by positivity)
  have hTsq : T^2 ≤ 8*x₀^3 := by
    have hprod : 0 ≤ (Real.sqrt (8*x₀^3)-T) *
        (Real.sqrt (8*x₀^3)+T) :=
      mul_nonneg (sub_nonneg.mpr hTle) (by positivity)
    nlinarith [hT0sq, hprod]
  have hX0 : isoscelesSolutionX z 0 = x₀ := by
    simp [isoscelesSolutionX, hstart, isoscelesConfiguration, pointXY]
  have hXvel0 : isoscelesSolutionXVelocity z 0 = 0 := by
    simp [isoscelesSolutionXVelocity, hstart]
  have hZ0 : isoscelesSolutionZ z 0 = H := by
    simp [H, isoscelesSolutionZ, isoscelesSolutionV,
      isoscelesSolutionU, hstart, isoscelesConfiguration, pointXY]
  have hZvel0 : isoscelesSolutionZVelocity z 0 = 0 := by
    simp [isoscelesSolutionZVelocity, hstart]
  have hXderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionX z)
        (isoscelesSolutionXVelocity z t) t := by
    intro t ht
    exact hasDerivAt_isoscelesSolutionX hsol (hsegment ht)
  have hZderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionZ z)
        (isoscelesSolutionZVelocity z t) t := by
    intro t ht
    exact hasDerivAt_isoscelesSolutionZ hsol (hsegment ht)
  have hXacc : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionXVelocity z)
        (deriv (isoscelesSolutionXVelocity z) t) t := by
    intro t ht
    have hode := classicalNewton_isosceles_scalar_ode hsol (hsegment ht)
      (hSym t ht) (hx t ht)
    simpa only [← hode.1.deriv] using hode.1
  have hZacc : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionZVelocity z)
        (deriv (isoscelesSolutionZVelocity z) t) t := by
    intro t ht
    have hode := classicalNewton_isosceles_scalar_ode hsol (hsegment ht)
      (hSym t ht) (hx t ht)
    simpa only [← hode.2.deriv] using hode.2
  have hconcaveX : ∀ t ∈ Set.Icc 0 T,
      deriv (isoscelesSolutionXVelocity z) t ≤ 0 := by
    intro t ht
    exact le_of_lt (classicalNewton_isosceles_base_half_acceleration_neg
      hsol (hsegment ht) (hSym t ht) (hx t ht))
  have hconcaveX' : ∀ t ∈ Set.Icc 0 T,
      deriv (isoscelesSolutionXVelocity z) t ≤ -0 := by
    intro t ht
    simpa using hconcaveX t ht
  have hXbound := secondOrder_upper_bound_of_deriv_le (c := 0) hT hXderiv hXacc
    hconcaveX' hX0 hXvel0
  have hC : 0 ≤ 12/H^2 := by positivity
  have hmargin : H/2 < H - (12/H^2)*T^2/2 := by
    have hstrongMargin : H/2 < H - (12/H^2)*(8*x₀^3)/2 := by
      dsimp [H]
      field_simp [ne_of_gt hH]
      nlinarith [htall]
    have hmul := mul_le_mul_of_nonneg_left hTsq
      (by positivity : 0 ≤ (12/H^2 : ℝ))
    linarith
  have hsecondZ : ∀ t ∈ Set.Icc 0 T,
      H/2 ≤ isoscelesSolutionZ z t →
        -(12/H^2) ≤ deriv (isoscelesSolutionZVelocity z) t := by
    intro t ht hh
    exact classicalNewton_isosceles_height_second_derivative_ge_of_height_ge_half
      hsol (hsegment ht) (hSym t ht) (hx t ht) hH' hh
  have hmargin' : H/2 < isoscelesSolutionZ z 0 - (12/H^2)*T^2/2 := by
    rw [hZ0]
    exact hmargin
  have hbarrier := lower_barrier_preserved_of_second_deriv_bound
    hT hZderiv hZacc hC hsecondZ (by rw [hZ0]; linarith)
    hZvel0 hmargin'
  intro t ht
  exact ⟨by simpa using hXbound t ht, hbarrier t ht⟩

/-- Positive base half-length and vertical separation give a uniform lower
    bound for all three pair distances in an isosceles configuration. -/
theorem isoscelesConfiguration_all_distances_ge_min
    (x u v δ : ℝ) (hx : 0 < x) (hh : 0 < v-u)
    (hbase : δ ≤ 2*x) (hheight : δ ≤ v-u) :
    ∀ i j : Fin 3, i ≠ j →
      δ ≤ dist (isoscelesConfiguration x u v i)
        (isoscelesConfiguration x u v j) := by
  have hbaseSq := isoscelesConfiguration_base_dist_sq x u v
  have hleg0Sq := isoscelesConfiguration_leftLeg_dist_sq x u v
  have hleg1Sq := isoscelesConfiguration_rightLeg_dist_sq x u v
  have hbaseDist : dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) = 2*x := by
    have hnonneg : 0 ≤ dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1) := dist_nonneg
    nlinarith [hbaseSq,
      sq_nonneg (dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1) - 2*x),
      sq_nonneg (dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1) + 2*x)]
  have hleg0 : v-u ≤ dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 2) := by
    have hdistnonneg : 0 ≤ dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 2) := dist_nonneg
    apply (sq_le_sq₀ (le_of_lt hh) hdistnonneg).1
    rw [hleg0Sq]
    nlinarith [sq_nonneg x]
  have hleg1 : v-u ≤ dist (isoscelesConfiguration x u v 1)
      (isoscelesConfiguration x u v 2) := by
    have hdistnonneg : 0 ≤ dist (isoscelesConfiguration x u v 1)
        (isoscelesConfiguration x u v 2) := dist_nonneg
    apply (sq_le_sq₀ (le_of_lt hh) hdistnonneg).1
    rw [hleg1Sq]
    nlinarith [sq_nonneg x]
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij (by decide)).elim
  · simpa [hbaseDist] using hbase
  · exact le_trans hheight hleg0
  · calc
      δ ≤ 2*x := hbase
      _ = dist (isoscelesConfiguration x u v 1)
          (isoscelesConfiguration x u v 0) := by rw [dist_comm, hbaseDist]
  · exact (hij (by decide)).elim
  · exact le_trans hheight hleg1
  · simpa [dist_comm] using le_trans hheight hleg0
  · simpa [dist_comm] using le_trans hheight hleg1
  · exact (hij (by decide)).elim

/-- In an isosceles configuration with positive base half-length, every pair
    distance is at least the base half-length, independently of the height. -/
theorem isoscelesConfiguration_all_distances_ge_base_half
    (x u v : ℝ) (hx : 0 < x) :
    ∀ i j : Fin 3, i ≠ j →
      x ≤ dist (isoscelesConfiguration x u v i)
        (isoscelesConfiguration x u v j) := by
  have hbaseSq := isoscelesConfiguration_base_dist_sq x u v
  have hleg0Sq := isoscelesConfiguration_leftLeg_dist_sq x u v
  have hleg1Sq := isoscelesConfiguration_rightLeg_dist_sq x u v
  have hbase : dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) = 2*x := by
    have hdnonneg : 0 ≤ dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1) := dist_nonneg
    nlinarith [hbaseSq,
      sq_nonneg (dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1) - 2*x),
      sq_nonneg (dist (isoscelesConfiguration x u v 0)
        (isoscelesConfiguration x u v 1) + 2*x)]
  have hleg0 : x ≤ dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 2) := by
    apply (sq_le_sq₀ (le_of_lt hx) dist_nonneg).1
    rw [hleg0Sq]
    nlinarith
  have hleg1 : x ≤ dist (isoscelesConfiguration x u v 1)
      (isoscelesConfiguration x u v 2) := by
    apply (sq_le_sq₀ (le_of_lt hx) dist_nonneg).1
    rw [hleg1Sq]
    nlinarith
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij (by decide)).elim
  · simpa [hbase] using (show x ≤ 2*x by linarith)
  · exact hleg0
  · calc
      x ≤ 2*x := by linarith
      _ = dist (isoscelesConfiguration x u v 1)
          (isoscelesConfiguration x u v 0) := by rw [dist_comm, hbase]
  · exact (hij (by decide)).elim
  · exact hleg1
  · simpa [dist_comm] using hleg0
  · simpa [dist_comm] using hleg1
  · exact (hij (by decide)).elim

/-- Exact base-pair distance in an isosceles configuration with nonnegative
    base half-length. -/
theorem isoscelesConfiguration_base_dist_eq
    (x u v : ℝ) (hx : 0 ≤ x) :
    dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) = 2*x := by
  have hsq := isoscelesConfiguration_base_dist_sq x u v
  have hdnonneg : 0 ≤ dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) := dist_nonneg
  nlinarith [hsq,
    sq_nonneg (dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) - 2*x),
    sq_nonneg (dist (isoscelesConfiguration x u v 0)
      (isoscelesConfiguration x u v 1) + 2*x)]

/-- The base half-length is antitone on every regular symmetric segment from
    rest: the negative base acceleration makes its velocity nonincreasing
    from zero, hence the base half-length itself is nonincreasing. -/
theorem classicalNewton_isosceles_base_half_antitone_on_segment
    {z : ℝ → Phase} {I : Set ℝ} {T x₀ u₀ v₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I)
    (hstart : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)))
    (hsegment : Set.Icc 0 T ⊆ I)
    (hSym : ∀ t ∈ Set.Icc 0 T, isoscelesSymmetryPhase (z t) = z t)
    (hx : ∀ t ∈ Set.Icc 0 T, 0 < isoscelesSolutionX z t)
    (hT : 0 ≤ T) :
    AntitoneOn (isoscelesSolutionX z) (Set.Icc 0 T) := by
  let X : ℝ → ℝ := isoscelesSolutionX z
  let V : ℝ → ℝ := isoscelesSolutionXVelocity z
  have hV0 : V 0 = 0 := by simp [V, isoscelesSolutionXVelocity, hstart]
  have hXderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt X (V t) t := by
    intro t ht
    exact hasDerivAt_isoscelesSolutionX hsol (hsegment ht)
  have hVderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt V (deriv V t) t := by
    intro t ht
    have hode := classicalNewton_isosceles_scalar_ode hsol (hsegment ht)
      (hSym t ht) (hx t ht)
    simpa only [← hode.1.deriv] using hode.1
  have hnegVderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (fun s => -V s) (-deriv V t) t := by
    intro t ht
    exact (hVderiv t ht).neg
  have hnegVderiv_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ -deriv V t := by
    intro t ht
    have hneg := classicalNewton_isosceles_base_half_acceleration_neg
      hsol (hsegment ht) (hSym t ht) (hx t ht)
    linarith
  have hminusVmono : MonotoneOn (fun t => -V t) (Set.Icc 0 T) :=
    monotoneOn_of_hasDerivAt_nonneg (convex_Icc 0 T)
      (fun t ht => hnegVderiv t ht) hnegVderiv_nonneg
  have hVnonpos : ∀ t ∈ Set.Icc 0 T, V t ≤ 0 := by
    intro t ht
    have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
    have h := hminusVmono hzero ht (by linarith [ht.1])
    change -V 0 ≤ -V t at h
    rw [hV0] at h
    linarith
  have hminusXderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (fun s => -X s) (-V t) t := by
    intro t ht
    exact (hXderiv t ht).neg
  have hminusXderiv_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ -V t := by
    intro t ht
    exact neg_nonneg.mpr (hVnonpos t ht)
  have hminusXmono : MonotoneOn (fun t => -X t) (Set.Icc 0 T) :=
    monotoneOn_of_hasDerivAt_nonneg (convex_Icc 0 T)
      (fun t ht => hminusXderiv t ht) hminusXderiv_nonneg
  intro s hs t ht hst
  have h := hminusXmono hs ht hst
  dsimp [X] at h
  linarith

/-- Every equal-mass isosceles rest trajectory with positive initial base
    half-length loses its positive-base regularity before
    `sqrt (8*x₀^3)`, regardless of the initial height. The argument uses the
    base equation alone: concavity first gives `x≤x₀`, after which the
    stronger inverse-square acceleration bound forces `x` to vanish by the
    comparison time. -/
theorem classicalNewton_isosceles_rest_segment_impossible
    {z : ℝ → Phase} {I : Set ℝ} {T x₀ u₀ v₀ : ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    (hzero : (0 : ℝ) ∈ I)
    (hstart : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)))
    (hsegment : Set.Icc 0 T ⊆ I)
    (hx : ∀ t ∈ Set.Icc 0 T, 0 < isoscelesSolutionX z t)
    (hx₀ : 0 < x₀)
    (hT : T = Real.sqrt (8*x₀^3)) : False := by
  have hTnonneg : 0 ≤ T := by rw [hT]; positivity
  have hfixed : isoscelesSymmetryPhase (z 0) = z 0 := by
    rw [hstart]
    exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
  have hSym : ∀ t ∈ Set.Icc 0 T, isoscelesSymmetryPhase (z t) = z t := by
    intro t ht
    exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
      hfixed t (hsegment ht)
  have hanti := classicalNewton_isosceles_base_half_antitone_on_segment
    hsol hstart hsegment hSym hx hTnonneg
  have hX₀ : isoscelesSolutionX z 0 = x₀ := by
    simp [isoscelesSolutionX, hstart, isoscelesConfiguration, pointXY]
  have hXvel₀ : isoscelesSolutionXVelocity z 0 = 0 := by
    simp [isoscelesSolutionXVelocity, hstart]
  have hXle : ∀ t ∈ Set.Icc 0 T, isoscelesSolutionX z t ≤ x₀ := by
    intro t ht
    have hzeroIcc : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hTnonneg⟩
    have h := hanti hzeroIcc ht ht.1
    rw [hX₀] at h
    exact h
  have hXderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionX z)
        (isoscelesSolutionXVelocity z t) t := by
    intro t ht
    exact hasDerivAt_isoscelesSolutionX hsol (hsegment ht)
  have hXacc : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (isoscelesSolutionXVelocity z)
        (deriv (isoscelesSolutionXVelocity z) t) t := by
    intro t ht
    have hode := classicalNewton_isosceles_scalar_ode hsol (hsegment ht)
      (hSym t ht) (hx t ht)
    simpa only [← hode.1.deriv] using hode.1
  have hconcave : ∀ t ∈ Set.Icc 0 T,
      deriv (isoscelesSolutionXVelocity z) t ≤ 0 := by
    intro t ht
    exact le_of_lt (classicalNewton_isosceles_base_half_acceleration_neg
      hsol (hsegment ht) (hSym t ht) (hx t ht))
  have hforce : ∀ t ∈ Set.Icc 0 T,
      isoscelesSolutionX z t ≤ x₀ →
        deriv (isoscelesSolutionXVelocity z) t ≤ -(1/(4*x₀^2)) := by
    intro t ht hxt
    exact classicalNewton_isosceles_base_second_derivative_le_of_le_initial
      hsol (hsegment ht) (hSym t ht) (hx t ht) hxt hx₀
  exact no_positive_segment_to_sqrt_eight_scale hx₀ hT hXderiv hXacc
    hconcave hforce hX₀ hXvel₀ hx
end DroppingThreeBodies
