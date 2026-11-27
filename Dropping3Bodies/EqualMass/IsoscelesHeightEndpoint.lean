module

public import Dropping3Bodies.EqualMass.IsoscelesMaximalEndpoint
public import Dropping3Bodies.Support.IntervalEndpoint
public import Mathlib.Tactic

@[expose] public section

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- On the maximal forward orbit from tall isosceles rest data, the vertical
separation has a finite left limit at the finite right endpoint, and the
uniform comparison barrier survives in that limit. -/
theorem maximalNewtonUnion_tall_isosceles_height_tends_limit
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀) (hH : 0 < v₀-u₀)
    (htall : (v₀-u₀)^3 > 96*x₀^3)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ∃ hτ : ℝ,
      Tendsto (isoscelesSolutionZ (maximalNewtonUnionTrajectory z₀))
        (nhdsWithin (sSup (maximalNewtonUnionDomain z₀))
          (Set.Iio (sSup (maximalNewtonUnionDomain z₀)))) (𝓝 hτ) ∧
      (v₀-u₀)/2 ≤ hτ := by
  let D := maximalNewtonUnionDomain z₀
  let z := maximalNewtonUnionTrajectory z₀
  let τ := sSup D
  let T₀ := Real.sqrt (8*x₀^3)
  let H := v₀-u₀
  let C := 12/H^2
  let Z := isoscelesSolutionZ z
  let W := isoscelesSolutionZVelocity z
  have hupperT : ∀ t ∈ D, t < T₀ := by
    simpa [D, T₀] using
      maximalNewtonUnionDomain_bddAbove_of_tall_isosceles
        x₀ u₀ v₀ hx₀ hH htall z₀ hstart hcf
  have hbounded : BddAbove D := ⟨T₀, fun t ht => le_of_lt (hupperT t ht)⟩
  have hnonempty : D.Nonempty := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact ⟨0, maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩⟩
  have hτpos : 0 < τ := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    have hwmem : w.right/2 ∈ D := by
      apply maximalNewtonWitness_interval_subset z₀ w
      constructor <;> linarith [w.left_lt_zero, w.zero_lt_right]
    exact lt_of_lt_of_le (by linarith [w.zero_lt_right]) (le_csSup hbounded hwmem)
  have hτupper : τ ≤ T₀ := csSup_le hnonempty
    (fun t ht => le_of_lt (hupperT t ht))
  have hzero : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hconn : IsPreconnected D := by simpa [D] using
    isPreconnected_maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D :=
    maximalNewtonUnionTrajectory_solution z₀
  have hinit : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  have hstartZ : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)) :=
    hinit.trans hstart
  have hright : ∀ t ∈ Set.Ico 0 τ, t ∈ D := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := (lt_csSup_iff hbounded hnonempty).mp ht.2
    exact hconn.Icc_subset hzero hs ⟨ht.1, le_of_lt hts⟩
  have hstartSym : isoscelesSymmetryPhase (z 0) = z 0 := by
    rw [hstartZ]
    exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
  have hC : 0 ≤ C := by positivity
  have hW0 : W 0 = 0 := by
    simp [W, isoscelesSolutionZVelocity, hstartZ]
  have hWbounds : ∀ t ∈ Set.Ico 0 τ, -C*T₀ ≤ W t ∧ W t ≤ 0 := by
    intro t ht
    have hseg : Set.Icc 0 t ⊆ D := by
      apply hconn.Icc_subset hzero (hright t ht)
    have hSym : ∀ s ∈ Set.Icc 0 t, isoscelesSymmetryPhase (z s) = z s := by
      intro s hs
      exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
        hstartSym s (hseg hs)
    have hx : ∀ s ∈ Set.Icc 0 t, 0 < isoscelesSolutionX z s :=
      classicalNewton_isosceles_base_half_positive_on_segment
        hsol hstartZ hseg hSym hx₀
    have htT : 0 ≤ t := ht.1
    have htTle : t ≤ T₀ := le_trans (le_of_lt ht.2) hτupper
    have hcoord := classicalNewton_isosceles_tall_coordinate_bounds_on_segment
      hsol hstartZ hseg hSym hx htT hx₀ hH htall htTle
    have hWderiv : ∀ s ∈ Set.Icc 0 t, HasDerivAt W (deriv W s) s := by
      intro s hs
      have hode := classicalNewton_isosceles_scalar_ode hsol (hseg hs)
        (hSym s hs) (hx s hs)
      simpa only [← hode.2.deriv] using hode.2
    have hWupper' : ∀ s ∈ Set.Icc 0 t, deriv W s ≤ 0 := by
      intro s hs
      have hode := classicalNewton_isosceles_scalar_ode hsol (hseg hs)
        (hSym s hs) (hx s hs)
      have hcf' := classicalNewton_isosceles_reconstructed_configuration_collisionFree
        hsol (hseg hs) (hSym s hs)
      have hd : 0 < dist
          (isoscelesConfiguration (isoscelesSolutionX z s)
            (isoscelesSolutionU z s) (isoscelesSolutionV z s) 0)
          (isoscelesConfiguration (isoscelesSolutionX z s)
            (isoscelesSolutionU z s) (isoscelesSolutionV z s) 2) :=
        dist_pos.mpr (hcf' 0 2 (by decide))
      have hk : 0 < inverseCubeDistance
          (isoscelesConfiguration (isoscelesSolutionX z s)
            (isoscelesSolutionU z s) (isoscelesSolutionV z s)) 0 2 := by
        rw [inverseCubeDistance_eq_inv_distance_cube]
        positivity
      rw [hode.2.deriv]
      have hz : 0 < Z s := by
        have hh := (hcoord s hs).2
        dsimp [Z, H] at hh ⊢
        linarith
      have hmul : 0 ≤ 3 * isoscelesSolutionZ z s *
          inverseCubeDistance
            (isoscelesConfiguration (isoscelesSolutionX z s)
              (isoscelesSolutionU z s) (isoscelesSolutionV z s)) 0 2 := by
        positivity
      nlinarith
    have hWlower' : ∀ s ∈ Set.Icc 0 t, -C ≤ deriv W s := by
      intro s hs
      have hSymS := hSym s hs
      have hxS := hx s hs
      have hhS : H/2 ≤ Z s := by
        have hh := (hcoord s hs).2
        dsimp [H, Z]
        linarith
      have hlower := classicalNewton_isosceles_height_second_derivative_ge_of_height_ge_half
        hsol (hseg hs) hSymS hxS hH hhS
      dsimp [C]
      linarith
    have hminusDeriv : ∀ s ∈ Set.Icc 0 t, 0 ≤ -deriv W s := by
      intro s hs
      linarith [hWupper' s hs]
    have hminusHas : ∀ s ∈ Set.Icc 0 t,
        HasDerivAt (fun r => -W r) (-deriv W s) s := by
      intro s hs
      exact (hWderiv s hs).neg
    have hminusMono : MonotoneOn (fun s => -W s) (Set.Icc 0 t) :=
      monotoneOn_of_hasDerivAt_nonneg (convex_Icc 0 t) hminusHas hminusDeriv
    have htmem : t ∈ Set.Icc 0 t := ⟨ht.1, le_rfl⟩
    have hzeroMem : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht.1⟩
    have hWnonpos : W t ≤ 0 := by
      have h := hminusMono hzeroMem htmem ht.1
      change -W 0 ≤ -W t at h
      rw [hW0] at h
      linarith
    have hGderiv : ∀ s ∈ Set.Icc 0 t,
        HasDerivAt (fun r => W r + C*r) (deriv W s + C) s := by
      intro s hs
      have hlin : HasDerivAt (fun r : ℝ => C*r) C s := by
        simpa using (hasDerivAt_id s).const_mul C
      exact (hWderiv s hs).add hlin
    have hGnonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ deriv W s + C := by
      intro s hs
      linarith [hWlower' s hs]
    have hGmono : MonotoneOn (fun s => W s + C*s) (Set.Icc 0 t) :=
      monotoneOn_of_hasDerivAt_nonneg (convex_Icc 0 t) hGderiv hGnonneg
    have hG0 : W 0 + C*0 = 0 := by rw [hW0]; ring
    have hGlow := hGmono hzeroMem htmem ht.1
    have hWlo : -C*t ≤ W t := by dsimp at hGlow; linarith
    exact ⟨le_trans (by nlinarith [hC, htTle]) hWlo, hWnonpos⟩
  let K : NNReal := ⟨C*T₀, mul_nonneg hC (Real.sqrt_nonneg _)⟩
  have hLip : LipschitzOnWith K Z (Set.Ico 0 τ) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (hasDerivAt_isoscelesSolutionZ hsol (hright t ht)).differentiableAt
    · intro t ht
      have hb := hWbounds t ht
      rw [(hasDerivAt_isoscelesSolutionZ hsol (hright t ht)).deriv]
      apply NNReal.coe_le_coe.mpr
      change ‖W t‖ ≤ C*T₀
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [hb.1, hb.2]
    · exact convex_Ico 0 τ
  obtain ⟨hτ, hlim⟩ :=
    exists_left_limit_of_lipschitzOnWith_finiteDimensional hτpos hLip
  have hheightEvent : ∀ᶠ t in nhdsWithin τ (Set.Iio τ), H/2 ≤ Z t := by
    have hnear : ∀ᶠ t in nhdsWithin τ (Set.Iio τ), 0 < t := by
      exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio τ))
        (Ioi_mem_nhds hτpos)
    filter_upwards [hnear, self_mem_nhdsWithin] with t htt htτ
    have htD : t ∈ D := hright t ⟨le_of_lt htt, htτ⟩
    have hseg : Set.Icc 0 t ⊆ D := by
      apply hconn.Icc_subset hzero htD
    have hSym : ∀ s ∈ Set.Icc 0 t, isoscelesSymmetryPhase (z s) = z s := by
      intro s hs
      exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
        hstartSym s (hseg hs)
    have hx : ∀ s ∈ Set.Icc 0 t, 0 < isoscelesSolutionX z s :=
      classicalNewton_isosceles_base_half_positive_on_segment
        hsol hstartZ hseg hSym hx₀
    have hcoord := classicalNewton_isosceles_tall_coordinate_bounds_on_segment
      hsol hstartZ hseg hSym hx (le_of_lt htt) hx₀ hH htall
      (le_trans (le_of_lt htτ) hτupper)
    have hh := (hcoord t ⟨le_of_lt htt, le_rfl⟩).2
    dsimp [H, Z]
    linarith
  have hlimLower : H/2 ≤ hτ :=
    (isClosed_Ici.mem_of_tendsto hlim hheightEvent)
  exact ⟨hτ, hlim, by simpa [H] using hlimLower⟩

end

end DroppingThreeBodies
