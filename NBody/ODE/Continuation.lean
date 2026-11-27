module

public import NBody.ODE.LocalTheory
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

namespace NBody

open Filter
open scoped Topology

/-- Extend a left trajectory by its finite endpoint limit. If the vector field
is continuous at that limit, the extended curve has the expected one-sided
derivative. This is the calculus step behind regular-endpoint continuation. -/
theorem hasDerivWithinAt_leftExtension_of_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {X : E → E} {z : ℝ → E} {I : Set ℝ} {xT : E} {a T : ℝ}
    (haT : a < T) (hsol : SolutionOn Ω X z I)
    (hright : ∀ t ∈ Set.Ioo a T, t ∈ I)
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 xT))
    (hX : ContinuousAt X xT) :
    HasDerivWithinAt (fun t => if t < T then z t else xT)
      (X xT) (Set.Iic T) T := by
  let zExt : ℝ → E := fun t => if t < T then z t else xT
  have hEqEvent : zExt =ᶠ[nhdsWithin T (Set.Iio T)] z := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t < T at ht
    simp [zExt, ht]
  have hExtLim : Tendsto zExt (nhdsWithin T (Set.Iio T)) (𝓝 xT) :=
    hlim.congr' hEqEvent.symm
  have hExtCont' : ContinuousWithinAt zExt (Set.Ioo a T) T := by
    rw [continuousWithinAt_Ioo_iff_Iio haT]
    change Tendsto zExt (nhdsWithin T (Set.Iio T)) (𝓝 (zExt T))
    simpa [zExt] using hExtLim
  have hfieldLim : Tendsto (fun t => X (z t))
      (nhdsWithin T (Set.Iio T)) (𝓝 (X xT)) := hX.tendsto.comp hlim
  have hderivEq : ∀ᶠ t in nhdsWithin T (Set.Iio T),
      deriv zExt t = X (z t) := by
    have haEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T), t ∈ Set.Ioi a :=
      Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio T))
        (Ioi_mem_nhds haT)
    filter_upwards [haEvent, self_mem_nhdsWithin] with t hta ht
    have htI : t ∈ I := hright t ⟨hta, ht⟩
    have hD : HasDerivAt z (X (z t)) t := (hsol.2 t htI).2
    have hlocalEq : zExt =ᶠ[𝓝 t] z := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      change s < T at hs
      simp [zExt, hs]
    exact (hD.congr_of_eventuallyEq hlocalEq).deriv
  have hderivFunctionEq : (fun t => deriv zExt t) =ᶠ[nhdsWithin T (Set.Iio T)]
      (fun t => X (z t)) := by
    filter_upwards [hderivEq] with t ht
    exact ht
  have hderivLim : Tendsto (fun t => deriv zExt t)
      (nhdsWithin T (Set.Iio T)) (𝓝 (X xT)) := hfieldLim.congr' hderivFunctionEq.symm
  have hdiff : DifferentiableOn ℝ zExt (Set.Ioo a T) := by
    intro t ht
    have htI : t ∈ I := hright t ht
    have hD : HasDerivAt z (X (z t)) t := (hsol.2 t htI).2
    have hlocalEq : zExt =ᶠ[𝓝 t] z := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      change s < T at hs
      simp [zExt, hs]
    exact (hD.congr_of_eventuallyEq hlocalEq).differentiableAt.differentiableWithinAt
  exact hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hExtCont'
    (Ioo_mem_nhdsLT haT) hderivLim

/-- A finite regular phase limit extends a classical solution to a strictly
larger right interval. The old trajectory is preserved and the new local IVP
starts from the limiting state. -/
theorem exists_local_extension_of_right_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Ω : Set E} {X : E → E} {z : ℝ → E} {xT : E} {a T : ℝ}
    (hΩ : IsOpen Ω) (haT : a < T) (hsol : SolutionOn Ω X z (Set.Ioo a T))
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 xT))
    (hxT : xT ∈ Ω) (hX : ContDiffAt ℝ 1 X xT) :
    ∃ ε > 0, ∃ w : ℝ → E,
      w T = xT ∧ SolutionOn Ω X w (Set.Ioo a (T + ε)) ∧
      ∀ t ∈ Set.Ioo a T, w t = z t := by
  obtain ⟨ε, hε, y, hy0, hySol⟩ := exists_local_solutionOn hΩ hxT hX 0
  let w : ℝ → E := fun t => if t < T then z t else y (t - T)
  have hleft : HasDerivWithinAt (fun t => if t < T then z t else xT)
      (X xT) (Set.Iic T) T :=
    hasDerivWithinAt_leftExtension_of_limit haT hsol
      (fun t ht => ht) hlim hX.continuousAt
  have hEqLeft : ∀ t ∈ Set.Iic T,
      w t = (if t < T then z t else xT) := by
    intro t ht
    by_cases htt : t < T
    · simp [w, htt]
    · have hEq : t = T := le_antisymm ht (le_of_not_gt htt)
      subst t
      simp [w, hy0]
  have hWLeft : HasDerivWithinAt w (X xT) (Set.Iic T) T :=
    hleft.congr hEqLeft (hEqLeft T (by simp))
  have hlocal0 : (0 : ℝ) ∈ Set.Ioo (0 - ε) (0 + ε) := by
    constructor <;> linarith
  have hyDerivT : HasDerivAt y (X xT) 0 := by
    have h := (hySol.2 0 hlocal0).2
    simpa [hy0] using h
  have hShift : HasDerivAt (fun t => y (t - T)) (X xT) T := by
    have hD : HasDerivAt y (X xT) (T - T) := by simpa using hyDerivT
    simpa using HasDerivAt.comp_sub_const T T hD
  have hEqRight : ∀ t ∈ Set.Ici T, w t = y (t - T) := by
    intro t ht
    change T ≤ t at ht
    simp [w, not_lt_of_ge ht]
  have hWRight : HasDerivWithinAt w (X xT) (Set.Ici T) T :=
    hShift.hasDerivWithinAt.congr hEqRight (hEqRight T (by simp))
  have hleftSlope : Tendsto (slope w T) (nhdsWithin T (Set.Iio T))
      (𝓝 (X xT)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hWLeft
    have hle : nhdsWithin T (Set.Iio T) ≤ nhdsWithin T (Set.Iic T \ {T}) :=
      nhdsWithin_mono T (by
        intro t ht
        change t < T at ht
        exact ⟨le_of_lt ht, by simp [ht.ne]⟩)
    exact h.mono_left hle
  have hrightSlope : Tendsto (slope w T) (nhdsWithin T (Set.Ioi T))
      (𝓝 (X xT)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hWRight
    have hle : nhdsWithin T (Set.Ioi T) ≤ nhdsWithin T (Set.Ici T \ {T}) :=
      nhdsWithin_mono T (by
        intro t ht
        change T < t at ht
        exact ⟨le_of_lt ht, by simp [ht.ne']⟩)
    exact h.mono_left hle
  have hjoin : HasDerivAt w (X xT) T :=
    (hasDerivAt_iff_tendsto_slope_left_right).2 ⟨hleftSlope, hrightSlope⟩
  refine ⟨ε, hε, w, ?_, ?_, ?_⟩
  · simp [w, hy0]
  · refine ⟨isOpen_Ioo, ?_⟩
    intro t ht
    by_cases htt : t < T
    · have htI : t ∈ Set.Ioo a T := ⟨ht.1, htt⟩
      have hdata := hsol.2 t htI
      have hevent : w =ᶠ[𝓝 t] z := by
        filter_upwards [Iio_mem_nhds htt] with s hs
        change s < T at hs
        simp [w, hs]
      have hD := hdata.2.congr_of_eventuallyEq hevent
      have hvalue : w t = z t := by simp [w, htt]
      exact ⟨by rw [hvalue]; exact hdata.1,
        by simpa [hvalue] using hD⟩
    · by_cases hEq : t = T
      · subst t
        have hvalue : w T = xT := by simp [w, hy0]
        exact ⟨by simpa [hvalue] using hxT, by simpa [hvalue] using hjoin⟩
      · have htt' : T < t := lt_of_le_of_ne (le_of_not_gt htt) (Ne.symm hEq)
        have hτ : t - T ∈ Set.Ioo (-ε) ε := by
          constructor <;> linarith [ht.2]
        have hτ' : t - T ∈ Set.Ioo (0 - ε) (0 + ε) := by simpa using hτ
        have hdata := hySol.2 (t - T) hτ'
        have hshiftD : HasDerivAt (fun s => y (s - T))
            (X (y (t - T))) t := by
          exact HasDerivAt.comp_sub_const t T hdata.2
        have hevent : w =ᶠ[𝓝 t] (fun s => y (s - T)) := by
          filter_upwards [Ioi_mem_nhds htt'] with s hs
          change T < s at hs
          simp [w, not_lt_of_gt hs]
        have hD := hshiftD.congr_of_eventuallyEq hevent
        have hvalue : w t = y (t - T) := by simp [w, not_lt_of_gt htt']
        exact ⟨by rw [hvalue]; exact hdata.1,
          by simpa [hvalue] using hD⟩
  · intro t ht
    simp [w, ht.2]

end NBody
