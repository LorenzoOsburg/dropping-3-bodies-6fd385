module

public import NBody.Solution
public import NBody.Regularity
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

namespace NBody

open Filter
open scoped Topology

/-- Every collision-free phase has a genuine classical solution on a nonempty
open interval around any prescribed initial time. -/
theorem exists_local_solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (G : ℝ) (m : ι → ℝ) (a : ℝ)
    (z₀ : Phase ι d) (hcf : CollisionFree z₀.1) :
    ∃ ε > 0, ∃ z : ℝ → Phase ι d, z a = z₀ ∧
      ClassicalSolution G m z (Set.Ioo (a - ε) (a + ε)) := by
  obtain ⟨α, hαa, ε, hε, hderiv⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (vectorField_contDiffAt G m z₀ hcf) a
  have ha : a ∈ Set.Ioo (a - ε) (a + ε) := by constructor <;> linarith
  have hαreg : α a ∈ regularPhaseSet ι d := by
    rw [hαa]
    exact hcf
  have hcont : ContinuousAt α a := (hderiv a ha).continuousAt
  have hpre : α ⁻¹' regularPhaseSet ι d ∈ 𝓝 a :=
    hcont.preimage_mem_nhds ((isOpen_regularPhaseSet (ι := ι) d).mem_nhds hαreg)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let ρ := min ε δ
  refine ⟨ρ, lt_min hε hδ, α, hαa, ?_⟩
  refine ⟨isOpen_Ioo, ?_⟩
  intro t ht
  have ht' : a - ρ < t ∧ t < a + ρ := ht
  have htin : t ∈ Set.Ioo (a - ε) (a + ε) := by
    constructor
    · linarith [min_le_left ε δ]
    · linarith [min_le_left ε δ]
  have htAbs : |t - a| < ρ := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdist : dist t a < δ := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le htAbs (min_le_right ε δ)
  have hregular : α t ∈ regularPhaseSet ι d := hball hdist
  exact ⟨by simpa [regularPhaseSet] using hregular, hderiv t htin⟩

/-- Solutions with the same regular initial phase agree on a neighborhood of
that time. This is the local uniqueness contract supplied by Mathlib's ODE
uniqueness theorem. -/
theorem solution_unique_near_initial {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (G : ℝ) (m : ι → ℝ)
    {z w : ℝ → Phase ι d} {I J : Set ℝ} {a : ℝ}
    (hz : ClassicalSolution G m z I) (hw : ClassicalSolution G m w J)
    (haI : a ∈ I) (haJ : a ∈ J) (hinit : z a = w a) :
    z =ᶠ[𝓝 a] w := by
  have hz0 := hz.2 a haI
  have hw0 := hw.2 a haJ
  obtain ⟨K, U, hU, hLip⟩ :=
    (vectorField_contDiffAt G m (z a) hz0.1).exists_lipschitzOnWith
  obtain ⟨r, hr, hballU⟩ := Metric.mem_nhds_iff.mp hU
  let V : Set (Phase ι d) := Metric.ball (z a) r
  have hLipV : LipschitzOnWith K (vectorField G m) V := by
    apply hLip.mono
    intro x hx
    exact hballU hx
  have hzIevent : I ∈ 𝓝 a := hz.1.mem_nhds haI
  have hwIevent : J ∈ 𝓝 a := hw.1.mem_nhds haJ
  have hzVevent : ∀ᶠ t in 𝓝 a, z t ∈ V :=
    hz0.2.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (z a) hr)
  have hwVevent : ∀ᶠ t in 𝓝 a, w t ∈ V := by
    have hcont := hw0.2.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (w a) hr)
    change ∀ᶠ t in 𝓝 a, w t ∈ Metric.ball (w a) r at hcont
    simpa [V, hinit] using hcont
  have hv : ∀ᶠ t in 𝓝 a,
      LipschitzOnWith K (vectorField G m) V :=
    Filter.Eventually.of_forall fun _ => hLipV
  have hzevent : ∀ᶠ t in 𝓝 a,
      HasDerivAt z (vectorField G m (z t)) t ∧ z t ∈ V := by
    filter_upwards [hzIevent, hzVevent] with t htI htV
    exact ⟨(hz.2 t htI).2, htV⟩
  have hwevent : ∀ᶠ t in 𝓝 a,
      HasDerivAt w (vectorField G m (w t)) t ∧ w t ∈ V := by
    filter_upwards [hwIevent, hwVevent] with t htI htV
    exact ⟨(hw.2 t htI).2, htV⟩
  exact ODE_solution_unique_of_eventually hv hzevent hwevent hinit

end NBody
