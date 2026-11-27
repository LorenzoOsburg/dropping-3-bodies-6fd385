module

public import NBody.ODE.Solution
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

namespace NBody

open Filter
open scoped Topology

/-- A `C¹` autonomous vector field has a local classical solution through any
point of an open state domain. The interval is shrunk so that the curve stays
inside the prescribed domain. -/
theorem exists_local_solutionOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Ω : Set E} {X : E → E} {x₀ : E}
    (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω) (hX : ContDiffAt ℝ 1 X x₀)
    (a : ℝ) :
    ∃ ε > 0, ∃ z : ℝ → E, z a = x₀ ∧
      SolutionOn Ω X z (Set.Ioo (a - ε) (a + ε)) := by
  obtain ⟨α, hαa, ε, hε, hderiv⟩ :=
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ a
  have ha : a ∈ Set.Ioo (a - ε) (a + ε) := by constructor <;> linarith
  have hαmem : α a ∈ Ω := by simpa [hαa] using hx₀
  have hcont : ContinuousAt α a := (hderiv a ha).continuousAt
  have hpre : α ⁻¹' Ω ∈ 𝓝 a := hcont.preimage_mem_nhds (hΩ.mem_nhds hαmem)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let ρ := min ε δ
  refine ⟨ρ, lt_min hε hδ, α, hαa, isOpen_Ioo, ?_⟩
  intro t ht
  change a - min ε δ < t ∧ t < a + min ε δ at ht
  have ht' : a - ε < t ∧ t < a + ε := by
    constructor <;> linarith [ht.1, ht.2, min_le_left ε δ]
  have htAbs : |t - a| < ρ := by
    rw [abs_lt]
    constructor <;> dsimp [ρ] <;> linarith [ht.1, ht.2]
  have hdist : dist t a < δ := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le htAbs (min_le_right ε δ)
  exact ⟨hball hdist, hderiv t ht'⟩

/-- Local uniqueness for a `C¹` autonomous vector field. This theorem only
requires regularity at the common initial state. -/
theorem solutionOn_unique_near_initial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω : Set E} {X : E → E} {z w : ℝ → E}
    {I J : Set ℝ} {a : ℝ}
    (hz : SolutionOn Ω X z I) (hw : SolutionOn Ω X w J)
    (haI : a ∈ I) (haJ : a ∈ J) (hinit : z a = w a)
    (hX : ContDiffAt ℝ 1 X (z a)) : z =ᶠ[𝓝 a] w := by
  have hz0 := hz.2 a haI
  have hw0 := hw.2 a haJ
  obtain ⟨K, U, hU, hLip⟩ := hX.exists_lipschitzOnWith
  obtain ⟨r, hr, hballU⟩ := Metric.mem_nhds_iff.mp hU
  let V : Set E := Metric.ball (z a) r
  have hLipV : LipschitzOnWith K X V := by
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
  have hv : ∀ᶠ t in 𝓝 a, LipschitzOnWith K X V :=
    Filter.Eventually.of_forall fun _ => hLipV
  have hzevent : ∀ᶠ t in 𝓝 a,
      HasDerivAt z (X (z t)) t ∧ z t ∈ V := by
    filter_upwards [hzIevent, hzVevent] with t htI htV
    exact ⟨(hz.2 t htI).2, htV⟩
  have hwevent : ∀ᶠ t in 𝓝 a,
      HasDerivAt w (X (w t)) t ∧ w t ∈ V := by
    filter_upwards [hwIevent, hwVevent] with t htI htV
    exact ⟨(hw.2 t htI).2, htV⟩
  exact ODE_solution_unique_of_eventually hv hzevent hwevent hinit

/-- Local uniqueness propagates over a preconnected overlap. Equality is a
locally constant Boolean predicate: uniqueness handles equality points and
continuity handles inequality points. -/
theorem solutions_eqOn_of_preconnected_overlap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [T2Space E]
    {Ω : Set E} {X : E → E} {z w : ℝ → E} {I J : Set ℝ} {t₀ : ℝ}
    (hz : SolutionOn Ω X z I) (hw : SolutionOn Ω X w J)
    (hX : ∀ x ∈ Ω, ContDiffAt ℝ 1 X x)
    (hconn : IsPreconnected (I ∩ J)) (ht₀ : t₀ ∈ I ∩ J)
    (hinit : z t₀ = w t₀) : ∀ t ∈ I ∩ J, z t = w t := by
  classical
  let S := {t : ℝ // t ∈ I ∩ J}
  let f : S → Bool := fun t => decide (z t.1 = w t.1)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hzX := hz.2 x.1 x.2.1
    have hwX := hw.2 x.1 x.2.2
    by_cases heq : z x.1 = w x.1
    · have hEq := solutionOn_unique_near_initial hz hw
        x.2.1 x.2.2 heq (hX (z x.1) hzX.1)
      have hEqSub : ∀ᶠ y : S in 𝓝 x, z y.1 = w y.1 := by
        rw [nhds_subtype_eq_comap]
        exact hEq.comap Subtype.val
      filter_upwards [hEqSub] with y hy
      simp [f, heq, hy]
    · have hneOpen : IsOpen {p : E × E | p.1 ≠ p.2} :=
        isOpen_ne_fun continuous_fst continuous_snd
      have hpairCont : ContinuousAt (fun t : ℝ => (z t, w t)) x.1 :=
        hzX.2.continuousAt.prodMk hwX.2.continuousAt
      have hne : ∀ᶠ t in 𝓝 x.1, z t ≠ w t := by
        have hmem : (fun t : ℝ => (z t, w t)) ⁻¹'
            {p : E × E | p.1 ≠ p.2} ∈ 𝓝 x.1 :=
          hpairCont.preimage_mem_nhds (hneOpen.mem_nhds heq)
        filter_upwards [hmem] with t ht
        exact ht
      have hneSub : ∀ᶠ y : S in 𝓝 x, z y.1 ≠ w y.1 := by
        rw [nhds_subtype_eq_comap]
        exact hne.comap Subtype.val
      filter_upwards [hneSub] with y hy
      simp [f, heq, hy]
  letI : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  intro t ht
  have hval := hloc.apply_eq_of_preconnectedSpace
    (⟨t₀, ht₀⟩ : S) (⟨t, ht⟩ : S)
  have htrue : f ⟨t₀, ht₀⟩ = true := by simp [f, hinit]
  have h : f ⟨t, ht⟩ = true := by simpa [htrue] using hval.symm
  exact of_decide_eq_true h

end NBody
