module

public import Dropping3Bodies.Dynamics.GeneralEnergy
public import Dropping3Bodies.Dynamics.RegularDomain
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-! Local existence for the general-mass Newton field on its regular domain.

The coefficients `G` and `m` are fixed real constants. Smoothness is needed
only away from binary collisions and does not require their positivity.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

/-- A single summand in the general Newton acceleration is C1 away from its
    source-target collision. -/
theorem generalForceTerm_contDiffAt (G : ℝ) (m : Fin 3 → ℝ)
    (z : Phase) (i j : Fin 3) (hcollision : z.1 i ≠ z.1 j) :
    ContDiffAt ℝ 1
      (fun w : Phase =>
        (G * m j * inverseCubeDistance w.1 i j) • (w.1 j - w.1 i)) z := by
  have hinv := inverseCubeDistance_contDiffAt z i j hcollision
  have hconst : ContDiffAt ℝ 1 (fun _ : Phase => G * m j) z := by
    fun_prop
  have hscalar : ContDiffAt ℝ 1
      (fun w : Phase => G * m j * inverseCubeDistance w.1 i j) z := by
    exact hconst.mul hinv
  have hvector : ContDiffAt ℝ 1
      (fun w : Phase => w.1 j - w.1 i) z := by
    fun_prop
  exact hscalar.smul hvector

/-- The general Newton field is C1 at every collision-free phase, for
    arbitrary fixed real `G` and mass coefficients. -/
theorem generalNewtonField_contDiffAt (G : ℝ) (m : Fin 3 → ℝ)
    (z : Phase) (hcf : CollisionFree z.1) :
    ContDiffAt ℝ 1 (fun w : Phase => generalNewtonField G m w) z := by
  change ContDiffAt ℝ 1
    (fun w : Phase => (w.2, fun i => generalAcceleration G m w.1 i)) z
  apply ContDiffAt.prodMk
  · fun_prop
  · rw [contDiffAt_pi]
    intro i
    have hterms (j : Fin 3) : ContDiffAt ℝ 1
        (fun w : Phase => if j = i then 0 else
          (G * m j * inverseCubeDistance w.1 i j) • (w.1 j - w.1 i)) z := by
      by_cases hij : j = i
      · simpa [hij] using (by fun_prop : ContDiffAt ℝ 1 (fun _ : Phase => (0 : Point)) z)
      · simp only [if_neg hij]
        exact generalForceTerm_contDiffAt G m z i j
          (hcf i j (Ne.symm hij))
    simpa [generalAcceleration] using
      (ContDiffAt.sum (s := Finset.univ) (fun j hj => hterms j))

/-- Every collision-free initial phase admits an actual local classical
    solution of the general-mass Newton equations. The solution interval is
    shrunk so its phase remains collision-free. -/
theorem exists_local_generalClassicalNewtonSolution (G : ℝ)
    (m : Fin 3 → ℝ) (z₀ : Phase) (hcf : CollisionFree z₀.1) :
    ∃ ε > 0, ∃ z : ℝ → Phase, z 0 = z₀ ∧
      GeneralClassicalNewtonSolution G m z (Set.Ioo (-ε) ε) := by
  obtain ⟨α, hα₀, ε, hε, hderiv⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (generalNewtonField_contDiffAt G m z₀ hcf) 0
  have hzero : 0 ∈ Set.Ioo (0 - ε) (0 + ε) := by
    constructor <;> linarith
  have hαreg : α 0 ∈ regularPhaseSet := by
    rw [hα₀]
    exact hcf
  have hcont : ContinuousAt α 0 := (hderiv 0 hzero).continuousAt
  have hpre : α ⁻¹' regularPhaseSet ∈ nhds (0 : ℝ) :=
    hcont.preimage_mem_nhds (regularPhaseSet_isOpen.mem_nhds hαreg)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let ρ := min ε δ
  refine ⟨ρ, lt_min hε hδ, α, ?_, ?_⟩
  · simpa using hα₀
  · refine ⟨isOpen_Ioo, ?_⟩
    intro t ht
    have ht' : -ρ < t ∧ t < ρ := ht
    have htin : t ∈ Set.Ioo (0 - ε) (0 + ε) := by
      constructor
      · have hlow : -min ε δ < t := by simpa [ρ] using ht'.1
        linarith [min_le_left ε δ]
      · have hhigh : t < min ε δ := by simpa [ρ] using ht'.2
        linarith [min_le_left ε δ]
    have hdist : dist t (0 : ℝ) < δ := by
      simpa only [Real.dist_eq, sub_zero] using
        (lt_of_lt_of_le (abs_lt.mpr (by simpa only [sub_zero] using ht'))
          (min_le_right ε δ))
    have hregular : α t ∈ regularPhaseSet := hball (by
      change dist t (0 : ℝ) < δ
      exact hdist)
    exact ⟨by simpa [regularPhaseSet] using hregular,
      hderiv t htin⟩

/-- General-mass local uniqueness at the initial time, obtained from C1
    regularity of the field and Mathlib's ODE uniqueness theorem. -/
theorem generalClassicalNewton_local_unique_at
    (G : ℝ) (m : Fin 3 → ℝ) {z w : ℝ → Phase} {I J : Set ℝ}
    (hz : GeneralClassicalNewtonSolution G m z I)
    (hw : GeneralClassicalNewtonSolution G m w J)
    (h0I : 0 ∈ I) (h0J : 0 ∈ J) (hinit : z 0 = w 0) :
    z =ᶠ[nhds (0 : ℝ)] w := by
  have hz0 := hz.2 0 h0I
  have hw0 := hw.2 0 h0J
  obtain ⟨K, U, hU, hLip⟩ :=
    (generalNewtonField_contDiffAt G m (z 0) hz0.1).exists_lipschitzOnWith
  obtain ⟨r, hr, hballU⟩ := Metric.mem_nhds_iff.mp hU
  let V : Set Phase := Metric.ball (z 0) r
  have hLipV : LipschitzOnWith K (generalNewtonField G m) V := by
    apply hLip.mono
    intro x hx
    exact hballU hx
  have hzIevent : I ∈ nhds (0 : ℝ) := hz.1.mem_nhds h0I
  have hwIevent : J ∈ nhds (0 : ℝ) := hw.1.mem_nhds h0J
  have hzVevent : ∀ᶠ t in nhds (0 : ℝ), z t ∈ V :=
    hz0.2.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (z 0) hr)
  have hwVevent : ∀ᶠ t in nhds (0 : ℝ), w t ∈ V := by
    have hcont := hw0.2.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (w 0) hr)
    change ∀ᶠ t in nhds (0 : ℝ), w t ∈ Metric.ball (w 0) r at hcont
    simpa [V, hinit] using hcont
  have hv : ∀ᶠ t in nhds (0 : ℝ),
      LipschitzOnWith K (generalNewtonField G m) V :=
    Filter.Eventually.of_forall fun _ => hLipV
  have hzevent : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt z (generalNewtonField G m (z t)) t ∧ z t ∈ V := by
    filter_upwards [hzIevent, hzVevent] with t htI htV
    exact ⟨(hz.2 t htI).2, htV⟩
  have hwevent : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt w (generalNewtonField G m (w t)) t ∧ w t ∈ V := by
    filter_upwards [hwIevent, hwVevent] with t htI htV
    exact ⟨(hw.2 t htI).2, htV⟩
  exact ODE_solution_unique_of_eventually hv hzevent hwevent hinit

end DroppingThreeBodies
