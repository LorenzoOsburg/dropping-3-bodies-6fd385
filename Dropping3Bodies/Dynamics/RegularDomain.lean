module

public import Dropping3Bodies.Dynamics.Newton
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

/-!
The open regular phase-space region for the unit Newton field.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

/-- Phase points whose position coordinates have no binary collision. -/
def regularPhaseSet : Set Phase := {z | CollisionFree z.1}

/-- The Newton vector field is considered on an open subset of phase space. -/
theorem regularPhaseSet_isOpen : IsOpen regularPhaseSet := by
  have hcoord (i : Fin 3) : Continuous (fun z : Phase => z.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hpair (i j : Fin 3) : IsOpen {z : Phase | i = j ∨ z.1 i ≠ z.1 j} := by
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using isOpen_ne_fun (hcoord i) (hcoord j)
  have hset : regularPhaseSet =
      ⋂ i : Fin 3, ⋂ j : Fin 3,
        {z : Phase | i = j ∨ z.1 i ≠ z.1 j} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_setOf_eq, regularPhaseSet,
      CollisionFree]
    constructor
    · intro hz i j
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (hz i j hij)
    · intro hz i j hij
      exact (hz i j).resolve_left hij
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => hpair i j

/-- Pairwise distance is C1 as a function of phase away from binary
    collision; the only nonlinear operation is the norm at a nonzero vector. -/
theorem contDiffAt_phaseDistance (z : Phase) (i j : Fin 3)
    (hcollision : (z.1 i) ≠ z.1 j) :
    ContDiffAt ℝ 1 (fun w : Phase => dist (w.1 i) (w.1 j)) z := by
  have hdiff : ContDiffAt ℝ 1 (fun w : Phase => w.1 i - w.1 j) z := by
    fun_prop
  have hnonzero : z.1 i - z.1 j ≠ (0 : Point) := sub_ne_zero.mpr hcollision
  simpa only [dist_eq_norm] using ContDiffAt.norm ℝ hdiff hnonzero

/-- The inverse-cube kernel is C1 as a phase function wherever its two
    positions are distinct. The integer power is replaced locally by the
    inverse of a positive cubic. -/
theorem inverseCubeDistance_contDiffAt (z : Phase) (i j : Fin 3)
    (hcollision : z.1 i ≠ z.1 j) :
    ContDiffAt ℝ 1 (fun w : Phase => inverseCubeDistance w.1 i j) z := by
  have hd := contDiffAt_phaseDistance z i j hcollision
  have hpos : 0 < dist (z.1 i) (z.1 j) := dist_pos.mpr hcollision
  have hpow : ContDiffAt ℝ 1
      (fun w : Phase => dist (w.1 i) (w.1 j) ^ 3) z := hd.pow 3
  have hpow_ne : dist (z.1 i) (z.1 j) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt hpos)
  have hinv := hpow.inv hpow_ne
  have heq : (fun w : Phase => inverseCubeDistance w.1 i j) =ᶠ[nhds z]
      (fun w => (dist (w.1 i) (w.1 j) ^ 3)⁻¹) := by
    filter_upwards [] with w
    simp [inverseCubeDistance, zpow_neg]
  exact hinv.congr_of_eventuallyEq heq

/-- Each unit-mass acceleration coordinate is C1 at every collision-free
    phase. -/
theorem unitAcceleration_contDiffAt (z : Phase) (hcf : CollisionFree z.1)
    (i : Fin 3) :
    ContDiffAt ℝ 1 (fun w : Phase => unitAcceleration w.1 i) z := by
  fin_cases i
  · change ContDiffAt ℝ 1 (fun w : Phase =>
      inverseCubeDistance w.1 0 1 • (w.1 1 - w.1 0) +
      inverseCubeDistance w.1 0 2 • (w.1 2 - w.1 0)) z
    apply ContDiffAt.add
    · exact (inverseCubeDistance_contDiffAt z 0 1 (hcf 0 1 (by decide))).smul (by fun_prop)
    · exact (inverseCubeDistance_contDiffAt z 0 2 (hcf 0 2 (by decide))).smul (by fun_prop)
  · change ContDiffAt ℝ 1 (fun w : Phase =>
      inverseCubeDistance w.1 1 0 • (w.1 0 - w.1 1) +
      inverseCubeDistance w.1 1 2 • (w.1 2 - w.1 1)) z
    apply ContDiffAt.add
    · exact (inverseCubeDistance_contDiffAt z 1 0 (hcf 1 0 (by decide))).smul (by fun_prop)
    · exact (inverseCubeDistance_contDiffAt z 1 2 (hcf 1 2 (by decide))).smul (by fun_prop)
  · change ContDiffAt ℝ 1 (fun w : Phase =>
      inverseCubeDistance w.1 2 0 • (w.1 0 - w.1 2) +
      inverseCubeDistance w.1 2 1 • (w.1 1 - w.1 2)) z
    apply ContDiffAt.add
    · exact (inverseCubeDistance_contDiffAt z 2 0 (hcf 2 0 (by decide))).smul (by fun_prop)
    · exact (inverseCubeDistance_contDiffAt z 2 1 (hcf 2 1 (by decide))).smul (by fun_prop)

/-- The unit Newton phase-space field is C1 on its regular domain. -/
theorem unitNewtonField_contDiffAt (z : Phase) (hcf : CollisionFree z.1) :
    ContDiffAt ℝ 1 (fun w : Phase => unitNewtonField w) z := by
  change ContDiffAt ℝ 1 (fun w : Phase =>
    (w.2, fun i => unitAcceleration w.1 i)) z
  apply ContDiffAt.prodMk
  · fun_prop
  · rw [contDiffAt_pi]
    intro i
    exact unitAcceleration_contDiffAt z hcf i

/-- Every collision-free phase is initial data for a local classical Newton
    solution. The interval is shrunk so that the Picard solution remains in
    the regular phase domain. -/
theorem exists_local_classicalNewtonSolution (z₀ : Phase)
    (hcf : CollisionFree z₀.1) :
    ∃ ε > 0, ∃ z : ℝ → Phase, z 0 = z₀ ∧
      ClassicalNewtonSolution z (Set.Ioo (-ε) ε) := by
  obtain ⟨α, hα₀, ε, hε, hderiv⟩ :=
    (unitNewtonField_contDiffAt z₀ hcf).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
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
      have htlo : -min ε δ < t := by simpa [ρ] using ht'.1
      have hthi : t < min ε δ := by simpa [ρ] using ht'.2
      constructor
      · linarith [min_le_left ε δ]
      · linarith [min_le_left ε δ]
    have hdist : dist t (0 : ℝ) < δ := by
      simpa only [Real.dist_eq, sub_zero] using
        (lt_of_lt_of_le (abs_lt.mpr (by simpa only [sub_zero] using ht'))
          (min_le_right ε δ))
    have hregular : α t ∈ regularPhaseSet := hball (by
      change dist t (0 : ℝ) < δ
      exact hdist)
    exact ⟨by simpa [regularPhaseSet] using hregular,
      hderiv t htin⟩

/-- Two classical Newton solutions with the same phase at an interior time
    agree on a neighborhood of that time. C1 regularity supplies a fixed
    local Lipschitz region for Mathlib's ODE uniqueness theorem. -/
theorem classicalNewton_local_unique_at
    {z w : ℝ → Phase} {I J : Set ℝ}
    (hz : ClassicalNewtonSolution z I) (hw : ClassicalNewtonSolution w J)
    (h0I : 0 ∈ I) (h0J : 0 ∈ J) (hinit : z 0 = w 0) :
    z =ᶠ[nhds (0 : ℝ)] w := by
  have hz0 := hz.2 0 h0I
  have hw0 := hw.2 0 h0J
  obtain ⟨K, U, hU, hLip⟩ :=
    (unitNewtonField_contDiffAt (z 0) hz0.1).exists_lipschitzOnWith
  obtain ⟨r, hr, hballU⟩ := Metric.mem_nhds_iff.mp hU
  let V : Set Phase := Metric.ball (z 0) r
  have hLipV : LipschitzOnWith K unitNewtonField V := by
    apply hLip.mono
    intro x hx
    exact hballU hx
  have hzIevent : I ∈ nhds (0 : ℝ) := hz.1.mem_nhds h0I
  have hwIevent : J ∈ nhds (0 : ℝ) := hw.1.mem_nhds h0J
  have hzVevent : ∀ᶠ t in nhds (0 : ℝ), z t ∈ V := by
    exact hz0.2.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (z 0) hr)
  have hwVevent : ∀ᶠ t in nhds (0 : ℝ), w t ∈ V := by
    have hcont := hw0.2.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (w 0) hr)
    change ∀ᶠ t in nhds (0 : ℝ), w t ∈ Metric.ball (w 0) r at hcont
    simpa [V, hinit] using hcont
  have hv : ∀ᶠ t in nhds (0 : ℝ),
      LipschitzOnWith K unitNewtonField V :=
    Filter.Eventually.of_forall fun _ => hLipV
  have hzevent : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt z (unitNewtonField (z t)) t ∧ z t ∈ V := by
    filter_upwards [hzIevent, hzVevent] with t htI htV
    exact ⟨(hz.2 t htI).2, htV⟩
  have hwevent : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt w (unitNewtonField (w t)) t ∧ w t ∈ V := by
    filter_upwards [hwIevent, hwVevent] with t htI htV
    exact ⟨(hw.2 t htI).2, htV⟩
  exact ODE_solution_unique_of_eventually hv hzevent hwevent hinit

/-- Local uniqueness at an arbitrary common interior time. This is the
    overlap lemma needed to glue solutions whose intervals are centered at
    different times. -/
theorem classicalNewton_local_unique_at_time
    {z w : ℝ → Phase} {I J : Set ℝ} {t₀ : ℝ}
    (hz : ClassicalNewtonSolution z I) (hw : ClassicalNewtonSolution w J)
    (h0I : t₀ ∈ I) (h0J : t₀ ∈ J) (hinit : z t₀ = w t₀) :
    z =ᶠ[nhds t₀] w := by
  have hz0 := hz.2 t₀ h0I
  have hw0 := hw.2 t₀ h0J
  obtain ⟨K, U, hU, hLip⟩ :=
    (unitNewtonField_contDiffAt (z t₀) hz0.1).exists_lipschitzOnWith
  obtain ⟨r, hr, hballU⟩ := Metric.mem_nhds_iff.mp hU
  let V : Set Phase := Metric.ball (z t₀) r
  have hLipV : LipschitzOnWith K unitNewtonField V := by
    apply hLip.mono
    intro x hx
    exact hballU hx
  have hzIevent : I ∈ nhds t₀ := hz.1.mem_nhds h0I
  have hwIevent : J ∈ nhds t₀ := hw.1.mem_nhds h0J
  have hzVevent : ∀ᶠ t in nhds t₀, z t ∈ V := by
    exact hz0.2.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (z t₀) hr)
  have hwVevent : ∀ᶠ t in nhds t₀, w t ∈ V := by
    have hcont := hw0.2.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (w t₀) hr)
    change ∀ᶠ t in nhds t₀, w t ∈ Metric.ball (w t₀) r at hcont
    simpa [V, hinit] using hcont
  have hv : ∀ᶠ t in nhds t₀,
      LipschitzOnWith K unitNewtonField V :=
    Filter.Eventually.of_forall fun _ => hLipV
  have hzevent : ∀ᶠ t in nhds t₀,
      HasDerivAt z (unitNewtonField (z t)) t ∧ z t ∈ V := by
    filter_upwards [hzIevent, hzVevent] with t htI htV
    exact ⟨(hz.2 t htI).2, htV⟩
  have hwevent : ∀ᶠ t in nhds t₀,
      HasDerivAt w (unitNewtonField (w t)) t ∧ w t ∈ V := by
    filter_upwards [hwIevent, hwVevent] with t htI htV
    exact ⟨(hw.2 t htI).2, htV⟩
  exact ODE_solution_unique_of_eventually hv hzevent hwevent hinit

/-- Local uniqueness propagates over a preconnected overlap: two classical
    Newton solutions that agree at one common time agree everywhere on the
    overlap. The equality predicate is locally constant, using ODE uniqueness
    at its true points and continuity at its false points. -/
theorem classicalNewton_eq_on_of_preconnected_overlap
    {z w : ℝ → Phase} {I J : Set ℝ} {t₀ : ℝ}
    (hz : ClassicalNewtonSolution z I) (hw : ClassicalNewtonSolution w J)
    (hconn : IsPreconnected (I ∩ J)) (ht₀ : t₀ ∈ I ∩ J)
    (hinit : z t₀ = w t₀) :
    ∀ t ∈ I ∩ J, z t = w t := by
  let S := {t : ℝ // t ∈ I ∩ J}
  let f : S → Bool := fun t => decide (z t.1 = w t.1)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hzX := hz.2 x.1 x.2.1
    have hwX := hw.2 x.1 x.2.2
    by_cases heq : z x.1 = w x.1
    · have hEq := classicalNewton_local_unique_at_time hz hw
        x.2.1 x.2.2 heq
      have hEqSub : ∀ᶠ y : S in 𝓝 x, z y.1 = w y.1 := by
        rw [nhds_subtype_eq_comap]
        exact hEq.comap Subtype.val
      filter_upwards [hEqSub] with y hy
      simp [f, heq, hy]
    · have hneOpen : IsOpen {p : Phase × Phase | p.1 ≠ p.2} :=
        isOpen_ne_fun continuous_fst continuous_snd
      have hpairCont : ContinuousAt (fun t : ℝ => (z t, w t)) x.1 :=
        hzX.2.continuousAt.prodMk hwX.2.continuousAt
      have hne : ∀ᶠ t in 𝓝 x.1, z t ≠ w t := by
        have hmem : (fun t : ℝ => (z t, w t)) ⁻¹'
            {p : Phase × Phase | p.1 ≠ p.2} ∈ 𝓝 x.1 :=
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
  have : f ⟨t, ht⟩ = true := by simpa [htrue] using hval.symm
  exact of_decide_eq_true this

end DroppingThreeBodies
