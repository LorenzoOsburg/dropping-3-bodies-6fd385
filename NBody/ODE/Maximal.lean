module

public import NBody.ODE.LocalTheory
public import Mathlib.Analysis.Convex.PathConnected
public import PrincipiaThreeBodies.Definitions

@[expose] public section

namespace NBody

open Filter
open scoped Topology

noncomputable section

theorem exists_initialIntervalWitness {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Ω : Set E} {X : E → E} {x₀ : E}
    (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω) (hX : ContDiffAt ℝ 1 X x₀) (a : ℝ) :
    Nonempty (InitialIntervalWitness Ω X x₀ a) := by
  obtain ⟨ε, hε, z, hz, hsol⟩ := exists_local_solutionOn hΩ hx₀ hX a
  exact ⟨⟨a - ε, a + ε, z, by linarith, by linarith, hz, hsol⟩⟩

theorem isOpen_maximalUnionDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (x₀ : E) (a : ℝ) :
    IsOpen (maximalUnionDomain Ω X x₀ a) := by
  unfold maximalUnionDomain
  apply isOpen_sUnion
  rintro s ⟨w, rfl⟩
  exact isOpen_Ioo

theorem isPreconnected_maximalUnionDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (x₀ : E) (a : ℝ) :
    IsPreconnected (maximalUnionDomain Ω X x₀ a) := by
  unfold maximalUnionDomain
  apply isPreconnected_sUnion a
  · rintro s ⟨w, rfl⟩
    exact ⟨w.left_lt, w.lt_right⟩
  · rintro s ⟨w, rfl⟩
    exact isPreconnected_Ioo

theorem maximalChosenWitness_spec {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (x₀ : E) (a t : ℝ)
    (ht : t ∈ maximalUnionDomain Ω X x₀ a) :
    t ∈ Set.Ioo (maximalChosenWitness Ω X x₀ a t ht).left
      (maximalChosenWitness Ω X x₀ a t ht).right :=
  Classical.choose_spec (maximalUnionDomain_covered Ω X x₀ a t ht)

theorem isPreconnected_inter_openIntervals (a b c d : ℝ) :
    IsPreconnected (Set.Ioo a b ∩ Set.Ioo c d) :=
  (Convex.inter (convex_Ioo a b) (convex_Ioo c d)).isPreconnected

/-- A chosen representative agrees locally with the union trajectory; the
overlap theorem makes the pointwise choice independent of the representative. -/
theorem maximalUnionTrajectory_eventuallyEq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [T2Space E]
    {Ω : Set E} {X : E → E} {x₀ : E} {a t : ℝ}
    (hX : ∀ x ∈ Ω, ContDiffAt ℝ 1 X x)
    (ht : t ∈ maximalUnionDomain Ω X x₀ a) :
    maximalUnionTrajectory Ω X x₀ a =ᶠ[𝓝 t]
      (maximalChosenWitness Ω X x₀ a t ht).trajectory := by
  let w := maximalChosenWitness Ω X x₀ a t ht
  have htW := maximalChosenWitness_spec Ω X x₀ a t ht
  have htD : maximalUnionDomain Ω X x₀ a ∈ 𝓝 t :=
    (isOpen_maximalUnionDomain Ω X x₀ a).mem_nhds ht
  have htWnhds : Set.Ioo w.left w.right ∈ 𝓝 t := isOpen_Ioo.mem_nhds htW
  filter_upwards [htD, htWnhds] with s hsD hsW
  let v := maximalChosenWitness Ω X x₀ a s hsD
  have hsV := maximalChosenWitness_spec Ω X x₀ a s hsD
  have hinit : w.trajectory a = v.trajectory a := w.initial.trans v.initial.symm
  have ha : a ∈ Set.Ioo w.left w.right ∩ Set.Ioo v.left v.right :=
    ⟨⟨w.left_lt, w.lt_right⟩, ⟨v.left_lt, v.lt_right⟩⟩
  have hoverlap := solutions_eqOn_of_preconnected_overlap
    w.solution v.solution hX (isPreconnected_inter_openIntervals w.left w.right v.left v.right)
    ha hinit
  have hsOverlap : s ∈ Set.Ioo w.left w.right ∩ Set.Ioo v.left v.right := ⟨hsW, hsV⟩
  have heq := hoverlap s hsOverlap
  have htrajectory : maximalUnionTrajectory Ω X x₀ a s = v.trajectory s := by
    unfold maximalUnionTrajectory
    rw [dif_pos hsD]
  rw [htrajectory, heq]

theorem maximalUnionTrajectory_solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [T2Space E]
    {Ω : Set E} {X : E → E} {x₀ : E} {a : ℝ}
    (hX : ∀ x ∈ Ω, ContDiffAt ℝ 1 X x) :
    SolutionOn Ω X (maximalUnionTrajectory Ω X x₀ a)
      (maximalUnionDomain Ω X x₀ a) := by
  classical
  refine ⟨isOpen_maximalUnionDomain Ω X x₀ a, ?_⟩
  intro t ht
  let w := maximalChosenWitness Ω X x₀ a t ht
  have htW := maximalChosenWitness_spec Ω X x₀ a t ht
  have hvalue : maximalUnionTrajectory Ω X x₀ a t = w.trajectory t := by
    unfold maximalUnionTrajectory
    rw [dif_pos ht]
  have hdata := w.solution.2 t htW
  have hderiv := hdata.2.congr_of_eventuallyEq
    (maximalUnionTrajectory_eventuallyEq hX ht)
  exact ⟨by simpa [hvalue] using hdata.1, by simpa [hvalue] using hderiv⟩

theorem maximalUnionTrajectory_initial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Ω : Set E} {X : E → E} {x₀ : E} {a : ℝ}
    (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω) (hX : ContDiffAt ℝ 1 X x₀) :
    maximalUnionTrajectory Ω X x₀ a a = x₀ := by
  obtain ⟨w⟩ := exists_initialIntervalWitness hΩ hx₀ hX a
  have haW : a ∈ Set.Ioo w.left w.right := ⟨w.left_lt, w.lt_right⟩
  have haD : a ∈ maximalUnionDomain Ω X x₀ a :=
    Set.mem_sUnion.mpr ⟨Set.Ioo w.left w.right, ⟨w, rfl⟩, haW⟩
  have haChosen := maximalChosenWitness_spec Ω X x₀ a a haD
  have hvalue : maximalUnionTrajectory Ω X x₀ a a =
      (maximalChosenWitness Ω X x₀ a a haD).trajectory a := by
    unfold maximalUnionTrajectory
    rw [dif_pos haD]
  rw [hvalue]
  exact (maximalChosenWitness Ω X x₀ a a haD).initial

/-- Every solution interval with the same initial data is contained in the
union domain; this is the domain-maximality contract of the construction. -/
theorem initialWitness_interval_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω : Set E} {X : E → E} {x₀ : E} {a : ℝ}
    (w : InitialIntervalWitness Ω X x₀ a) :
    Set.Ioo w.left w.right ⊆ maximalUnionDomain Ω X x₀ a := by
  intro t ht
  exact Set.mem_sUnion.mpr ⟨Set.Ioo w.left w.right, ⟨w, rfl⟩, ht⟩

end

end NBody
