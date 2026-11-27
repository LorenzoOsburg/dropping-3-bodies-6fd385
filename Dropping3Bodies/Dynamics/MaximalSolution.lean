module

public import Dropping3Bodies.Dynamics.RegularDomain
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

/-!
# Union domain for centered local Newton solutions

This file begins the project-local maximal-solution construction. All local
solutions are taken on symmetric intervals about the same initial time, so
their domains are nested and their union remains an interval.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- A radius and trajectory witnessing a centered classical solution with the
    given initial phase. -/
def centeredClassicalNewtonWitnesses (z₀ : Phase) :
    Set (ℝ × (ℝ → Phase)) :=
  {p | 0 < p.1 ∧ p.2 0 = z₀ ∧
    ClassicalNewtonSolution p.2 (Set.Ioo (-p.1) p.1)}

/-- The union of all symmetric regular solution intervals for one initial
    phase. The compatibility lemma in `RegularDomain` will be used to define
    a single trajectory on this union. -/
def centeredClassicalNewtonUnionDomain (z₀ : Phase) : Set ℝ :=
  ⋃₀ {s : Set ℝ | ∃ p ∈ centeredClassicalNewtonWitnesses z₀,
    s = Set.Ioo (-p.1) p.1}

/-- Local existence makes the centered family of intervals nonempty. -/
theorem centeredClassicalNewtonWitnesses_nonempty (z₀ : Phase)
    (hcf : CollisionFree z₀.1) :
    (centeredClassicalNewtonWitnesses z₀).Nonempty := by
  obtain ⟨ε, hε, z, hz₀, hsol⟩ := exists_local_classicalNewtonSolution z₀ hcf
  exact ⟨(ε, z), ⟨hε, hz₀, hsol⟩⟩

/-- The union domain is open. -/
theorem isOpen_centeredClassicalNewtonUnionDomain (z₀ : Phase) :
    IsOpen (centeredClassicalNewtonUnionDomain z₀) := by
  unfold centeredClassicalNewtonUnionDomain
  apply isOpen_sUnion
  rintro s ⟨r, hr, rfl⟩
  exact isOpen_Ioo

/-- The union domain is preconnected because every interval in the family
    contains the common initial time zero. -/
theorem isPreconnected_centeredClassicalNewtonUnionDomain (z₀ : Phase) :
    IsPreconnected (centeredClassicalNewtonUnionDomain z₀) := by
  unfold centeredClassicalNewtonUnionDomain
  apply isPreconnected_sUnion 0
  · rintro s ⟨p, hp, rfl⟩
    exact ⟨neg_neg_of_pos hp.1, hp.1⟩
  · rintro s ⟨p, hp, rfl⟩
    exact isPreconnected_Ioo

/-- Every point in the union is covered by at least one centered local
    solution interval with the prescribed initial phase. -/
theorem centeredClassicalNewtonUnionDomain_covered
    (z₀ : Phase) {t : ℝ}
    (ht : t ∈ centeredClassicalNewtonUnionDomain z₀) :
    ∃ r : ℝ, ∃ z : ℝ → Phase,
      0 < r ∧ t ∈ Set.Ioo (-r) r ∧ z 0 = z₀ ∧
        ClassicalNewtonSolution z (Set.Ioo (-r) r) := by
  rcases Set.mem_sUnion.mp ht with ⟨s, hs, ht⟩
  rcases hs with ⟨p, hp, rfl⟩
  exact ⟨p.1, p.2, hp.1, ht, hp.2.1, hp.2.2⟩

/-- Every centered solution interval is included in the union domain. -/
theorem centeredClassicalNewtonWitness_interval_subset
    (z₀ : Phase) {p : ℝ × (ℝ → Phase)}
    (hp : p ∈ centeredClassicalNewtonWitnesses z₀) :
    Set.Ioo (-p.1) p.1 ⊆ centeredClassicalNewtonUnionDomain z₀ := by
  intro t ht
  exact Set.mem_sUnion.mpr ⟨Set.Ioo (-p.1) p.1, ⟨p, hp, rfl⟩, ht⟩

/-- A covering witness can be chosen at every time in the union domain. -/
theorem centeredClassicalNewtonUnionDomain_chooseWitness
    (z₀ : Phase) {t : ℝ}
    (ht : t ∈ centeredClassicalNewtonUnionDomain z₀) :
    ∃ p : ℝ × (ℝ → Phase),
      p ∈ centeredClassicalNewtonWitnesses z₀ ∧
        t ∈ Set.Ioo (-p.1) p.1 := by
  obtain ⟨r, z, hr, htI, hz₀, hsol⟩ :=
    centeredClassicalNewtonUnionDomain_covered z₀ ht
  exact ⟨(r, z), ⟨hr, hz₀, hsol⟩, htI⟩

/-- The selected local solution witness covering a given point of the union. -/
noncomputable def centeredClassicalNewtonChosenWitness
    (z₀ : Phase) (t : ℝ)
    (ht : t ∈ centeredClassicalNewtonUnionDomain z₀) :
    ℝ × (ℝ → Phase) :=
  Classical.choose (centeredClassicalNewtonUnionDomain_chooseWitness z₀ ht)

theorem centeredClassicalNewtonChosenWitness_spec
    (z₀ : Phase) (t : ℝ)
    (ht : t ∈ centeredClassicalNewtonUnionDomain z₀) :
    centeredClassicalNewtonChosenWitness z₀ t ht ∈
      centeredClassicalNewtonWitnesses z₀ ∧
      t ∈ Set.Ioo
        (-(centeredClassicalNewtonChosenWitness z₀ t ht).1)
        (centeredClassicalNewtonChosenWitness z₀ t ht).1 :=
  Classical.choose_spec (centeredClassicalNewtonUnionDomain_chooseWitness z₀ ht)

/-- Choose a local trajectory at each time. The compatibility theorem proved
    below makes this pointwise choice independent of which witness covers the
    nearby time. -/
noncomputable def centeredClassicalNewtonUnionTrajectory
    (z₀ : Phase) (t : ℝ) : Phase :=
  by
    classical
    exact if ht : t ∈ centeredClassicalNewtonUnionDomain z₀ then
      (centeredClassicalNewtonChosenWitness z₀ t ht).2 t
    else z₀

/-- The intersection of two centered open intervals is preconnected. -/
theorem isPreconnected_inter_centeredIntervals (r s : ℝ) :
    IsPreconnected
      (Set.Ioo (-r) r ∩ Set.Ioo (-s) s) := by
  exact (Convex.inter (convex_Ioo (-r) r) (convex_Ioo (-s) s)).isPreconnected

/-- Around any point of the union, the selected trajectory agrees with one
    fixed local solution. -/
theorem centeredClassicalNewtonUnionTrajectory_eventuallyEq_chosen
    (z₀ : Phase) (t : ℝ)
    (ht : t ∈ centeredClassicalNewtonUnionDomain z₀) :
    centeredClassicalNewtonUnionTrajectory z₀ =ᶠ[𝓝 t]
      (centeredClassicalNewtonChosenWitness z₀ t ht).2 := by
  let p := centeredClassicalNewtonChosenWitness z₀ t ht
  have hp := centeredClassicalNewtonChosenWitness_spec z₀ t ht
  have hDopen := isOpen_centeredClassicalNewtonUnionDomain z₀
  have htD : centeredClassicalNewtonUnionDomain z₀ ∈ 𝓝 t := hDopen.mem_nhds ht
  have htP : Set.Ioo (-p.1) p.1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds hp.2
  filter_upwards [htD, htP] with s hsD hsP
  have hsChosen := centeredClassicalNewtonChosenWitness_spec z₀ s hsD
  have hsSol : ClassicalNewtonSolution (centeredClassicalNewtonChosenWitness z₀ s hsD).2
      (Set.Ioo
        (-(centeredClassicalNewtonChosenWitness z₀ s hsD).1)
        (centeredClassicalNewtonChosenWitness z₀ s hsD).1) :=
    (hsChosen.1.2.2)
  have hpSol : ClassicalNewtonSolution p.2 (Set.Ioo (-p.1) p.1) := hp.1.2.2
  have hinit : p.2 0 =
      (centeredClassicalNewtonChosenWitness z₀ s hsD).2 0 :=
    hp.1.2.1.trans hsChosen.1.2.1.symm
  have hzero : (0 : ℝ) ∈ Set.Ioo (-p.1) p.1 ∩
      Set.Ioo
        (-(centeredClassicalNewtonChosenWitness z₀ s hsD).1)
        (centeredClassicalNewtonChosenWitness z₀ s hsD).1 := by
    constructor
    · exact ⟨neg_neg_of_pos hp.1.1, hp.1.1⟩
    · exact ⟨neg_neg_of_pos hsChosen.1.1, hsChosen.1.1⟩
  have hoverlap := classicalNewton_eq_on_of_preconnected_overlap
    hpSol hsSol (isPreconnected_inter_centeredIntervals p.1
      (centeredClassicalNewtonChosenWitness z₀ s hsD).1)
    hzero hinit
  have hsOverlap : s ∈ Set.Ioo (-p.1) p.1 ∩
      Set.Ioo
        (-(centeredClassicalNewtonChosenWitness z₀ s hsD).1)
        (centeredClassicalNewtonChosenWitness z₀ s hsD).1 :=
    ⟨hsP, hsChosen.2⟩
  have heq := hoverlap s hsOverlap
  have htrajectory : centeredClassicalNewtonUnionTrajectory z₀ s =
      (centeredClassicalNewtonChosenWitness z₀ s hsD).2 s := by
    unfold centeredClassicalNewtonUnionTrajectory
    rw [dif_pos hsD]
  rw [htrajectory, heq]

theorem centeredClassicalNewtonUnionTrajectory_solution
    (z₀ : Phase) :
    ClassicalNewtonSolution (centeredClassicalNewtonUnionTrajectory z₀)
      (centeredClassicalNewtonUnionDomain z₀) := by
  refine ⟨isOpen_centeredClassicalNewtonUnionDomain z₀, ?_⟩
  intro t ht
  let p := centeredClassicalNewtonChosenWitness z₀ t ht
  have hp := centeredClassicalNewtonChosenWitness_spec z₀ t ht
  have hsol : ClassicalNewtonSolution p.2 (Set.Ioo (-p.1) p.1) := hp.1.2.2
  have htP : t ∈ Set.Ioo (-p.1) p.1 := hp.2
  have hcollision : CollisionFree (p.2 t).1 := (hsol.2 t htP).1
  have hvalue : centeredClassicalNewtonUnionTrajectory z₀ t = p.2 t := by
    unfold centeredClassicalNewtonUnionTrajectory
    rw [dif_pos ht]
  constructor
  · rw [hvalue]
    exact hcollision
  · have hD := (hsol.2 t htP).2
    have hevent := centeredClassicalNewtonUnionTrajectory_eventuallyEq_chosen z₀ t ht
    have hderiv := hD.congr_of_eventuallyEq hevent
    have hvalue' : centeredClassicalNewtonUnionTrajectory z₀ t = p.2 t := hvalue
    simpa [hvalue'] using hderiv

/-- The selected union trajectory has the prescribed initial phase. -/
theorem centeredClassicalNewtonUnionTrajectory_initial
    (z₀ : Phase) (hcf : CollisionFree z₀.1) :
    centeredClassicalNewtonUnionTrajectory z₀ 0 = z₀ := by
  obtain ⟨p, hp⟩ := centeredClassicalNewtonWitnesses_nonempty z₀ hcf
  have hzeroP : (0 : ℝ) ∈ Set.Ioo (-p.1) p.1 :=
    ⟨neg_neg_of_pos hp.1, hp.1⟩
  have hzeroD := centeredClassicalNewtonWitness_interval_subset z₀ hp hzeroP
  have hchosen := centeredClassicalNewtonChosenWitness_spec z₀ 0 hzeroD
  have hvalue : centeredClassicalNewtonUnionTrajectory z₀ 0 =
      (centeredClassicalNewtonChosenWitness z₀ 0 hzeroD).2 0 := by
    unfold centeredClassicalNewtonUnionTrajectory
    rw [dif_pos hzeroD]
  rw [hvalue]
  exact hchosen.1.2.1

end

end DroppingThreeBodies
