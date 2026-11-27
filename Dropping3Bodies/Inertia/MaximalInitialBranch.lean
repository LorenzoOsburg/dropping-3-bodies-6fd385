module

public import Dropping3Bodies.Adapters.NBody
public import Dropping3Bodies.Inertia.InitialBranchFiniteness
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# The paper's initial noncollinear endpoint on the maximal Newton solution

The domain and trajectory below specialize the existing NBody union over all
classical solution intervals through the initial phase. The endpoint is the
supremum of the initial noncollinear branch on that domain, not the supremum
of the whole maximal solution domain.
-/

namespace DroppingThreeBodies

noncomputable section

/-- The full collision-free solution domain through `z₀` at time zero. -/
def generalMaximalNewtonDomain (G : ℝ) (m : Fin 3 → ℝ) (z₀ : Phase) : Set ℝ :=
  NBody.maximalUnionDomain (NBody.regularPhaseSet (Fin 3) 2)
    (NBody.vectorField G m) z₀ 0

/-- The compatible union trajectory on the full maximal domain. -/
def generalMaximalNewtonTrajectory (G : ℝ) (m : Fin 3 → ℝ) (z₀ : Phase) : ℝ → Phase :=
  NBody.maximalUnionTrajectory (NBody.regularPhaseSet (Fin 3) 2)
    (NBody.vectorField G m) z₀ 0

/-- `T_*` in Theorem 2.1: the supremum of the initial noncollinear branch
of the maximal classical collision-free solution. -/
def maximalInitialNoncollinearEndpoint (G : ℝ) (m : Fin 3 → ℝ) (z₀ : Phase) : ℝ :=
  sSup (BeforeFirstCollinearity (generalMaximalNewtonTrajectory G m z₀)
    (generalMaximalNewtonDomain G m z₀) 0)

/-- Noncollinearity already implies collision-freedom for three bodies. -/
theorem collisionFree_of_signedDoubleArea_ne_zero
    {q : Fin 3 → Point} (harea : signedDoubleArea q ≠ 0) : CollisionFree q := by
  intro i j hij heq
  fin_cases i <;> fin_cases j <;>
    simp_all [signedDoubleArea, cross] <;> ring_nf at harea <;> contradiction

/-- The union construction satisfies the arbitrary-mass Newton equation. -/
theorem generalMaximalNewtonTrajectory_solution (G : ℝ) (m : Fin 3 → ℝ) (z₀ : Phase) :
    GeneralClassicalNewtonSolution G m (generalMaximalNewtonTrajectory G m z₀)
      (generalMaximalNewtonDomain G m z₀) := by
  apply (nbody_classicalSolution_iff_generalClassicalNewtonSolution _ _ _ _).mp
  exact NBody.maximalUnionTrajectory_solution
    (fun z hz => NBody.vectorField_contDiffAt G m z hz)

theorem generalMaximalNewtonDomain_isPreconnected (G : ℝ) (m : Fin 3 → ℝ) (z₀ : Phase) :
    IsPreconnected (generalMaximalNewtonDomain G m z₀) :=
  NBody.isPreconnected_maximalUnionDomain _ _ _ _

theorem generalMaximalNewtonDomain_initial_mem
    (G : ℝ) (m : Fin 3 → ℝ) {z₀ : Phase} (hcf : CollisionFree z₀.1) :
    (0 : ℝ) ∈ generalMaximalNewtonDomain G m z₀ := by
  obtain ⟨w⟩ := NBody.exists_initialIntervalWitness
    (NBody.isOpen_regularPhaseSet (ι := Fin 3) 2)
    (show z₀ ∈ NBody.regularPhaseSet (Fin 3) 2 from hcf)
    (NBody.vectorField_contDiffAt G m z₀ hcf) 0
  exact NBody.initialWitness_interval_subset w ⟨w.left_lt, w.lt_right⟩

theorem generalMaximalNewtonTrajectory_initial
    (G : ℝ) (m : Fin 3 → ℝ) {z₀ : Phase} (hcf : CollisionFree z₀.1) :
    generalMaximalNewtonTrajectory G m z₀ 0 = z₀ :=
  NBody.maximalUnionTrajectory_initial
    (NBody.isOpen_regularPhaseSet (ι := Fin 3) 2)
    (show z₀ ∈ NBody.regularPhaseSet (Fin 3) 2 from hcf)
    (NBody.vectorField_contDiffAt G m z₀ hcf)

/-- The domain is not a chosen local interval: it contains every classical
open solution interval with these initial data, by the existing union contract. -/
theorem generalMaximalNewtonDomain_contains_initialInterval
    {G : ℝ} {m : Fin 3 → ℝ} {z₀ : Phase} {z : ℝ → Phase} {l r : ℝ}
    (hl : l < 0) (hr : 0 < r) (hinit : z 0 = z₀)
    (hsol : GeneralClassicalNewtonSolution G m z (Set.Ioo l r)) :
    Set.Ioo l r ⊆ generalMaximalNewtonDomain G m z₀ := by
  let w : NBody.InitialIntervalWitness (NBody.regularPhaseSet (Fin 3) 2)
      (NBody.vectorField G m) z₀ 0 :=
    ⟨l, r, z, hl, hr, hinit,
      (nbody_classicalSolution_iff_generalClassicalNewtonSolution _ _ _ _).mpr hsol⟩
  exact NBody.initialWitness_interval_subset w

/-- Continuity gives a genuinely later initial-branch time, without any
assumption about a first syzygy or the maximal lifetime. -/
theorem generalNewton_exists_pos_mem_initialBranch
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hzero : (0 : ℝ) ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : signedDoubleArea (z 0).1 ≠ 0) :
    ∃ t > 0, t ∈ BeforeFirstCollinearity z I 0 := by
  have hcont := (generalNewton_signedDoubleArea_deriv hsol hzero hm0 hm1 hm2 harea).continuousAt
  have hnhds : {s | s ∈ I ∧ signedDoubleArea (z s).1 ≠ 0} ∈ nhds (0 : ℝ) :=
    Filter.inter_mem (hsol.1.mem_nhds hzero) (hcont.eventually_ne harea)
  obtain ⟨l, r, hzeroLR, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  refine ⟨r / 2, by linarith [hzeroLR.2], ?_⟩
  have hseg : ∀ s ∈ Set.Icc 0 (r / 2), s ∈ I ∧ signedDoubleArea (z s).1 ≠ 0 := by
    intro s hs
    exact hsub ⟨by linarith [hzeroLR.1, hs.1], by linarith [hzeroLR.2, hs.2]⟩
  exact ⟨by linarith [hzeroLR.2], fun s hs => (hseg s hs).1,
    fun s hs => (hseg s hs).2⟩

/-- Theorem 2.1's positive finite `T_*`, with only physical initial
assumptions. `IsLUB` asserts that the real supremum is a genuine least upper
bound, rather than relying on the totalized value of real `sSup`. -/
theorem generalNewton_maximal_initialBranch_endpoint_pos_finite
    {G : ℝ} {m : Fin 3 → ℝ} {z₀ : Phase}
    (hm : ∀ i, 0 < m i) (hG : 0 < G)
    (harea : signedDoubleArea z₀.1 ≠ 0) (hrest : ∀ i, z₀.2 i = 0) :
    let S := BeforeFirstCollinearity (generalMaximalNewtonTrajectory G m z₀)
      (generalMaximalNewtonDomain G m z₀) 0
    S.Nonempty ∧ BddAbove S ∧ IsLUB S (maximalInitialNoncollinearEndpoint G m z₀) ∧
      0 < maximalInitialNoncollinearEndpoint G m z₀ ∧
      (maximalInitialNoncollinearEndpoint G m z₀ : EReal) < ⊤ := by
  let z := generalMaximalNewtonTrajectory G m z₀
  let I := generalMaximalNewtonDomain G m z₀
  have hcf := collisionFree_of_signedDoubleArea_ne_zero harea
  have hsol := generalMaximalNewtonTrajectory_solution G m z₀
  have hconn := generalMaximalNewtonDomain_isPreconnected G m z₀
  have hzero := generalMaximalNewtonDomain_initial_mem G m hcf
  have hinit := generalMaximalNewtonTrajectory_initial G m hcf
  have harea' : signedDoubleArea (z 0).1 ≠ 0 := by simpa [z, hinit] using harea
  have hrest' : ∀ i, (z 0).2 i = 0 := by simpa [z, hinit] using hrest
  obtain ⟨t, htpos, ht⟩ := generalNewton_exists_pos_mem_initialBranch hsol hzero
    (hm 0) (hm 1) (hm 2) harea'
  have hbdd := generalNewton_initialBranch_bddAbove hsol hconn hzero
    (hm 0) (hm 1) (hm 2) hG harea' hrest'
  exact ⟨⟨t, ht⟩, hbdd, isLUB_csSup ⟨t, ht⟩ hbdd,
    htpos.trans_le (le_csSup hbdd ht), EReal.coe_lt_top _⟩

end

end DroppingThreeBodies
