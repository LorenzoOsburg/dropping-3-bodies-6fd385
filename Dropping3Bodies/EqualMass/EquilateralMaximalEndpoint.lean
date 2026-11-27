module

public import Dropping3Bodies.Dynamics.Homothetic
public import Dropping3Bodies.Dynamics.MaximalInterval
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-! # Equilateral triple collapse at the maximal right endpoint

The explicit homothetic solution agrees with the maximal Newton trajectory
throughout the pre-collapse interval. Its centroid limit excludes a regular
maximal-domain point at or beyond the collapse time.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- A nondegenerate equilateral configuration has nonzero signed area. -/
theorem equilateral_signedDoubleArea_ne_zero
    (q : Fin 3 → Point) (d : ℝ) (hd : 0 < d)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d) :
    signedDoubleArea q ≠ 0 := by
  intro harea
  have hcf := collisionFree_of_equilateral q d hd h01 h02 h12
  have hlongPrev : dist (q (cyclicPrev (0 : Fin 3)))
      (q (cyclicNext 0)) ^ 2 ≥ dist (q 0) (q (cyclicPrev 0)) ^ 2 := by
    simp only [cyclicPrev, cyclicNext]
    rw [dist_comm, h12, h02]
  have hlongNext : dist (q (cyclicPrev (0 : Fin 3)))
      (q (cyclicNext 0)) ^ 2 ≥ dist (q (cyclicNext 0)) (q 0) ^ 2 := by
    simp only [cyclicPrev, cyclicNext]
    rw [dist_comm (q 2) (q 1), h12, dist_comm (q 1) (q 0), h01]
  have hbtw := sbtw_of_longest_opposite_side q 0 harea hcf hlongPrev hlongNext
  have hdist := (dist_add_dist_eq_iff).2 hbtw.wbtw
  simp only [cyclicPrev, cyclicNext] at hdist
  rw [dist_comm (q 2) (q 0), h02, dist_comm (q 2) (q 1), h12] at hdist
  nlinarith [hd]

/-- The maximal trajectory from arbitrary equilateral rest data is exactly the
explicit homothetic trajectory before collapse. Its forward domain ends at
the triple-collision time, no regular syzygy occurs before then, and every
pair distance tends to zero at the maximal right endpoint. -/
theorem exists_equilateral_maximal_drop
    (q : Fin 3 → Point) (d : ℝ) (hd : 0 < d)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d) :
    ∃ K : ℝ, ∃ hK : 0 < K,
      let z₀ : Phase := (q, fun _ : Fin 3 => (0 : Point))
      let T := homotheticCollapseTime K
      (∀ t, 0 ≤ t → t < T →
        maximalNewtonUnionTrajectory z₀ t = homotheticPhase q K hK t) ∧
      (∀ t, 0 ≤ t →
        (t ∈ maximalNewtonUnionDomain z₀ ↔ t < T)) ∧
      (∀ t, 0 ≤ t → t < T →
        signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 ≠ 0) ∧
      (∀ i j : Fin 3,
        Tendsto (fun t => dist ((maximalNewtonUnionTrajectory z₀ t).1 i)
          ((maximalNewtonUnionTrajectory z₀ t).1 j))
          (𝓝[<] T) (𝓝 0)) := by
  obtain ⟨K, hK, hsolH, hphase0, hTpos, hcollapse⟩ :=
    exists_homothetic_equilateral_drop q d hd h01 h02 h12
  let z₀ : Phase := (q, fun _ : Fin 3 => (0 : Point))
  let T := homotheticCollapseTime K
  let L := homotheticTimeParameter K (-(Real.pi / 4))
  have hrightEq : homotheticTimeParameter K (Real.pi / 2) = T := by
    exact homotheticTimeParameter_right_eq_collapseTime K
  have hleftNeg : L < 0 := (homotheticTimeParameter_left_lt_zero_right K hK).1
  have h0T : 0 < T := by simpa [T] using hTpos
  have hleftLT : L < T := by
    rw [← hrightEq]
    exact (homotheticTimeParameter_left_lt_zero_right K hK).1.trans
      (homotheticTimeParameter_left_lt_zero_right K hK).2
  have hphase0' : homotheticPhase q K hK 0 = z₀ := by
    simpa [z₀] using hphase0
  have hsolLeftRight : ClassicalNewtonSolution (homotheticPhase q K hK)
      (Set.Ioo L T) := by
    simpa [L, T, homotheticSolutionInterval, hrightEq] using hsolH
  let w : NewtonInitialIntervalWitness z₀ :=
    ⟨L, T, homotheticPhase q K hK, hleftNeg, h0T, hphase0', hsolLeftRight⟩
  have hJsub : Set.Ioo L T ⊆ maximalNewtonUnionDomain z₀ :=
    maximalNewtonWitness_interval_subset z₀ w
  have hsolM : ClassicalNewtonSolution (maximalNewtonUnionTrajectory z₀)
      (maximalNewtonUnionDomain z₀) := maximalNewtonUnionTrajectory_solution z₀
  have hinitM : maximalNewtonUnionTrajectory z₀ 0 = z₀ :=
    maximalNewtonUnionTrajectory_initial z₀ (collisionFree_of_equilateral q d hd h01 h02 h12)
  have hzeroD : (0 : ℝ) ∈ maximalNewtonUnionDomain z₀ := by
    obtain ⟨w₀⟩ := exists_newtonInitialIntervalWitness z₀
      (collisionFree_of_equilateral q d hd h01 h02 h12)
    exact maximalNewtonWitness_interval_subset z₀ w₀
      ⟨w₀.left_lt_zero, w₀.zero_lt_right⟩
  have hzeroJ : (0 : ℝ) ∈ Set.Ioo L T := ⟨hleftNeg, h0T⟩
  have hinter : maximalNewtonUnionDomain z₀ ∩ Set.Ioo L T = Set.Ioo L T :=
    Set.inter_eq_right.mpr hJsub
  have hconn : IsPreconnected (maximalNewtonUnionDomain z₀ ∩ Set.Ioo L T) := by
    rw [hinter]
    exact isPreconnected_Ioo
  have hinitH : maximalNewtonUnionTrajectory z₀ 0 = homotheticPhase q K hK 0 := by
    rw [hinitM, hphase0']
  have hagreeOn : ∀ t ∈ Set.Ioo L T,
      maximalNewtonUnionTrajectory z₀ t = homotheticPhase q K hK t := by
    have hEq := classicalNewton_eq_on_of_preconnected_overlap hsolM hsolLeftRight
      hconn ⟨hzeroD, hzeroJ⟩ hinitH
    intro t ht
    exact hEq t ⟨hJsub ht, ht⟩
  have hagree : ∀ t, 0 ≤ t → t < T →
      maximalNewtonUnionTrajectory z₀ t = homotheticPhase q K hK t := by
    intro t ht0 htT
    apply hagreeOn t
    exact ⟨lt_of_lt_of_le hleftNeg ht0, htT⟩
  have hleftEvent : ∀ᶠ t in 𝓝[<] T, t ∈ Set.Ioo L T := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds hleftLT]
      with t hLt htT
    exact ⟨hLt, htT⟩
  have harea0 : signedDoubleArea q ≠ 0 :=
    equilateral_signedDoubleArea_ne_zero q d hd h01 h02 h12
  have hnoSyzygy : ∀ t, 0 ≤ t → t < T →
      signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 ≠ 0 := by
    intro t ht0 htT
    rw [hagree t ht0 htT]
    have htJ : t ∈ Set.Ioo L (homotheticTimeParameter K (Real.pi / 2)) := by
      rw [hrightEq]
      exact ⟨lt_of_lt_of_le hleftNeg ht0, htT⟩
    exact signedDoubleArea_ne_zero_homotheticConfiguration q K hK
      htJ harea0
  have hnoT : T ∉ maximalNewtonUnionDomain z₀ := by
    intro hTD
    have hposLimit (i : Fin 3) :
        Tendsto (fun t => (maximalNewtonUnionTrajectory z₀ t).1 i)
          (𝓝[<] T) (𝓝 ((maximalNewtonUnionTrajectory z₀ T).1 i)) := by
      have hderiv := classicalNewton_body_vector_derivatives i hsolM hTD
      exact hderiv.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hposEq (i : Fin 3) :
        (fun t => (maximalNewtonUnionTrajectory z₀ t).1 i) =ᶠ[𝓝[<] T]
          (fun t => homotheticConfiguration q K hK t i) := by
      filter_upwards [hleftEvent] with t ht
      have heq := hagreeOn t ht
      exact congrArg (fun z : Phase => z.1 i) heq
    have hposHom (i : Fin 3) :
        Tendsto (fun t => homotheticConfiguration q K hK t i)
          (𝓝[<] T) (𝓝 (configurationCentroid q)) := by
      have h := tendsto_homotheticConfiguration_collapseTime q K hK i
      simpa [T] using h.mono_left nhdsWithin_le_nhds
    have hcenterAt (i : Fin 3) :
        (maximalNewtonUnionTrajectory z₀ T).1 i = configurationCentroid q :=
      tendsto_nhds_unique ((hposLimit i).congr' (hposEq i)) (hposHom i)
    have hcfT := (hsolM.2 T hTD).1
    have hdist := (collisionFree_iff_dist_pos _).mp hcfT 0 1 (by decide)
    rw [hcenterAt 0, hcenterAt 1] at hdist
    simp at hdist
  have hforward : ∀ t, 0 ≤ t →
      (t ∈ maximalNewtonUnionDomain z₀ ↔ t < T) := by
    intro t ht0
    constructor
    · intro htD
      by_contra hnot
      have hTle : T ≤ t := le_of_not_gt hnot
      have hsegment := (isPreconnected_maximalNewtonUnionDomain z₀).Icc_subset hzeroD htD
      exact hnoT (hsegment ⟨le_of_lt h0T, hTle⟩)
    · intro htT
      exact hJsub ⟨lt_of_lt_of_le hleftNeg ht0, htT⟩
  have hdistances (i j : Fin 3) :
      Tendsto (fun t => dist ((maximalNewtonUnionTrajectory z₀ t).1 i)
        ((maximalNewtonUnionTrajectory z₀ t).1 j)) (𝓝[<] T) (𝓝 0) := by
    have hhom : Tendsto (fun t => dist (homotheticConfiguration q K hK t i)
        (homotheticConfiguration q K hK t j)) (𝓝[<] T) (𝓝 0) := by
      have hscale := tendsto_homotheticScaleFromTime_collapseTime K hK
      have hmul0 := hscale.mul_const (dist (q i) (q j))
      have hmul : Tendsto (fun t => homotheticScaleFromTime K hK t * dist (q i) (q j))
          (𝓝[<] T) (𝓝 0) := by
        change Tendsto _
          (𝓝[Set.Iio (homotheticCollapseTime K)] (homotheticCollapseTime K)) (𝓝 0)
        simpa using hmul0.mono_left
          (nhdsWithin_le_nhds (s := Set.Iio (homotheticCollapseTime K)))
      have hformula : (fun t => dist (homotheticConfiguration q K hK t i)
          (homotheticConfiguration q K hK t j)) =ᶠ[𝓝[<] T]
          (fun t => homotheticScaleFromTime K hK t * dist (q i) (q j)) := by
        filter_upwards [hleftEvent] with t ht
        have ht' : t ∈ Set.Ioo L (homotheticTimeParameter K (Real.pi / 2)) := by
          rw [hrightEq]
          exact ht
        exact homotheticConfiguration_dist q K hK ht' i j
      exact hmul.congr' hformula.symm
    have heq : (fun t => dist ((maximalNewtonUnionTrajectory z₀ t).1 i)
        ((maximalNewtonUnionTrajectory z₀ t).1 j)) =ᶠ[𝓝[<] T]
        (fun t => dist (homotheticConfiguration q K hK t i)
          (homotheticConfiguration q K hK t j)) := by
      filter_upwards [hleftEvent] with t ht
      have heqphase := hagreeOn t ht
      rw [heqphase]
      simp [homotheticPhase]
    exact hhom.congr' heq.symm
  exact ⟨K, hK, hagree, hforward, hnoSyzygy, hdistances⟩

end

end DroppingThreeBodies
