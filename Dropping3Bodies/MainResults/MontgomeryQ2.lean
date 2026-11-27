module

public import Dropping3Bodies.MainResults.Q2

@[expose] public section

/-! A labeled distance-chain corollary matching Montgomery's statement. -/

namespace DroppingThreeBodies

noncomputable section

/-- The original strict distance chain `r12 < r23 < r13` implies that the
same labeled chain persists through the first regular syzygy. -/
theorem exists_completePaperQ2_initialData_montgomeryChain
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ)
    (d : InitialData) (hmass : ∀ i, d.mass i = μ)
    (hr12r23 : dist (d.position 0) (d.position 1) <
      dist (d.position 1) (d.position 2))
    (hr23r13 : dist (d.position 1) (d.position 2) <
      dist (d.position 0) (d.position 2)) :
-- wir verlangen hier Kollisionsfreiheit, ist das nicht zu stark für bestimme sehr symmetrische Konfigurationen. ah habs gecheckt: wir setzen immer schiefheit voraus, die sym. Konfig. werden gesondert behandelt. s. Theorem 2.2 (die Unterpunkte) im stärkeren Paper (nicht formalisiert soweit ich weiß)
    ∃ (z : ℝ → Phase) (I : Set ℝ) (T : ℝ),
      GeneralClassicalNewtonSolution G d.mass z I ∧
      z 0 = (d.position, initialVelocity d) ∧ 0 ∈ I ∧ T ∈ I ∧
      FirstRegularSyzygy z I 0 T ∧
      Sbtw ℝ ((z T).1 0) ((z T).1 1) ((z T).1 2) ∧
      (∀ t ∈ Set.Icc 0 T,
        dist ((z t).1 0) ((z t).1 1) < dist ((z t).1 1) ((z t).1 2) ∧
        dist ((z t).1 1) ((z t).1 2) < dist ((z t).1 0) ((z t).1 2)) := by
  have hsqOrder := originalPairDistanceChain_implies_sideSqOrder
    d.position hr12r23 hr23r13
  have hscalene : ScaleneConfiguration d.position := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp_all
    all_goals linarith [hsqOrder.1, hsqOrder.2]
  obtain ⟨z, I, T, hsol, hinit, hzero, hTmem, hfirst,
    ⟨i, hbetween, horders, hpairwise⟩⟩ :=
    exists_completePaperQ2_initialData_commonMass_scalene G μ hG hμ d
      hmass hscalene
  have hsq12 : ∀ t ∈ Set.Icc 0 T,
      sideSq (z t).1 2 < sideSq (z t).1 0 := by
    intro t ht
    exact hpairwise 2 0 hsqOrder.1 t ht
  have hsq23 : ∀ t ∈ Set.Icc 0 T,
      sideSq (z t).1 0 < sideSq (z t).1 1 := by
    intro t ht
    exact hpairwise 0 1 hsqOrder.2 t ht
  have hdist12 : ∀ t ∈ Set.Icc 0 T,
      dist ((z t).1 0) ((z t).1 1) < dist ((z t).1 1) ((z t).1 2) := by
    intro t ht
    have hlabels := sideSq_eq_originalPairDistance (z t).1
    have hsq : dist ((z t).1 0) ((z t).1 1) ^ 2 <
        dist ((z t).1 1) ((z t).1 2) ^ 2 := by
      simpa [hlabels.1, hlabels.2.2] using hsq12 t ht
    exact (sq_lt_sq₀ (dist_nonneg) (dist_nonneg)).1 hsq
  have hdist23 : ∀ t ∈ Set.Icc 0 T,
      dist ((z t).1 1) ((z t).1 2) < dist ((z t).1 0) ((z t).1 2) := by
    intro t ht
    have hlabels := sideSq_eq_originalPairDistance (z t).1
    have hsq : dist ((z t).1 1) ((z t).1 2) ^ 2 <
        dist ((z t).1 0) ((z t).1 2) ^ 2 := by
      simpa [hlabels.1, hlabels.2.1, dist_comm] using hsq23 t ht
    exact (sq_lt_sq₀ (dist_nonneg) (dist_nonneg)).1 hsq
  have hbetween012 :
      Sbtw ℝ ((z T).1 0) ((z T).1 1) ((z T).1 2) := by
    have ht0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, le_of_lt hfirst.1⟩
    have ho := horders 0 ht0
    have hi : i = 1 := by
      by_contra hne
      fin_cases i
      · have hbad : sideSq d.position 0 > sideSq d.position 1 := by
          simpa [hinit] using ho.2.1
        linarith [hsqOrder.2]
      · exact hne rfl
      · have hbad : sideSq d.position 2 > sideSq d.position 1 := by
          simpa [hinit] using ho.1
        linarith [hsqOrder.1, hsqOrder.2]
    simpa [hi, cyclicPrev, cyclicNext] using hbetween
  exact ⟨z, I, T, hsol, hinit, hzero, hTmem, hfirst, hbetween012,
    fun t ht => ⟨hdist12 t ht, hdist23 t ht⟩⟩

end

end DroppingThreeBodies
