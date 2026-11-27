module

public import Dropping3Bodies.EqualMass.PowerLawModel
public import Dropping3Bodies.Geometry.ScaleneSideSelection
public import Dropping3Bodies.Geometry.Betweenness
public import Dropping3Bodies.Support.CollisionBarrier
public import PrincipiaThreeBodies.Definitions

@[expose] public section

namespace DroppingThreeBodies.CentralForce

noncomputable section

theorem orderedOppositeSides_iff (q : Fin 3 → Point) (hcf : CollisionFree q) :
    orderedOppositeSides q ↔ sideSq q 1 < sideSq q 0 ∧ sideSq q 2 < sideSq q 1 := by
  obtain ⟨h0, h1, h2⟩ := sideSq_eq_originalPairDistance q
  rw [h0, h1, h2, sq_lt_sq₀ dist_nonneg dist_nonneg, sq_lt_sq₀ dist_nonneg dist_nonneg]
  have hp := dist_pos.mpr (hcf 0 1 (by decide))
  unfold orderedOppositeSides
  tauto

theorem positive_gaps_iff_side_order (q : Fin 3 → Point) :
    (0 < sideGap q 2 ∧ 0 < sideGap q 0) ↔
    sideSq q 1 < sideSq q 0 ∧ sideSq q 2 < sideSq q 1 := by
  simp only [sideGap_eq_next_sub_prev_sideSq, cyclicNext_two, cyclicPrev_two,
    cyclicNext_zero, cyclicPrev_zero, sub_pos]

theorem shortest_distance_of_side_order {q : Fin 3 → Point}
    (h : sideSq q 1 < sideSq q 0 ∧ sideSq q 2 < sideSq q 1) :
    ∀ i j : Fin 3, i ≠ j → dist (q 0) (q 1) ≤ dist (q i) (q j) := by
  have hshort := shortest_sideSq_le_all_pair_distances q 2
    (show sideSq q 2 ≤ sideSq q (cyclicPrev 2) ∧ sideSq q 2 ≤ sideSq q (cyclicNext 2)
     from ⟨h.2.le, (h.2.trans h.1).le⟩)
  simpa [dist_comm (q 1) (q 0)] using hshort

theorem middle_body_of_side_order {q : Fin 3 → Point} (harea : signedDoubleArea q = 0)
    (hcf : CollisionFree q) (h : sideSq q 1 < sideSq q 0 ∧ sideSq q 2 < sideSq q 1) :
    Sbtw ℝ (q 2) (q 0) (q 1) := by
  obtain ⟨h0, h1, h2⟩ := sideSq_eq_originalPairDistance q
  exact sbtw_of_longest_opposite_side q 0 harea hcf
    (by simpa [cyclicPrev, cyclicNext, h0, h1, dist_comm] using h.1.le)
    (by simpa [cyclicPrev, cyclicNext, h0, h2, dist_comm] using (h.2.trans h.1).le)

end
end DroppingThreeBodies.CentralForce
