module

public import Dropping3Bodies.EqualMass.SideFrame
public import Mathlib.Tactic

@[expose] public section

/-! Static selection of the unique longest side in a scalene configuration.-/

namespace DroppingThreeBodies

noncomputable section

/-- The three opposite-side squared lengths are pairwise distinct. -/
def ScaleneConfiguration (q : Fin 3 → Point) : Prop :=
  ∀ i j : Fin 3, i ≠ j → sideSq q i ≠ sideSq q j

/-- Among three pairwise distinct side squares there is an index strictly
larger than both others. -/
theorem exists_strictly_largest_sideSq (q : Fin 3 → Point)
    (hsc : ScaleneConfiguration q) :
    ∃ i : Fin 3, ∀ j : Fin 3, j ≠ i → sideSq q j < sideSq q i := by
  have h01 : sideSq q 0 ≠ sideSq q 1 := hsc 0 1 (by decide)
  have h02 : sideSq q 0 ≠ sideSq q 2 := hsc 0 2 (by decide)
  have h12 : sideSq q 1 ≠ sideSq q 2 := hsc 1 2 (by decide)
  by_cases h01lt : sideSq q 0 < sideSq q 1
  · by_cases h12lt : sideSq q 1 < sideSq q 2
    · refine ⟨2, ?_⟩
      intro j hj
      fin_cases j
      · exact lt_trans h01lt h12lt
      · exact h12lt
      · exact (hj rfl).elim
    · have h21lt : sideSq q 2 < sideSq q 1 :=
        lt_of_le_of_ne (le_of_not_gt h12lt) (Ne.symm h12)
      refine ⟨1, ?_⟩
      intro j hj
      fin_cases j
      · exact h01lt
      · exact (hj rfl).elim
      · exact h21lt
  · have h10lt : sideSq q 1 < sideSq q 0 :=
      lt_of_le_of_ne (le_of_not_gt h01lt) (Ne.symm h01)
    by_cases h02lt : sideSq q 0 < sideSq q 2
    · refine ⟨2, ?_⟩
      intro j hj
      fin_cases j
      · exact h02lt
      · exact lt_trans h10lt h02lt
      · exact (hj rfl).elim
    · have h20lt : sideSq q 2 < sideSq q 0 :=
        lt_of_le_of_ne (le_of_not_gt h02lt) (Ne.symm h02)
      refine ⟨0, ?_⟩
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · exact h10lt
      · exact h20lt

/-- Every cyclic side gap is nonzero for a scalene configuration, since its
two neighboring opposite-side squares are distinct. -/
theorem sideGap_ne_zero_of_scalene (q : Fin 3 → Point)
    (hsc : ScaleneConfiguration q) (i : Fin 3) : sideGap q i ≠ 0 := by
  rw [sideGap_eq_next_sub_prev_sideSq]
  apply sub_ne_zero.mpr
  apply hsc
  · fin_cases i <;> decide

/-- A selected longest side in a scalene configuration has a nonzero cyclic
gap, which records that the two shorter sides have unequal lengths. -/
theorem exists_strictly_largest_sideSq_with_nonzero_gap
    (q : Fin 3 → Point) (hsc : ScaleneConfiguration q) :
    ∃ i : Fin 3,
      (∀ j : Fin 3, j ≠ i → sideSq q j < sideSq q i) ∧ sideGap q i ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_strictly_largest_sideSq q hsc
  exact ⟨i, hi, sideGap_ne_zero_of_scalene q hsc i⟩

/-- In one-based labels, `sideSq 0`, `sideSq 1`, `sideSq 2` are respectively
`r23`, `r13`, and `r12`. -/
theorem sideSq_eq_originalPairDistance (q : Fin 3 → Point) :
    sideSq q 0 = dist (q 1) (q 2) ^ 2 ∧
    sideSq q 1 = dist (q 2) (q 0) ^ 2 ∧
    sideSq q 2 = dist (q 0) (q 1) ^ 2 := by
  simp [sideSq_eq_cyclicNeighborDistance, dist_comm]

/-- Montgomery's strict chain `r12 < r23 < r13` becomes the strict side-square
ordering `sideSq 2 < sideSq 0 < sideSq 1` in zero-based project indices. -/
theorem originalPairDistanceChain_implies_sideSqOrder
    (q : Fin 3 → Point)
    (hr12r23 : dist (q 0) (q 1) < dist (q 1) (q 2))
    (hr23r13 : dist (q 1) (q 2) < dist (q 0) (q 2)) :
    sideSq q 2 < sideSq q 0 ∧ sideSq q 0 < sideSq q 1 := by
  have hsq12 : dist (q 0) (q 1) ^ 2 < dist (q 1) (q 2) ^ 2 :=
    (sq_lt_sq₀ (dist_nonneg) (dist_nonneg)).2 hr12r23
  have hsq23 : dist (q 1) (q 2) ^ 2 < dist (q 0) (q 2) ^ 2 :=
    (sq_lt_sq₀ (dist_nonneg) (dist_nonneg)).2 hr23r13
  have hlabels := sideSq_eq_originalPairDistance q
  rw [hlabels.2.2, hlabels.1, hlabels.2.1]
  exact ⟨hsq12, by simpa [dist_comm] using hsq23⟩

end

end DroppingThreeBodies
