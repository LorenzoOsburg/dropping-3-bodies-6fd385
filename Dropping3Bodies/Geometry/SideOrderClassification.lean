module

public import Dropping3Bodies.Geometry.BodyIndex
public import Mathlib.Tactic

@[expose] public section

/-! Exhaustive order classification for three real side values. -/

namespace DroppingThreeBodies

/-- For three side values, either there is a unique strict maximum, all values
    agree, or a unique shorter side lies below two equal longest sides.

The witness index is always stated against the project's cyclic predecessor
and successor conventions. -/
theorem sideValue_order_trichotomy (s : Fin 3 → ℝ) :
    (∃ i, s (cyclicPrev i) < s i ∧ s (cyclicNext i) < s i) ∨
    (∀ i j, s i = s j) ∨
    (∃ i, s i < s (cyclicPrev i) ∧ s i < s (cyclicNext i) ∧
      s (cyclicPrev i) = s (cyclicNext i)) := by
  let a := s 0
  let b := s 1
  let c := s 2
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · by_cases hstrict : b < c
      · left
        refine ⟨2, ?_, ?_⟩
        · change b < c
          exact hstrict
        · change a < c
          exact lt_of_le_of_lt hab hstrict
      · have hbcEq : b = c := le_antisymm hbc (le_of_not_gt hstrict)
        by_cases habStrict : a < b
        · right
          right
          refine ⟨0, ?_, ?_, ?_⟩
          · change a < c
            exact lt_of_lt_of_eq habStrict hbcEq
          · change a < b
            exact habStrict
          · change c = b
            exact hbcEq.symm
        · right
          left
          have habEq : a = b := le_antisymm hab (le_of_not_gt habStrict)
          intro i j
          fin_cases i <;> fin_cases j <;> simp [a, b, c, habEq, hbcEq]
    · have hcb : c < b := lt_of_not_ge hbc
      by_cases habStrict : a < b
      · left
        refine ⟨1, ?_, ?_⟩
        · simpa [a, b, c, cyclicPrev] using habStrict
        · simpa [a, b, c, cyclicNext] using hcb
      · right
        right
        have habEq : a = b := le_antisymm hab (le_of_not_gt habStrict)
        refine ⟨2, ?_, ?_, ?_⟩
        · change c < b
          exact hcb
        · change c < a
          rw [habEq]
          exact hcb
        · change b = a
          exact habEq.symm
  · have hba : b < a := lt_of_not_ge hab
    by_cases hac : a ≤ c
    · by_cases hstrict : a < c
      · left
        refine ⟨2, ?_, ?_⟩
        · change b < c
          exact lt_trans hba hstrict
        · change a < c
          exact hstrict
      · right
        right
        have hca : c = a := le_antisymm (le_of_not_gt hstrict) hac
        refine ⟨1, ?_, ?_, ?_⟩
        · change b < a
          exact hba
        · change b < c
          rw [hca]
          exact hba
        · change a = c
          exact hca.symm
    · have hca : c < a := lt_of_not_ge hac
      left
      refine ⟨0, ?_, ?_⟩
      · change c < a
        exact hca
      · change b < a
        exact hba

end DroppingThreeBodies
