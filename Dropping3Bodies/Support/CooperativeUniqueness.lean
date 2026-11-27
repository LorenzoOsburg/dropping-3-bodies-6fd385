module

public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

/-!
# Uniqueness for a cooperative pair on a compact interval

The zero initial-value solution of a two-component linear system is unique
under bounded coefficients. This will handle tied initial side lengths, where
the strict-positive-start comparison theorem does not apply.
-/

namespace DroppingThreeBodies

theorem cooperative_pair_eq_zero_of_zero_initial
    {X Y c d : ℝ → ℝ} {a T K : ℝ}
    (hcontX : ContinuousOn X (Set.Icc a T))
    (hcontY : ContinuousOn Y (Set.Icc a T))
    (hderivX : ∀ t ∈ Set.Ico a T, HasDerivAt X (c t * Y t) t)
    (hderivY : ∀ t ∈ Set.Ico a T, HasDerivAt Y (d t * X t) t)
    (hX₀ : X a = 0) (hY₀ : Y a = 0)
    (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Set.Ico a T, |c t| ≤ K ∧ |d t| ≤ K) :
    ∀ t ∈ Set.Icc a T, X t = 0 ∧ Y t = 0 := by
  let F : ℝ → ℝ × ℝ := fun t => (X t, Y t)
  have hcontF : ContinuousOn F (Set.Icc a T) := hcontX.prodMk hcontY
  have hderivF : ∀ t ∈ Set.Ico a T,
      HasDerivWithinAt F (c t * Y t, d t * X t) (Set.Ici t) t := by
    intro t ht
    exact (hderivX t ht).hasDerivWithinAt.prodMk (hderivY t ht).hasDerivWithinAt
  have hF₀ : F a = 0 := by
    simp [F, hX₀, hY₀]
  have hFbound : ∀ t ∈ Set.Ico a T,
      ‖(c t * Y t, d t * X t)‖ ≤ K * ‖F t‖ := by
    intro t ht
    rw [Prod.norm_def, Prod.norm_def]
    change max |c t * Y t| |d t * X t| ≤ K * max |X t| |Y t|
    apply max_le
    · calc
        |c t * Y t| = |c t| * |Y t| := abs_mul _ _
        _ ≤ K * |Y t| := mul_le_mul_of_nonneg_right (hbound t ht).1 (abs_nonneg _)
        _ ≤ K * max |X t| |Y t| :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hK
    · calc
        |d t * X t| = |d t| * |X t| := abs_mul _ _
        _ ≤ K * |X t| := mul_le_mul_of_nonneg_right (hbound t ht).2 (abs_nonneg _)
        _ ≤ K * max |X t| |Y t| :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hK
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hcontF hderivF hF₀ hFbound
  intro t ht
  have hFt := hzero t ht
  exact ⟨congrArg Prod.fst hFt, congrArg Prod.snd hFt⟩

end DroppingThreeBodies
