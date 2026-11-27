module

public import NBody.Configuration.Masses
public import Mathlib.Tactic

@[expose] public section

namespace NBody

noncomputable section

/-- The physical mass-weighted configuration pairing. It is kept separate
from the supremum norm on `Config`. -/
def massPairing {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (q r : Config ι d) : ℝ :=
  ∑ i, m i * inner ℝ (q i) (r i)

theorem continuous_massPairing {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) : Continuous (fun p : Config ι d × Config ι d =>
      massPairing m p.1 p.2) := by
  unfold massPairing
  fun_prop

theorem massPairing_symm {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (q r : Config ι d) : massPairing m q r = massPairing m r q := by
  simp [massPairing, real_inner_comm]

theorem massPairing_add_right {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (q r s : Config ι d) :
    massPairing m q (r + s) = massPairing m q r + massPairing m q s := by
  simp only [massPairing, Pi.add_apply, inner_add_right, mul_add,
    Finset.sum_add_distrib]

theorem massPairing_smul_right {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (q r : Config ι d) (a : ℝ) :
    massPairing m q (a • r) = a * massPairing m q r := by
  simp [massPairing, inner_smul_right, Finset.mul_sum, mul_left_comm]

/-- A test configuration supported at one label. Pairing against it isolates
that body's mass and displacement norm. -/
def massPairingProbe {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (i : ι) (q : Config ι d) : Config ι d :=
  fun j => if j = i then q i else 0

theorem massPairing_probe {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (m : ι → ℝ) (i : ι) (q : Config ι d) :
    massPairing m q (massPairingProbe i q) = m i * ‖q i‖ ^ 2 := by
  classical
  unfold massPairing massPairingProbe
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem exists_massPairing_nonzero_probe {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (m : ι → ℝ) (hm : ∀ i, 0 < m i)
    {q : Config ι d} (hq : q ≠ 0) :
    ∃ r, massPairing m q r ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
  have hnorm : 0 < ‖q i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hi)
  refine ⟨massPairingProbe i q, ?_⟩
  rw [massPairing_probe]
  exact ne_of_gt (mul_pos (hm i) hnorm)

theorem massPairing_self_pos {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) {q : Config ι d} (hq : q ≠ 0) :
    0 < massPairing m q q := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
  rw [massPairing, Finset.sum_pos_iff_of_nonneg]
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa [real_inner_self_eq_norm_sq] using
      mul_pos (hm i) (sq_pos_of_pos (norm_pos_iff.mpr hi))
  · intro j hj
    apply mul_nonneg (le_of_lt (hm j))
    simp

end

end NBody
