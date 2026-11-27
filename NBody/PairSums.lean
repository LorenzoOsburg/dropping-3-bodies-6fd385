module

public import NBody.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

namespace NBody

theorem sum_sum_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [AddCommMonoid α] (f : ι → ι → α) :
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j, f j i := by
  rw [Finset.sum_comm]

theorem sum_pair_cancellation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ι → ℝ) (hskew : ∀ i j, f i j = -f j i) :
    (∑ i, ∑ j, f i j) = 0 := by
  have hswap : (∑ i, ∑ j, f i j) = ∑ i, ∑ j, f j i := sum_sum_swap f
  have hneg : (∑ i, ∑ j, f i j) = -∑ i, ∑ j, f i j := by
    calc
      (∑ i, ∑ j, f i j) = ∑ i, ∑ j, f j i := hswap
      _ = ∑ i, ∑ j, -f i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hskew j i
      _ = -∑ i, ∑ j, f i j := by simp only [Finset.sum_neg_distrib]
  linarith

theorem sum_pair_cancellation_euclidean {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ}
    (f : ι → ι → EuclideanSpace ℝ (Fin d))
    (hskew : ∀ i j, f i j = -f j i) :
    (∑ i, ∑ j, f i j) = 0 := by
  ext k
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  exact sum_pair_cancellation (fun i j => (f i j) k)
    (fun i j => congrArg (fun x => x k) (hskew i j))

end NBody
