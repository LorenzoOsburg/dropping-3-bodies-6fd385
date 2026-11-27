module

public import NBody.Basic
public import NBody.PairSums
public import Mathlib.Tactic

@[expose] public section

namespace NBody

noncomputable section

def inverseCubeDistance {ι : Type*} [Fintype ι] {d : ℕ}
    (q : Config ι d) (i j : ι) : ℝ := dist (q i) (q j) ^ (-3 : ℤ)

def acceleration {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (G : ℝ) (m : ι → ℝ) (q : Config ι d) (i : ι) : EuclideanSpace ℝ (Fin d) :=
  ∑ j, if j = i then 0 else
    (G * m j * inverseCubeDistance q i j) • (q j - q i)

def vectorField {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (G : ℝ) (m : ι → ℝ) (z : Phase ι d) : Phase ι d :=
  (z.2, fun i => acceleration G m z.1 i)

theorem weightedAcceleration_sum_eq_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (G : ℝ) (m : ι → ℝ) (q : Config ι d) :
    ∑ i, m i • acceleration G m q i = 0 := by
  classical
  let f : ι → ι → EuclideanSpace ℝ (Fin d) := fun i j =>
    if i = j then 0 else
      (G * m i * m j * inverseCubeDistance q i j) • (q j - q i)
  have hf : ∀ i j, f i j = -f j i := by
    intro i j
    by_cases hij : i = j
    · simp [f, hij]
    · simp [f, hij, Ne.symm hij, inverseCubeDistance, dist_comm,
        mul_assoc, mul_left_comm, mul_comm]
      rw [← smul_neg]
      congr 1
      abel
  have hrewrite :
      (∑ i, m i • acceleration G m q i) = ∑ i, ∑ j, f i j := by
    simp [f, acceleration, inverseCubeDistance, Finset.smul_sum,
      smul_smul, mul_assoc, mul_left_comm, mul_comm, eq_comm]
  rw [hrewrite]
  exact sum_pair_cancellation_euclidean f hf

theorem acceleration_translation_invariant {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (G : ℝ) (m : ι → ℝ)
    (q : Config ι d) (b : EuclideanSpace ℝ (Fin d)) (i : ι) :
    acceleration G m (fun j => q j + b) i = acceleration G m q i := by
  simp [acceleration, inverseCubeDistance, dist_eq_norm, add_sub_add_right_eq_sub]

end

end NBody
