module

public import NBody.Conservation.Momentum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

namespace NBody

noncomputable section

theorem acceleration_permutation_equivariant {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (G : ℝ) (m : ι → ℝ)
    (q : Config ι d) (σ : Equiv.Perm ι) (i : ι) :
    acceleration G (fun j => m (σ j)) (fun j => q (σ j)) i =
      acceleration G m q (σ i) := by
  classical
  let f : ι → EuclideanSpace ℝ (Fin d) := fun k =>
    if k = σ i then 0 else
      (G * m k * inverseCubeDistance q (σ i) k) • (q k - q (σ i))
  have hterm : ∀ j,
      (if j = i then 0 else
        (G * m (σ j) * inverseCubeDistance (fun k => q (σ k)) i j) •
          (q (σ j) - q (σ i))) = f (σ j) := by
    intro j
    by_cases hij : j = i
    · subst j
      simp [f]
    · have hσ : σ j ≠ σ i := fun h => hij (σ.injective h)
      simp [f, hij, hσ, inverseCubeDistance]
  unfold acceleration
  rw [show (∑ j, if j = i then 0 else
      (G * m (σ j) * inverseCubeDistance (fun k => q (σ k)) i j) •
        (q (σ j) - q (σ i))) = ∑ j, f (σ j) by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j]
  rw [Equiv.sum_comp]

end


theorem acceleration_isometry_equivariant {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (G : ℝ) (m : ι → ℝ)
    (q : Config ι d) (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d)) (i : ι) :
    acceleration G m (fun j => L (q j)) i = L (acceleration G m q i) := by
  classical
  let f : ι → EuclideanSpace ℝ (Fin d) := fun j =>
    if j = i then 0 else
      (G * m j * inverseCubeDistance q i j) • (q j - q i)
  have hmap (s : Finset ι) : L (∑ j ∈ s, f j) = ∑ j ∈ s, L (f j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert, ha, map_add, ih]
  unfold acceleration
  rw [hmap]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : j = i
  · subst j
    simp [f]
  · simp [f, hij, inverseCubeDistance, L.isometry.dist_eq, map_sub, map_smul]
end NBody
