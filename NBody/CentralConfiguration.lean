module

public import NBody.Conservation.Momentum

@[expose] public section

namespace NBody

def CentralConfiguration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (G : ℝ) (m : ι → ℝ) (q : Config ι d) (κ : ℝ) : Prop :=
  CollisionFree q ∧ totalMass m ≠ 0 ∧ 0 < κ ∧
    ∀ i, acceleration G m q i = -κ • (q i - centerOfMass m q)

/-- At equal pair distance, arbitrary masses produce a central configuration
about their actual center of mass. The coupling constant is the total mass
times the common inverse-cube factor. -/
theorem acceleration_equilateral_eq_centerOfMass
    (G : ℝ) (m : Fin 3 → ℝ) (q : Config (Fin 3) 2) (d : ℝ)
    (h01 : dist (q 0) (q 1) = d)
    (h02 : dist (q 0) (q 2) = d)
    (h12 : dist (q 1) (q 2) = d)
    (hM : totalMass m ≠ 0) (i : Fin 3) :
    acceleration G m q i =
      -(G * d ^ (-3 : ℤ) * totalMass m) • (q i - centerOfMass m q) := by
  have hdist : ∀ i j : Fin 3, i ≠ j → dist (q i) (q j) = d := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (False.elim (hij rfl))
    · exact h01
    · exact h02
    · rw [dist_comm]
      exact h01
    · exact (False.elim (hij rfl))
    · exact h12
    · rw [dist_comm]
      exact h02
    · rw [dist_comm]
      exact h12
    · exact (False.elim (hij rfl))
  have hacc : ∀ i : Fin 3,
      acceleration G m q i = (G * d ^ (-3 : ℤ)) •
        (weightedPosition m q - totalMass m • q i) := by
    intro i
    fin_cases i <;>
      simp [acceleration, inverseCubeDistance, weightedPosition, totalMass,
        Fin.sum_univ_succ, hdist] <;> module
  rw [hacc i]
  have hcenter : totalMass m • centerOfMass m q = weightedPosition m q := by
    simp [centerOfMass, hM]
  rw [← hcenter]
  module

end NBody
