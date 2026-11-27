module

public import NBody
public import Dropping3Bodies
public import Mathlib.Tactic

@[expose] public section

namespace DroppingThreeBodies

theorem nbody_acceleration_eq_generalAcceleration
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) (i : Fin 3) :
    NBody.acceleration G m q i = generalAcceleration G m q i := rfl

theorem nbody_vectorField_eq_generalNewtonField
    (G : ℝ) (m : Fin 3 → ℝ) (z : Phase) :
    NBody.vectorField G m z = generalNewtonField G m z := rfl

theorem nbody_classicalSolution_iff_generalClassicalNewtonSolution
    (G : ℝ) (m : Fin 3 → ℝ) (z : ℝ → Phase) (I : Set ℝ) :
    NBody.ClassicalSolution G m z I ↔ GeneralClassicalNewtonSolution G m z I := Iff.rfl

theorem generalAcceleration_equilateral_centerOfMass
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) (ell : ℝ)
    (hm : NBody.totalMass m ≠ 0)
    (heq : ∀ i j : Fin 3, i ≠ j → dist (q i) (q j) = ell)
    (i : Fin 3) :
    generalAcceleration G m q i =
      -(G * NBody.totalMass m * ell ^ (-3 : ℤ)) •
        (q i - NBody.centerOfMass m q) := by
  have hmass : NBody.totalMass m • NBody.centerOfMass m q =
      NBody.weightedPosition m q := by
    change NBody.totalMass m •
      ((NBody.totalMass m)⁻¹ • NBody.weightedPosition m q) = _
    rw [smul_smul, mul_inv_cancel₀ hm, one_smul]
  have hsum : ∑ j : Fin 3, m j • (q j - q i) =
      NBody.totalMass m • (NBody.centerOfMass m q - q i) := by
    calc
      ∑ j : Fin 3, m j • (q j - q i) =
          ∑ j : Fin 3, (m j • q j - m j • q i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_sub]
      _ = (∑ j : Fin 3, m j • q j) - ∑ j : Fin 3, m j • q i := by
        rw [Finset.sum_sub_distrib]
      _ = NBody.weightedPosition m q - NBody.totalMass m • q i := by
        simp [NBody.weightedPosition, NBody.totalMass, Finset.sum_smul]
      _ = NBody.totalMass m • NBody.centerOfMass m q -
          NBody.totalMass m • q i := by rw [hmass]
      _ = NBody.totalMass m • (NBody.centerOfMass m q - q i) := by
        rw [smul_sub]
  have hforce : generalAcceleration G m q i =
      (G * ell ^ (-3 : ℤ)) • ∑ j : Fin 3, m j • (q j - q i) := by
    unfold generalAcceleration
    calc
      (∑ j : Fin 3, if j = i then 0 else
          (G * m j * inverseCubeDistance q i j) • (q j - q i)) =
        ∑ j : Fin 3, (G * ell ^ (-3 : ℤ)) •
          (m j • (q j - q i)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : j = i
        · subst j
          simp
        · simp [hij, inverseCubeDistance, heq i j (Ne.symm hij), smul_smul]
          ring_nf
      _ = (G * ell ^ (-3 : ℤ)) •
          ∑ j : Fin 3, m j • (q j - q i) := by rw [Finset.smul_sum]
  calc
    generalAcceleration G m q i =
        (G * ell ^ (-3 : ℤ)) • ∑ j : Fin 3, m j • (q j - q i) := hforce
    _ = (G * ell ^ (-3 : ℤ)) •
        (NBody.totalMass m • (NBody.centerOfMass m q - q i)) := by rw [hsum]
    _ = -(G * NBody.totalMass m * ell ^ (-3 : ℤ)) •
        (q i - NBody.centerOfMass m q) := by
      rw [smul_smul]
      rw [show NBody.centerOfMass m q - q i =
        -(q i - NBody.centerOfMass m q) by abel]
      rw [smul_neg, ← neg_smul]
      congr 1
      congr 1
      ring_nf


theorem equilateral_is_centralConfiguration
    (G : ℝ) (hG : 0 < G) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (ell : ℝ) (hell : 0 < ell)
    (hm : ∀ i, 0 < m i)
    (heq : ∀ i j : Fin 3, i ≠ j → dist (q i) (q j) = ell) :
    NBody.CentralConfiguration G m q
      (G * NBody.totalMass m * ell ^ (-3 : ℤ)) := by
  have hmass : 0 < NBody.totalMass m := by
    unfold NBody.totalMass
    exact Finset.sum_pos (fun i hi => hm i) (by simp)
  have hcf : NBody.CollisionFree q := by
    intro i j hij hpos
    have hd : 0 < dist (q i) (q j) := by rw [heq i j hij]; exact hell
    exact (dist_pos.mp hd) hpos
  unfold NBody.CentralConfiguration
  refine ⟨hcf, ne_of_gt hmass, ?_, ?_⟩
  · positivity
  · intro i
    exact generalAcceleration_equilateral_centerOfMass G m q ell
      (ne_of_gt hmass) heq i
end DroppingThreeBodies
