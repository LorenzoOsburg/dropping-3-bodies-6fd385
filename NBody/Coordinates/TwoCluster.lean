module

public import NBody.Configuration.Masses

@[expose] public section

namespace NBody

noncomputable section

/-- Reduced mass of two clusters with masses M_A and M_B. -/
def twoClusterReducedMass (M_A M_B : ℝ) : ℝ :=
  M_A * M_B / (M_A + M_B)

/-- Center of mass of two cluster positions, when their total mass is nonzero. -/
def twoClusterCenter (M_A M_B : ℝ)
    {d : ℕ} (q_A q_B : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (M_A + M_B)⁻¹ • (M_A • q_A + M_B • q_B)

/-- Relative position directed from cluster A to cluster B. -/
def twoClusterRelative {d : ℕ} (q_A q_B : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := q_B - q_A

/-- Positive cluster masses give a positive reduced mass. -/
theorem twoClusterReducedMass_pos {M_A M_B : ℝ}
    (hA : 0 < M_A) (hB : 0 < M_B) :
    0 < twoClusterReducedMass M_A M_B := by
  unfold twoClusterReducedMass
  exact div_pos (mul_pos hA hB) (add_pos hA hB)

/-- Recover the two cluster positions from their center of mass and the
relative vector directed from A to B. -/
def twoClusterReconstruct {d : ℕ} (M_A M_B : ℝ)
    (R r : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
  (R - (M_B / (M_A + M_B)) • r,
    R + (M_A / (M_A + M_B)) • r)

theorem twoClusterRelative_reconstruct {M_A M_B : ℝ} {d : ℕ}
    (hM : M_A + M_B ≠ 0) (R r : EuclideanSpace ℝ (Fin d)) :
    twoClusterRelative (twoClusterReconstruct M_A M_B R r).1
      (twoClusterReconstruct M_A M_B R r).2 = r := by
  have hcoef : M_A / (M_A + M_B) + M_B / (M_A + M_B) = 1 := by
    field_simp
  simp only [twoClusterRelative, twoClusterReconstruct]
  calc
    (R + (M_A / (M_A + M_B)) • r) -
        (R - (M_B / (M_A + M_B)) • r) =
      (M_A / (M_A + M_B) + M_B / (M_A + M_B)) • r := by module
    _ = r := by rw [hcoef, one_smul]

end

end NBody
