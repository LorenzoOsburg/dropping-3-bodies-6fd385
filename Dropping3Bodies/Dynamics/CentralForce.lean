module

public import Dropping3Bodies.Dynamics.GeneralNewton
public import NBody.Regularity
public import NBody.ODE.Solution
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-! Symmetric central pair forces, with regularity and attraction hypotheses
kept separate from the equations. No potential is assumed. -/

namespace DroppingThreeBodies.CentralForce

noncomputable section

theorem weight_symmetric (κ : Coefficients) (q : Fin 3 → Point) (i j : Fin 3) :
    weight κ q i j = weight κ q j i := by
  simp only [weight, κ.symmetric i j, dist_comm]

theorem body_derivatives {κ : Coefficients} {m : Fin 3 → ℝ}
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : Solution κ m z I) (ht : t ∈ I) (i : Fin 3) :
    HasDerivAt (fun s => (z s).1 i) ((z t).2 i) t ∧
      HasDerivAt (fun s => (z s).2 i) (acceleration κ m (z t).1 i) t := by
  have hphase := (hsol.2 t ht).2
  constructor
  · simpa [vectorField] using
      (hasDerivAt_pi.1 hphase.hasFDerivAt.fst.hasDerivAt) i
  · simpa [vectorField] using
      (hasDerivAt_pi.1 hphase.hasFDerivAt.snd.hasDerivAt) i

/-- Multiplying acceleration by the target mass recovers precisely the force. -/
theorem mass_smul_acceleration (κ : Coefficients) (m : Fin 3 → ℝ)
    (q : Fin 3 → Point) (i : Fin 3) (hmi : m i ≠ 0) :
    m i • acceleration κ m q i =
      ∑ j, if j = i then 0 else weight κ q i j • (q j - q i) := by
  simp only [acceleration, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : j = i
  · simp [hij]
  · simp only [if_neg hij, smul_smul]
    congr 1
    field_simp

theorem mass_mul_acceleration_coord (κ : Coefficients) (m : Fin 3 → ℝ)
    (q : Fin 3 → Point) (i : Fin 3) (hmi : m i ≠ 0) (r : Fin 2) :
    m i * acceleration κ m q i r =
      ∑ j, if j = i then 0 else weight κ q i j * (q j - q i) r := by
  have h := congrArg (fun p : Point => p r) (mass_smul_acceleration κ m q i hmi)
  fin_cases i <;> simpa [Fin.sum_univ_succ] using h

theorem vectorField_contDiffAt (κ : Coefficients) (hκ : κ.C1)
    (m : Fin 3 → ℝ) (z : Phase) (hcf : CollisionFree z.1) :
    ContDiffAt ℝ 1 (vectorField κ m) z := by
  change ContDiffAt ℝ 1
    (fun w : Phase => (w.2, fun i => acceleration κ m w.1 i)) z
  apply ContDiffAt.prodMk
  · fun_prop
  · rw [contDiffAt_pi]
    intro i
    have hterms (j : Fin 3) : ContDiffAt ℝ 1
        (fun w : Phase => if j = i then 0 else
          (weight κ w.1 i j / m i) • (w.1 j - w.1 i)) z := by
      by_cases hij : j = i
      · simpa [hij] using
          (by fun_prop : ContDiffAt ℝ 1 (fun _ : Phase => (0 : Point)) z)
      · simp only [if_neg hij]
        have hne := hcf i j (Ne.symm hij)
        have hd := NBody.contDiffAt_phaseDistance z i j hne
        have hc := (hκ i j (Ne.symm hij) _ (dist_pos.mpr hne)).comp z hd
        exact (hc.div_const (m i)).smul (by fun_prop)
    simpa [acceleration] using
      (ContDiffAt.sum (s := Finset.univ) (fun j hj => hterms j))

end
end DroppingThreeBodies.CentralForce
