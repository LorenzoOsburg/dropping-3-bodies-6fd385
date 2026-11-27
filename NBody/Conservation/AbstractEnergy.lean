module

public import NBody.Conservation.Energy
public import NBody.Configuration.MassPairing

@[expose] public section

namespace NBody

noncomputable section

/-- Mechanical energy along a position and velocity curve, for a user-supplied
potential energy `V`. -/
def mechanicalEnergyCurve {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (V : Config ι d → ℝ)
    (q : ℝ → Config ι d) (v : ℝ → Config ι d) (t : ℝ) : ℝ :=
  kineticEnergyCurve m v t + V (q t)

/-- Abstract energy conservation principle: if the potential derivative along
the trajectory cancels the mass-weighted acceleration work, then mechanical
energy has derivative zero. Establishing this balance from a particular
potential and force law is a separate theorem. -/
theorem hasDerivAt_mechanicalEnergy_zero_of_work_balance
    {ι : Type*} [Fintype ι] {d : ℕ} (m : ι → ℝ)
    (V : Config ι d → ℝ) (q v : ℝ → Config ι d)
    {t : ℝ} (acc : Config ι d)
    (hv : HasDerivAt v acc t)
    (hV : HasDerivAt (fun s => V (q s)) (-massPairing m (v t) acc) t) :
    HasDerivAt (mechanicalEnergyCurve m V q v) 0 t := by
  have hkin := hasDerivAt_kineticEnergyCurve m hv
  have hcoeff :
      (1 / 2 : ℝ) * ∑ i, m i * (2 * inner ℝ (v t i) (acc i)) =
        massPairing m (v t) acc := by
    rw [Finset.mul_sum]
    dsimp [massPairing]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hkin' : HasDerivAt (kineticEnergyCurve m v)
      (massPairing m (v t) acc) t := by
    rw [← hcoeff]
    exact hkin
  have hsum := hkin'.add hV
  change HasDerivAt (kineticEnergyCurve m v + (fun s => V (q s))) 0 t
  simpa using hsum

end

end NBody
