module

public import Dropping3Bodies.Inertia.CentralForceJacobi
public import Dropping3Bodies.Inertia.AbstractJacobiArea
public import Dropping3Bodies.Inertia.MaximalInitialBranch
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-! Positive finite initial noncollinear time on the maximal collision-free
central-force solution. The maximal-union ODE construction is reused unchanged.
No regular first syzygy or finite maximal lifetime is assumed. -/

namespace DroppingThreeBodies.CentralForce

noncomputable section

theorem maximalTrajectory_solution (κ : Coefficients) (hκ : κ.C1)
    (m : Fin 3 → ℝ) (z₀ : Phase) :
    Solution κ m (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) :=
  NBody.maximalUnionTrajectory_solution (fun z hz => vectorField_contDiffAt κ hκ m z hz)

theorem maximalDomain_isPreconnected (κ : Coefficients) (m : Fin 3 → ℝ) (z₀ : Phase) :
    IsPreconnected (maximalDomain κ m z₀) :=
  NBody.isPreconnected_maximalUnionDomain _ _ _ _

theorem maximalDomain_initial_mem (κ : Coefficients) (hκ : κ.C1)
    (m : Fin 3 → ℝ) {z₀ : Phase} (hcf : CollisionFree z₀.1) :
    (0 : ℝ) ∈ maximalDomain κ m z₀ := by
  obtain ⟨w⟩ := NBody.exists_initialIntervalWitness
    (NBody.isOpen_regularPhaseSet (ι := Fin 3) 2)
    (show z₀ ∈ NBody.regularPhaseSet (Fin 3) 2 from hcf)
    (vectorField_contDiffAt κ hκ m z₀ hcf) 0
  exact NBody.initialWitness_interval_subset w ⟨w.left_lt, w.lt_right⟩

theorem maximalTrajectory_initial (κ : Coefficients) (hκ : κ.C1)
    (m : Fin 3 → ℝ) {z₀ : Phase} (hcf : CollisionFree z₀.1) :
    maximalTrajectory κ m z₀ 0 = z₀ :=
  NBody.maximalUnionTrajectory_initial
    (NBody.isOpen_regularPhaseSet (ι := Fin 3) 2)
    (show z₀ ∈ NBody.regularPhaseSet (Fin 3) 2 from hcf)
    (vectorField_contDiffAt κ hκ m z₀ hcf)

/-- Every regular classical open interval through the initial data is
contained in the union; this prevents choosing an artificially short domain. -/
theorem maximalDomain_contains_initialInterval
    {κ : Coefficients} {m : Fin 3 → ℝ} {z₀ : Phase} {z : ℝ → Phase} {l r : ℝ}
    (hl : l < 0) (hr : 0 < r) (hinit : z 0 = z₀)
    (hsol : Solution κ m z (Set.Ioo l r)) :
    Set.Ioo l r ⊆ maximalDomain κ m z₀ := by
  let w : NBody.InitialIntervalWitness (NBody.regularPhaseSet (Fin 3) 2)
      (vectorField κ m) z₀ 0 := ⟨l, r, z, hl, hr, hinit, hsol⟩
  exact NBody.initialWitness_interval_subset w

/-- The maximal central-force solution has a genuinely positive finite
initial noncollinear endpoint. Only attraction, symmetry, C1 regularity away
from collisions, positive masses, noncollinearity and initial rest are used.
`IsLUB` ensures the real supremum is a genuine least upper bound. -/
theorem maximal_initialBranch_endpoint_pos_finite
    {κ : Coefficients} {m : Fin 3 → ℝ} {z₀ : Phase}
    (hm : ∀ i, 0 < m i) (hκpos : κ.Positive) (hκreg : κ.C1)
    (harea : signedDoubleArea z₀.1 ≠ 0) (hrest : ∀ i, z₀.2 i = 0) :
    let S := BeforeFirstCollinearity (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0
    S.Nonempty ∧ BddAbove S ∧ IsLUB S (initialNoncollinearEndpoint κ m z₀) ∧
      0 < initialNoncollinearEndpoint κ m z₀ ∧
      (initialNoncollinearEndpoint κ m z₀ : EReal) < ⊤ := by
  let z := maximalTrajectory κ m z₀
  let I := maximalDomain κ m z₀
  have hcf := collisionFree_of_signedDoubleArea_ne_zero harea
  have hsol := maximalTrajectory_solution κ hκreg m z₀
  have hconn := maximalDomain_isPreconnected κ m z₀
  have hzero := maximalDomain_initial_mem κ hκreg m hcf
  have hinit := maximalTrajectory_initial κ hκreg m hcf
  have hsys := jacobiSystem hsol hm
  have hforce := jacobiSystem_positiveForce hsol hm hκpos
  have hdet : (jacobiMatrix m (z 0).1).det ≠ 0 := by
    rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z 0).1 (hm 0) (hm 1)]
    have harea' : signedDoubleArea (z 0).1 ≠ 0 := by simpa [z, hinit] using harea
    exact mul_ne_zero (mul_ne_zero (sqrt_jacobiMu_pos m (hm 0) (hm 1)).ne'
      (sqrt_jacobiNu_pos m (hm 0) (hm 1) (hm 2)).ne') harea'
  have hrest' : jacobiMatrix m (maximalTrajectory κ m z₀ 0).2 = 0 := by
    apply jacobi_velocity_zero_of_rest m (maximalTrajectory κ m z₀) 0
    simpa [hinit] using hrest
  obtain ⟨t, htpos, ht⟩ := hsys.exists_lt_mem_initialBranch hzero hdet
  have hbdd := hsys.initialBranch_bddAbove hforce hconn hzero hrest'
  rw [initialBranch_eq m hm (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0] at ht hbdd
  exact ⟨⟨t, ht⟩, hbdd, isLUB_csSup ⟨t, ht⟩ hbdd,
    htpos.trans_le (le_csSup hbdd ht), EReal.coe_lt_top _⟩

end
end DroppingThreeBodies.CentralForce
