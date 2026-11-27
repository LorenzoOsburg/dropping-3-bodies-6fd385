module

public import Dropping3Bodies.Dynamics.SolutionDerivatives
public import Dropping3Bodies.Geometry.InertiaCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic

@[expose] public section

/-!
Energy functions and their local differential identities on collision-free
Newton trajectories.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Kinetic energy of a unit-mass velocity configuration. -/
def kineticEnergy (v : Fin 3 → Point) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 3, ‖v i‖ ^ 2

/-- Positive Newtonian potential magnitude, summed once over the three pairs. -/
def gravitationalPotential (q : Fin 3 → Point) : ℝ :=
  (dist (q 0) (q 1))⁻¹ + (dist (q 0) (q 2))⁻¹ +
    (dist (q 1) (q 2))⁻¹

/-- Total energy uses the sign convention kinetic minus positive potential. -/
def newtonianEnergy (z : Phase) : ℝ :=
  kineticEnergy z.2 - gravitationalPotential z.1

/-- The pairwise work rate shared by the kinetic and positive-potential
    energies. -/
def gravitationalPotentialRate (q v : Fin 3 → Point) : ℝ :=
  -(inner ℝ (q 0 - q 1) (v 0 - v 1)) * inverseCubeDistance q 0 1 +
    (-(inner ℝ (q 0 - q 2) (v 0 - v 2)) * inverseCubeDistance q 0 2 +
      -(inner ℝ (q 1 - q 2) (v 1 - v 2)) * inverseCubeDistance q 1 2)

/-- Pairing the six internal force terms shows that total kinetic work equals
    the derivative of the positive Newtonian potential. -/
theorem unitAcceleration_work_eq_gravitationalPotentialRate
    (q v : Fin 3 → Point) :
    (∑ i : Fin 3, inner ℝ (v i) (unitAcceleration q i)) =
      gravitationalPotentialRate q v := by
  simp [gravitationalPotentialRate, unitAcceleration, inverseCubeDistance,
    zpow_neg, Fin.sum_univ_succ, dist_comm, real_inner_comm,
    inner_add_right, inner_smul_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm (q 0) (v 1), real_inner_comm (q 0) (v 2),
    real_inner_comm (q 1) (v 0), real_inner_comm (q 1) (v 2),
    real_inner_comm (q 2) (v 0), real_inner_comm (q 2) (v 1),
    real_inner_comm (q 0) (v 0), real_inner_comm (q 1) (v 1),
    real_inner_comm (q 2) (v 2)]
  ring_nf

/-- The integer-power force kernel is the inverse of the cubic distance. -/
theorem inverseCubeDistance_eq_inv_distance_cube
    (q : Fin 3 → Point) (i j : Fin 3) :
    inverseCubeDistance q i j = (dist (q i) (q j) ^ 3)⁻¹ := by
  simp [inverseCubeDistance, zpow_neg]

/-- The work-rate formula uses the same inverse-cube coefficients as the
    derivative of the positive pair potential. -/
theorem gravitationalPotentialRate_eq_derivativeFormula
    (q v : Fin 3 → Point) :
    gravitationalPotentialRate q v =
      -(inner ℝ (q 0 - q 1) (v 0 - v 1)) / dist (q 0) (q 1) ^ 3 +
        (-(inner ℝ (q 0 - q 2) (v 0 - v 2)) / dist (q 0) (q 2) ^ 3 +
          -(inner ℝ (q 1 - q 2) (v 1 - v 2)) / dist (q 1) (q 2) ^ 3) := by
  simp [gravitationalPotentialRate, inverseCubeDistance_eq_inv_distance_cube,
    div_eq_mul_inv]

/-- Kinetic energy along a velocity curve. -/
def kineticEnergyCurve (v : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  massMomentCurve (fun _ => (1 / 2 : ℝ)) v t

/-- Positive potential magnitude along a position curve. -/
def gravitationalPotentialCurve (q : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  (dist (q 0 t) (q 1 t))⁻¹ + ((dist (q 0 t) (q 2 t))⁻¹ +
    (dist (q 1 t) (q 2 t))⁻¹)

/-- Total mechanical energy along a packed phase curve. -/
def newtonianEnergyCurve (z : ℝ → Phase) (t : ℝ) : ℝ :=
  kineticEnergyCurve (fun i s => (z s).2 i) t -
    gravitationalPotentialCurve (fun i s => (z s).1 i) t

/-- Kinetic-energy derivative along differentiable body velocities. -/
theorem hasDerivAt_kineticEnergyCurve
    {v : Fin 3 → ℝ → Point} {a : Fin 3 → Point} {t : ℝ}
    (hv : ∀ i, HasDerivAt (fun s => v i s) (a i) t) :
    HasDerivAt (kineticEnergyCurve v)
      (∑ i : Fin 3, inner ℝ (v i t) (a i)) t := by
  have h := hasDerivAt_massMomentCurve (fun _ => (1 / 2 : ℝ)) hv
  change HasDerivAt (massMomentCurve (fun _ => (1 / 2 : ℝ)) v)
    (∑ i : Fin 3, inner ℝ (v i t) (a i)) t
  have hcoef : (∑ i : Fin 3, inner ℝ (v i t) (a i)) =
      massMomentRate (fun _ => (1 / 2 : ℝ)) v a t := by
    simp [massMomentRate, Fin.sum_univ_succ]
  rw [hcoef]
  exact h

/-- Derivative of reciprocal pair distance along two differentiable planar
    curves. The separation hypothesis is needed because the norm is not
    differentiable at a collision. -/
theorem hasDerivAt_inverseDistanceCurve
    {q r : ℝ → Point} {dq dr : Point} {t : ℝ}
    (hq : HasDerivAt q dq t) (hr : HasDerivAt r dr t)
    (hsep : q t ≠ r t) :
    HasDerivAt (fun s => (dist (q s) (r s))⁻¹)
      (-(inner ℝ (q t - r t) (dq - dr)) /
        dist (q t) (r t) ^ 3) t := by
  have hf : HasDerivAt (fun s => q s - r s) (dq - dr) t := hq.sub hr
  have hnormpos : 0 < ‖q t - r t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsep)
  have hsquare : 0 < ‖q t - r t‖ ^ 2 := sq_pos_of_pos hnormpos
  have hsq : HasDerivAt (fun s => ‖q s - r s‖ ^ 2)
      (2 * inner ℝ (q t - r t) (dq - dr)) t := hf.norm_sq
  have hsqrt := hsq.sqrt (ne_of_gt hsquare)
  have hnormEq : (fun s => dist (q s) (r s)) =ᶠ[nhds t]
      (fun s => Real.sqrt (‖q s - r s‖ ^ 2)) := by
    filter_upwards [] with s
    simp [dist_eq_norm]
  have hdist : HasDerivAt (fun s => dist (q s) (r s))
      ((2 * inner ℝ (q t - r t) (dq - dr)) /
        (2 * Real.sqrt (‖q t - r t‖ ^ 2))) t :=
    hsqrt.congr_of_eventuallyEq hnormEq
  have hdist0 : dist (q t) (r t) ≠ 0 := (dist_pos.mpr hsep).ne'
  have hinv := hdist.inv hdist0
  have hderiv : -((2 * inner ℝ (q t - r t) (dq - dr)) /
      (2 * Real.sqrt (‖q t - r t‖ ^ 2))) / dist (q t) (r t) ^ 2 =
      -(inner ℝ (q t - r t) (dq - dr)) / dist (q t) (r t) ^ 3 := by
    have hnorm : Real.sqrt (‖q t - r t‖ ^ 2) = dist (q t) (r t) := by
      simp [dist_eq_norm]
    rw [hnorm]
    ring
  exact hinv.congr_deriv hderiv

/-- Derivative of the three-pair potential magnitude. -/
theorem hasDerivAt_gravitationalPotentialCurve
    {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {t : ℝ}
    (hq : ∀ i, HasDerivAt (fun s => q i s) (v i) t)
    (hsep : ∀ i j, i ≠ j → q i t ≠ q j t) :
    HasDerivAt (gravitationalPotentialCurve q)
      (gravitationalPotentialRate (fun i => q i t) v) t := by
  have h01 := hasDerivAt_inverseDistanceCurve (hq 0) (hq 1)
    (hsep 0 1 (by decide))
  have h02 := hasDerivAt_inverseDistanceCurve (hq 0) (hq 2)
    (hsep 0 2 (by decide))
  have h12 := hasDerivAt_inverseDistanceCurve (hq 1) (hq 2)
    (hsep 1 2 (by decide))
  convert (HasDerivAt.add h01 (HasDerivAt.add h02 h12)) using 1 <;> try rfl

/-- Mechanical energy has zero derivative at every instant of a classical
    collision-free unit-mass Newton solution. -/
theorem hasDerivAt_newtonianEnergyCurve_classicalNewton_zero
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (newtonianEnergyCurve z) 0 t := by
  let q : Fin 3 → ℝ → Point := fun i s => (z s).1 i
  let v : Fin 3 → ℝ → Point := fun i s => (z s).2 i
  let a : Fin 3 → Point := fun i => unitAcceleration (z t).1 i
  have hq (i : Fin 3) : HasDerivAt (q i) ((z t).2 i) t := by
    simpa [q] using (classicalNewton_body_vector_derivatives i hsol ht).1
  have hv (i : Fin 3) : HasDerivAt (v i) (a i) t := by
    simpa [v, a] using (classicalNewton_body_vector_derivatives i hsol ht).2
  have hcf := (hsol.2 t ht).1
  have hsep (i j : Fin 3) (hij : i ≠ j) : q i t ≠ q j t := by
    exact hcf i j hij
  have hkin := hasDerivAt_kineticEnergyCurve hv
  have hpot := hasDerivAt_gravitationalPotentialCurve hq hsep
  have hpotRate := hpot.congr_deriv (gravitationalPotentialRate_eq_derivativeFormula
    (fun i => q i t) (fun i => (z t).2 i)).symm
  have henergy := hkin.sub hpotRate
  have hwork := unitAcceleration_work_eq_gravitationalPotentialRate
    (z t).1 (z t).2
  have hzero : (∑ i : Fin 3, inner ℝ ((z t).2 i) (a i)) -
      gravitationalPotentialRate (z t).1 (z t).2 = 0 := by
    dsimp [a]
    rw [← hwork]
    ring
  have henergyZero := henergy.congr_deriv hzero
  convert henergyZero using 1 <;> try rfl

/-- Total mechanical energy is constant on every preconnected open interval of
    a classical collision-free Newton solution. -/
theorem newtonianEnergyCurve_eq_on_classicalNewtonSolution
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    newtonianEnergyCurve z s = newtonianEnergyCurve z t := by
  apply hsol.1.is_const_of_deriv_eq_zero hconn
  · intro τ hτ
    exact (hasDerivAt_newtonianEnergyCurve_classicalNewton_zero hsol hτ).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [(hasDerivAt_newtonianEnergyCurve_classicalNewton_zero hsol hτ).deriv]
    simp
  · exact hs
  · exact ht

/-- The curve-level energy agrees pointwise with the configuration-level
    energy definition. -/
theorem newtonianEnergyCurve_eq_newtonianEnergy (z : ℝ → Phase) (t : ℝ) :
    newtonianEnergyCurve z t = newtonianEnergy (z t) := by
  simp [newtonianEnergyCurve, newtonianEnergy, kineticEnergyCurve,
    gravitationalPotentialCurve, gravitationalPotential, massMomentCurve,
    massMoment, kineticEnergy, Fin.sum_univ_succ]
  ring

/-- If all three pair distances are at least `a>0`, the positive potential is
    at most `3/a`. -/
theorem gravitationalPotential_le_three_div_of_pair_distance_lower_bound
    (q : Fin 3 → Point) {a : ℝ} (ha : 0 < a)
    (h01 : a ≤ dist (q 0) (q 1))
    (h02 : a ≤ dist (q 0) (q 2))
    (h12 : a ≤ dist (q 1) (q 2)) :
    gravitationalPotential q ≤ 3 / a := by
  unfold gravitationalPotential
  have h01' := one_div_le_one_div_of_le ha h01
  have h02' := one_div_le_one_div_of_le ha h02
  have h12' := one_div_le_one_div_of_le ha h12
  norm_num at h01' h02' h12'
  have hthree : 3 / a = 3 * a⁻¹ := by ring
  rw [hthree]
  linarith

/-- At a collision-free configuration the positive Newtonian potential is
    strictly positive. -/
theorem gravitationalPotential_pos_of_collisionFree
    (q : Fin 3 → Point) (hcf : CollisionFree q) :
    0 < gravitationalPotential q := by
  have h01 : 0 < dist (q 0) (q 1) := dist_pos.mpr (hcf 0 1 (by decide))
  have h02 : 0 < dist (q 0) (q 2) := dist_pos.mpr (hcf 0 2 (by decide))
  have h12 : 0 < dist (q 1) (q 2) := dist_pos.mpr (hcf 1 2 (by decide))
  unfold gravitationalPotential
  positivity

/-- Initial rest and energy conservation imply that kinetic energy never
    exceeds the positive potential on the same connected solution interval. -/
theorem kineticEnergy_le_gravitationalPotential_of_initial_rest
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I)
    (hrest : ∀ i, (z a).2 i = 0) :
    kineticEnergy (z t).2 ≤ gravitationalPotential (z t).1 := by
  have hconst := newtonianEnergyCurve_eq_on_classicalNewtonSolution
    hsol hconn ha ht
  rw [newtonianEnergyCurve_eq_newtonianEnergy z a,
    newtonianEnergyCurve_eq_newtonianEnergy z t] at hconst
  have hkin0 : kineticEnergy (z a).2 = 0 := by
    unfold kineticEnergy
    simp [hrest]
  have hcf := (hsol.2 a ha).1
  have hUpos := gravitationalPotential_pos_of_collisionFree (z a).1 hcf
  unfold newtonianEnergy at hconst
  rw [hkin0] at hconst
  unfold gravitationalPotential at hUpos
  dsimp [kineticEnergy, gravitationalPotential] at hconst ⊢
  linarith

/-- The squared pair rotation is controlled by side length and total kinetic
    energy. This is the kinematic input `K²≤4a²Tkin` for the barrier. -/
theorem sidePairRotation_sq_le_four_sideSq_mul_kinetic
    (q v : Fin 3 → Point) (i : Fin 3) :
    cross (sideVector q i) (sideVector v i) ^ 2 ≤
      4 * sideSq q i * kineticEnergy v := by
  have hcross := cross_sq_le_norm_sq_mul_norm_sq
    (sideVector q i) (sideVector v i)
  have hdiff : ‖sideVector v i‖ ^ 2 ≤
      2 * (‖v (cyclicNext i)‖ ^ 2 + ‖v (cyclicPrev i)‖ ^ 2) := by
    have hbound (x y : Point) : ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      have hnorm := norm_sub_le x y
      have hleft := norm_nonneg (x - y)
      have hsum : 0 ≤ ‖x‖ + ‖y‖ := add_nonneg (norm_nonneg x) (norm_nonneg y)
      have hsq := (sq_le_sq₀ hleft hsum).2 hnorm
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    fin_cases i
    · simpa [sideVector, add_comm, add_left_comm, add_assoc] using hbound (v 2) (v 1)
    · simpa [sideVector, add_comm, add_left_comm, add_assoc] using hbound (v 0) (v 2)
    · simpa [sideVector, add_comm, add_left_comm, add_assoc] using hbound (v 1) (v 0)
  have hsum : ‖v (cyclicNext i)‖ ^ 2 + ‖v (cyclicPrev i)‖ ^ 2 ≤
      ∑ j : Fin 3, ‖v j‖ ^ 2 := by
    fin_cases i <;> simp [cyclicNext, cyclicPrev, Fin.sum_univ_succ]
    all_goals
      nlinarith [sq_nonneg (‖v 0‖), sq_nonneg (‖v 1‖), sq_nonneg (‖v 2‖)]
  have hside : 0 ≤ sideSq q i := by
    simp [sideSq]
  have hstep := mul_le_mul_of_nonneg_left hdiff (sq_nonneg (‖sideVector q i‖))
  have hstep2 := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ ‖sideVector q i‖ ^ 2 * 2 by positivity)
  calc
    cross (sideVector q i) (sideVector v i) ^ 2 ≤
        ‖sideVector q i‖ ^ 2 * ‖sideVector v i‖ ^ 2 := hcross
    _ ≤ ‖sideVector q i‖ ^ 2 *
        (2 * (‖v (cyclicNext i)‖ ^ 2 + ‖v (cyclicPrev i)‖ ^ 2)) := hstep
    _ = ‖sideVector q i‖ ^ 2 * 2 *
        (‖v (cyclicNext i)‖ ^ 2 + ‖v (cyclicPrev i)‖ ^ 2) := by ring
    _ ≤ ‖sideVector q i‖ ^ 2 * 2 * ∑ j : Fin 3, ‖v j‖ ^ 2 := hstep2
    _ = 4 * sideSq q i * kineticEnergy v := by
      norm_num [sideSq, kineticEnergy]
      ring

/-- Along a solution from rest, a common lower bound `a` on the three sides
    gives `Tkin≤3/a` through energy conservation. -/
theorem kineticEnergy_le_three_div_of_initial_rest
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {t₀ t a : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (ha : 0 < a)
    (hrest : ∀ i, (z t₀).2 i = 0)
    (h01 : a ≤ dist ((z t).1 0) ((z t).1 1))
    (h02 : a ≤ dist ((z t).1 0) ((z t).1 2))
    (h12 : a ≤ dist ((z t).1 1) ((z t).1 2)) :
    kineticEnergy (z t).2 ≤ 3 / a := by
  calc
    kineticEnergy (z t).2 ≤ gravitationalPotential (z t).1 :=
      kineticEnergy_le_gravitationalPotential_of_initial_rest
        hsol hconn ht₀ ht hrest
    _ ≤ 3 / a := gravitationalPotential_le_three_div_of_pair_distance_lower_bound
      (z t).1 ha h01 h02 h12

end

end DroppingThreeBodies
