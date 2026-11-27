module

public import Dropping3Bodies.EqualMass.PowerLawModel
public import Dropping3Bodies.Dynamics.Energy
public import NBody.Conservation.AbstractEnergy

@[expose] public section

namespace DroppingThreeBodies.CentralForce

noncomputable section

private theorem sum_fin_three {A : Type*} [AddCommMonoid A] (f : Fin 3 → A) :
    (∑ i, f i) = f 0 + (f 1 + f 2) := by
  simp [Fin.sum_univ_succ]

/-- The physical energy is constant on a connected classical solution. -/
theorem power_energy_conserved {α g m : ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : EqualPowerSolution α g m z I) (hm : 0 < m)
    (hconn : IsPreconnected I) {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I) :
    NBody.kineticEnergy (fun _ => m) (z t).2 + NBody.inversePowerPotential α (commonCouplings g) (z t).1 =
      NBody.kineticEnergy (fun _ => m) (z a).2 + NBody.inversePowerPotential α (commonCouplings g) (z a).1 := by
  let E := NBody.mechanicalEnergyCurve (fun _ : Fin 3 => m)
    (NBody.inversePowerPotential α (commonCouplings g)) (fun s => (z s).1) (fun s => (z s).2)
  have hd (s : ℝ) (hs : s ∈ I) : HasDerivAt E 0 s := by
    let acc := acceleration (powerCoefficients α (commonCouplings g)) (fun _ => m) (z s).1
    have hv : HasDerivAt (fun u => (z u).2) acc s :=
      hasDerivAt_pi.mpr fun i => (body_derivatives hsol hs i).2
    have hq : HasDerivAt (fun u => (z u).1) (z s).2 s :=
      hasDerivAt_pi.mpr fun i => (body_derivatives hsol hs i).1
    apply NBody.hasDerivAt_mechanicalEnergy_zero_of_work_balance _ _ _ _ acc hv
    have hV := (NBody.hasFDerivAt_inversePowerPotential α (commonCouplings g)
      (q := (z s).1) (hsol.2 s hs).1).comp_hasDerivAt s hq
    apply hV.congr_deriv
    simp only [neg_apply, sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      innerSL_apply_apply, NBody.massPairing, neg_inj]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [acc]
    rw [power_acceleration_eq_inversePowerForce, real_inner_smul_right, real_inner_comm]
    field_simp [hm.ne']
  exact hsol.1.is_const_of_deriv_eq_zero hconn
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hd s hs).deriv]; simp) ht ha

/-- The ordered-pair convention counts each physical interaction once. -/
theorem common_power_potential (α g : ℝ) (q : Fin 3 → Point) :
    NBody.inversePowerPotential α (commonCouplings g) q =
      -g * (dist (q 0) (q 1) ^ (-α) + dist (q 0) (q 2) ^ (-α) +
        dist (q 1) (q 2) ^ (-α)) := by
  simp (disch := decide) only [NBody.inversePowerPotential, sum_fin_three, commonCouplings,
    if_pos, if_neg, Real.rpow_eq_pow, dist_comm (q 1) (q 0), dist_comm (q 2) (q 0), dist_comm (q 2) (q 1)]
  ring

/-- Bounding all three distances below bounds the sum of the squared speeds. -/
theorem power_speed_sum_bound {α g m : ℝ} {z : ℝ → Phase} {I : Set ℝ} {a t δ : ℝ}
    (hsol : EqualPowerSolution α g m z I) (hα : 0 < α) (hg : 0 < g) (hm : 0 < m)
    (hconn : IsPreconnected I) (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (hδ : 0 < δ) (hsep : ∀ j k : Fin 3, j ≠ k → δ ≤ dist ((z t).1 j) ((z t).1 k)) :
    ∑ i : Fin 3, ‖(z t).2 i‖ ^ 2 ≤ 6 * g / m * δ ^ (-α) := by
  have hE := power_energy_conserved hsol hm hconn ha ht
  rw [common_power_potential, common_power_potential] at hE
  have hkin : NBody.kineticEnergy (fun _ : Fin 3 => m) (z t).2 =
      (1/2 : ℝ) * (m * ∑ i : Fin 3, ‖(z t).2 i‖ ^ 2) := by
    simp [NBody.kineticEnergy, Finset.mul_sum]
  rw [hkin, show NBody.kineticEnergy (fun _ : Fin 3 => m) (z a).2 = 0 by
    simp [NBody.kineticEnergy, hrest]] at hE
  have hinit (i j : Fin 3) : 0 ≤ dist ((z a).1 i) ((z a).1 j) ^ (-α) :=
    Real.rpow_nonneg (dist_nonneg) _
  have hbound (i j : Fin 3) (hij : i ≠ j) :=
    Real.rpow_le_rpow_of_nonpos hδ (hsep i j hij) (neg_nonpos.mpr hα.le)
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith [mul_nonneg hg.le (hinit 0 1), mul_nonneg hg.le (hinit 0 2),
    mul_nonneg hg.le (hinit 1 2), mul_le_mul_of_nonneg_left (hbound 0 1 (by decide)) hg.le,
    mul_le_mul_of_nonneg_left (hbound 0 2 (by decide)) hg.le,
    mul_le_mul_of_nonneg_left (hbound 1 2 (by decide)) hg.le]

private theorem relative_sq_le_double_sum (v : Fin 3 → Point) :
    ‖v 0 - v 1‖ ^ 2 ≤ 2 * ∑ i, ‖v i‖ ^ 2 := by
  have hsum := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
    (norm_sub_le (v 0) (v 1))
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  nlinarith [sq_nonneg (‖v 0‖ - ‖v 1‖), sq_nonneg ‖v 2‖]

/-- At the inverse-square potential, distance times relative speed is bounded. -/
theorem power_critical_relative_speed {g m : ℝ} {z : ℝ → Phase} {I : Set ℝ} {a t : ℝ}
    (hsol : EqualPowerSolution 2 g m z I) (hg : 0 < g) (hm : 0 < m)
    (hconn : IsPreconnected I) (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (hshort : ∀ j k : Fin 3, j ≠ k →
      dist ((z t).1 0) ((z t).1 1) ≤ dist ((z t).1 j) ((z t).1 k)) :
    dist ((z t).1 0) ((z t).1 1) * ‖(z t).2 0 - (z t).2 1‖ ≤ Real.sqrt (12 * g / m) := by
  let r := dist ((z t).1 0) ((z t).1 1)
  have hr : 0 < r := dist_pos.mpr ((hsol.2 t ht).1 0 1 (by decide))
  have hsum := power_speed_sum_bound hsol (by norm_num) hg hm hconn ha ht hrest hr hshort
  have hrel := (relative_sq_le_double_sum (z t).2).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 2))
  change _ ≤ 2 * (6 * g / m * r ^ (-(2 : ℝ))) at hrel
  rw [Real.rpow_neg hr.le, Real.rpow_two] at hrel
  have hmul := mul_le_mul_of_nonneg_left hrel (sq_nonneg r)
  change r * _ ≤ _
  apply (sq_le_sq₀ (mul_nonneg hr.le (norm_nonneg _)) (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt (by positivity), mul_pow]
  calc
    _ ≤ r ^ 2 * (2 * (6 * g / m * (r ^ 2)⁻¹)) := hmul
    _ = _ := by field_simp [hr.ne', hm.ne']; ring

/-- A shortest side with persistent angular momentum has a quantitative subcritical barrier. -/
theorem power_subcritical_distance_bound {α g m k : ℝ} {z : ℝ → Phase} {I : Set ℝ} {a t : ℝ}
    (hsol : EqualPowerSolution α g m z I) (hα : 0 < α) (hα2 : α < 2)
    (hg : 0 < g) (hm : 0 < m)
    (hconn : IsPreconnected I) (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (hshort : ∀ j l : Fin 3, j ≠ l →
      dist ((z t).1 0) ((z t).1 1) ≤ dist ((z t).1 j) ((z t).1 l))
    (hrot : k ^ 2 ≤ cross (sideVector (z t).1 2) (sideVector (z t).2 2) ^ 2) :
    (k ^ 2 * m / (12 * g)) ^ (2 - α)⁻¹ ≤ dist ((z t).1 0) ((z t).1 1) := by
  let r := dist ((z t).1 0) ((z t).1 1)
  have hr : 0 < r := dist_pos.mpr ((hsol.2 t ht).1 0 1 (by decide))
  have hsum := power_speed_sum_bound hsol hα hg hm hconn ha ht hrest hr hshort
  have hK := hrot.trans (sidePairRotation_sq_le_four_sideSq_mul_kinetic (z t).1 (z t).2 2)
  have hsq : sideSq (z t).1 2 = r ^ 2 := by
    rw [sideSq_eq_cyclicNeighborDistance]
    simp [r, cyclicPrev, cyclicNext, dist_comm]
  rw [hsq] at hK
  change _ ≤ 4 * r ^ 2 * ((1/2:ℝ) * ∑ i : Fin 3, ‖(z t).2 i‖ ^ 2) at hK
  change _ ≤ r
  apply (Real.rpow_inv_le_iff_of_pos (by positivity) hr.le (sub_pos.mpr hα2)).2
  rw [div_le_iff₀ (by positivity : 0 < 12 * g)]
  have hpow : r ^ (2 - α) = r ^ 2 * r ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_two]
  rw [hpow]
  calc
    k ^ 2 * m ≤ (4 * r ^ 2 * ((1/2:ℝ) * ∑ i : Fin 3, ‖(z t).2 i‖ ^ 2)) * m :=
      mul_le_mul_of_nonneg_right hK hm.le
    _ ≤ (4 * r ^ 2 * ((1/2:ℝ) * (6 * g / m * r ^ (-α)))) * m := by gcongr
    _ = _ := by field_simp [hm.ne']; ring

/-- The two force terms per body are bounded uniformly away from collisions. -/
theorem power_acceleration_norm_bound {α g m δ : ℝ} (q : Fin 3 → Point)
    (hα : 0 < α) (hg : 0 < g) (hm : 0 < m) (hδ : 0 < δ)
    (hsep : ∀ j k : Fin 3, j ≠ k → δ ≤ dist (q j) (q k)) (i : Fin 3) :
    ‖acceleration (powerCoefficients α (commonCouplings g)) (fun _ => m) q i‖ ≤
      2 * (α * g / m) * δ ^ (-α - 1) := by
  let B := (α * g / m) * δ ^ (-α - 1)
  have hterm (j : Fin 3) :
      ‖(if j = i then (0 : Point) else
          (weight (powerCoefficients α (commonCouplings g)) q i j / m) • (q j - q i))‖ ≤
        (if j = i then 0 else B) := by
    by_cases hji : j = i
    · simp [hji]
    have hij : i ≠ j := Ne.symm hji
    simp only [if_neg hji, norm_smul, Real.norm_eq_abs]
    have hr := hδ.trans_le (hsep i j hij)
    have hn : ‖q j - q i‖ = dist (q i) (q j) := by rw [dist_eq_norm, norm_sub_rev]
    simp only [weight, powerCoefficients, commonCouplings_offDiag _ hij]
    have hval : 0 ≤ α * g * Real.rpow (dist (q i) (q j)) (-α - 2) / m :=
      (div_pos (mul_pos (mul_pos hα hg) (Real.rpow_pos_of_pos hr _)) hm).le
    rw [abs_of_nonneg hval, hn]
    let r := dist (q i) (q j)
    change α * g * r ^ (-α - 2) / m * r ≤ B
    calc
      _ = (α * g / m) * (r ^ (-α - 2) * r) := by ring
      _ = (α * g / m) * r ^ (-α - 1) := by
        rw [← Real.rpow_add_one hr.ne', show -α - 2 + 1 = -α - 1 by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hδ (hsep i j hij) (by linarith)) (by positivity)
  unfold acceleration
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun j _ => hterm j).trans
  rw [sum_fin_three, mul_assoc]
  change _ ≤ 2 * B
  fin_cases i <;> simp (disch := decide) only [if_pos, if_neg, add_zero, zero_add] <;> linarith

/-- From rest, separation controls the entire phase derivative at any later time. -/
theorem power_field_bound {α g m : ℝ} {z : ℝ → Phase} {I : Set ℝ} {a t δ : ℝ}
    (hsol : EqualPowerSolution α g m z I) (hα : 0 < α) (hg : 0 < g) (hm : 0 < m)
    (hconn : IsPreconnected I) (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (hδ : 0 < δ) (hsep : ∀ j k : Fin 3, j ≠ k → δ ≤ dist ((z t).1 j) ((z t).1 k)) :
    ‖vectorField (powerCoefficients α (commonCouplings g)) (fun _ => m) (z t)‖ ≤
      max (Real.sqrt (6 * g / m * δ ^ (-α))) (2 * (α * g / m) * δ ^ (-α - 1)) := by
  have hs := power_speed_sum_bound hsol hα hg hm hconn ha ht hrest hδ hsep
  apply max_le_max
  · apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    have hi : ‖(z t).2 i‖ ^ 2 ≤ ∑ j : Fin 3, ‖(z t).2 j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖(z t).2 j‖) (Finset.mem_univ i)
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (by positivity)]
    exact hi.trans hs
  · exact (pi_norm_le_iff_of_nonneg (by positivity)).2
      (power_acceleration_norm_bound (z t).1 hα hg hm hδ hsep)

end
end DroppingThreeBodies.CentralForce
