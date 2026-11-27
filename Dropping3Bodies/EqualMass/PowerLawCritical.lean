module

public import Dropping3Bodies.EqualMass.PowerLawComparison
public import Dropping3Bodies.EqualMass.PowerLawEnergy
public import Dropping3Bodies.EqualMass.PowerLawGeometry
public import Dropping3Bodies.Dynamics.SyzygyAngle
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Collision exclusion at the critical inverse-square potential. The angle coordinate
of the Newtonian development differentiates on either component of nonzero area. -/

namespace DroppingThreeBodies.CentralForce

noncomputable section

/-- The two adjacent angular velocities give the derivative of the branch-free
angle coordinate. Its sign is reversed for the physical angle in negative orientation. -/
theorem triangleAngle_hasDerivAt_rotation_difference
    {κ : Coefficients} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : Solution κ m z I) (ht : t ∈ I) (hB : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (triangleAngleCurve z 0)
      (framePairRotation (sideVector (z t).1 1) (sideVector (z t).2 1) /
          (dist ((z t).1 0) ((z t).1 2)) ^ 2 -
        framePairRotation (sideVector (z t).1 2) (sideVector (z t).2 2) /
          (dist ((z t).1 0) ((z t).1 1)) ^ 2) t := by
  let u := angleNextRayCurve z 0
  let v := anglePrevRayCurve z 0
  let du := (z t).2 1 - (z t).2 0
  let dv := (z t).2 2 - (z t).2 0
  have hu : HasDerivAt u du t := (body_derivatives hsol ht 1).1.sub (body_derivatives hsol ht 0).1
  have hv : HasDerivAt v dv t := (body_derivatives hsol ht 2).1.sub (body_derivatives hsol ht 0).1
  have harea : cross (u t) (v t) ≠ 0 := hB
  have hquot := (hasDerivAt_dot2_curve hu hv).div (hasDerivAt_cross_curve hu hv) harea
  have hangle := ((Real.hasDerivAt_arctan _).comp t hquot).const_sub (Real.pi / 2)
  change HasDerivAt (fun s => Real.pi / 2 - Real.arctan (dot2 (u s) (v s) / cross (u s) (v s))) _ t
  apply hangle.congr_deriv
  have hnum := dotCross_derivativeNumerator_identity (u t) (v t) du dv
  have hden := cross_sq_add_dot2_sq (u t) (v t)
  have hcf := (hsol.2 t ht).1
  have hU : ‖u t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hcf 1 0 (by decide)))
  have hV : ‖v t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hcf 2 0 (by decide)))
  have hU2 : dist ((z t).1 0) ((z t).1 1) = ‖u t‖ := dist_comm _ _
  have hV2 : dist ((z t).1 0) ((z t).1 2) = ‖v t‖ := dist_comm _ _
  have hK1 : framePairRotation (sideVector (z t).1 1) (sideVector (z t).2 1) = cross (v t) dv := by
    simp [framePairRotation, sideVector, v, dv, anglePrevRayCurve, cyclicPrev, cross]
    ring
  have hK2 : framePairRotation (sideVector (z t).1 2) (sideVector (z t).2 2) = cross (u t) du := rfl
  rw [hU2, hV2, hK1, hK2]
  rw [← norm_sq_eq_dot2, ← norm_sq_eq_dot2] at hnum
  dsimp only [Function.comp_apply, Pi.div_apply] at *
  field_simp [harea, hU, hV]
  linear_combination hnum * (‖u t‖ ^ 2 * ‖v t‖ ^ 2) +
    hden * (cross (u t) du * ‖v t‖ ^ 2 - cross (v t) dv * ‖u t‖ ^ 2)

/-- On a tail with nonzero shortest-side angular momentum, the bounded angle
controls the logarithm of the distance whenever the relative speed is at most C/r. -/
theorem critical_tail_distance_of_rotation_and_speed
    {κ : Coefficients} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    {t₀ T k C σ : ℝ} (hsol : Solution κ m z I) (hseg : Set.Ico t₀ T ⊆ I)
    (ht₀ : t₀ < T) (hk : 0 < k) (hC : 0 ≤ C) (hσ : σ = 1 ∨ σ = -1)
    (harea : ∀ t ∈ Set.Ico t₀ T, signedDoubleArea (z t).1 ≠ 0)
    (hK : ∀ t ∈ Set.Ico t₀ T,
      0 ≤ σ * framePairRotation (sideVector (z t).1 1) (sideVector (z t).2 1) ∧
      k ≤ -(σ * framePairRotation (sideVector (z t).1 2) (sideVector (z t).2 2)))
    (hspeed : ∀ t ∈ Set.Ico t₀ T, dist ((z t).1 0) ((z t).1 1) *
      ‖(z t).2 0 - (z t).2 1‖ ≤ C) :
    ∃ δ > 0, ∀ t ∈ Set.Ico t₀ T, δ ≤ dist ((z t).1 0) ((z t).1 1) := by
  let r := fun t => dist ((z t).1 0) ((z t).1 1)
  let θ := fun t => σ * triangleAngleCurve z 0 t
  let F := fun t => k * Real.log (r t ^ 2) + (2 * C) * θ t
  have hr {t} (ht : t ∈ Set.Ico t₀ T) : 0 < r t :=
    dist_pos.mpr ((hsol.2 t (hseg ht)).1 0 1 (by decide))
  have hθ {t} : θ t ≤ Real.pi := by
    have h := triangleAngleCurve_mem_Ioo z 0 t
    rcases hσ with hσ | hσ <;> simp only [θ, hσ, one_mul, neg_mul] <;> linarith [h.1, h.2]
  have hder {t} (ht : t ∈ Set.Ico t₀ T) : ∃ d, HasDerivAt F d t ∧ 0 ≤ d := by
    let u := (z t).1 0 - (z t).1 1
    let w := (z t).2 0 - (z t).2 1
    let v := inner ℝ u w
    have hsq : HasDerivAt (fun s => r s ^ 2) (2 * v) t :=
      ((body_derivatives hsol (hseg ht) 0).1.sub (body_derivatives hsol (hseg ht) 1).1).norm_sq
    have hv : -C ≤ v := by
      have habs := abs_real_inner_le_norm u w
      have hs : ‖u‖ * ‖w‖ ≤ C := hspeed t ht
      exact (abs_le.mp (habs.trans hs)).1
    have hl := hsq.log (sq_pos_of_pos (hr ht)).ne'
    let K := fun (i : Fin 3) => framePairRotation (sideVector (z t).1 i) (sideVector (z t).2 i)
    let d := dist ((z t).1 0) ((z t).1 2)
    let ω := σ * (K 1 / d ^ 2 - K 2 / r t ^ 2)
    have ha : HasDerivAt θ ω t :=
      (triangleAngle_hasDerivAt_rotation_difference hsol (hseg ht) (harea t ht)).const_mul σ
    have hω : k / r t ^ 2 ≤ ω := by
      obtain ⟨h1, h2⟩ := hK t ht
      change 0 ≤ σ * K 1 at h1
      change k ≤ -(σ * K 2) at h2
      have hsecond := div_le_div_of_nonneg_right h2 (sq_nonneg (r t))
      have hfirst := div_nonneg h1 (sq_nonneg d)
      dsimp [ω]
      rw [mul_sub, mul_div_assoc', mul_div_assoc']
      rw [neg_div] at hsecond
      linarith
    refine ⟨_, (hl.const_mul k).add (ha.const_mul (2*C)), ?_⟩
    calc
      0 = k * (2 * (-C) / r t ^ 2) + (2*C) * (k / r t ^ 2) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith : 2 * (-C) ≤ 2 * v) (sq_nonneg _)) hk.le)
        (mul_le_mul_of_nonneg_left hω (by positivity))
  have hmono : MonotoneOn F (Set.Ico t₀ T) := by
    apply monotoneOn_of_hasDerivAt_nonneg (g := deriv F) (convex_Ico t₀ T)
    · intro t ht
      exact (hder ht).choose_spec.1.differentiableAt.hasDerivAt
    · intro t ht
      rw [(hder ht).choose_spec.1.deriv]
      exact (hder ht).choose_spec.2
  refine ⟨Real.exp ((F t₀ - 2*C*Real.pi) / (2*k)), Real.exp_pos _, ?_⟩
  intro t ht
  apply (Real.le_log_iff_exp_le (hr ht)).mp
  apply (div_le_iff₀ (by positivity : 0 < 2*k)).mpr
  have hcomp := hmono ⟨le_rfl, ht₀⟩ ht ht.1
  change F t₀ ≤ k * Real.log (r t ^ 2) + (2*C) * θ t at hcomp
  rw [Real.log_pow] at hcomp
  norm_num at hcomp
  nlinarith [mul_le_mul_of_nonneg_left (hθ (t := t)) (show 0 ≤ 2*C by positivity)]

private theorem signed_rotation_signs {B f₁ f₂ u v : ℝ}
    (hB : B ≠ 0) (hf₁ : f₁ < 0) (hf₂ : 0 < f₂)
    (hu : 0 < -(f₁ / B) * u) (hv : 0 < -(f₂ / B) * v) :
    let σ : ℝ := if 0 < B then 1 else -1
    0 ≤ σ * u ∧ -(σ * v) = |v| ∧ 0 < |v| := by
  by_cases h : 0 < B
  · have h₁ : 0 < -(f₁ / B) := neg_pos.mpr (div_neg_of_neg_of_pos hf₁ h)
    have h₂ : -(f₂ / B) < 0 := neg_neg_of_pos (div_pos hf₂ h)
    have hu' := (mul_pos_iff_of_pos_left h₁).mp hu
    have hv' : v < 0 := by rcases mul_pos_iff.mp hv with h | h <;> linarith [h.1, h.2]
    simpa [h, abs_of_neg hv'] using
      (show 0 ≤ u ∧ -v = -v ∧ 0 < -v from ⟨hu'.le, rfl, neg_pos.mpr hv'⟩)
  · have h' : B < 0 := lt_of_le_of_ne (le_of_not_gt h) hB
    have h₁ : -(f₁ / B) < 0 := neg_neg_of_pos (div_pos_of_neg_of_neg hf₁ h')
    have h₂ : 0 < -(f₂ / B) := neg_pos.mpr (div_neg_of_pos_of_neg hf₂ h')
    have hu' : u < 0 := by rcases mul_pos_iff.mp hu with h | h <;> linarith [h.1, h.2]
    have hv' := (mul_pos_iff_of_pos_left h₂).mp hv
    simpa [h, abs_of_pos hv'] using
      (show 0 ≤ -u ∧ v = v ∧ 0 < v from ⟨(neg_pos.mpr hu').le, rfl, hv'⟩)

/-- Uniform separation on every terminal part of the noncollinear initial interval
for the critical exponent. Side ordering and the lower bound for pair rotation
both follow from the initial scalene chain. -/
theorem power_critical_shortest_distance_uniform
    {g m : ℝ} {z : ℝ → Phase} {I : Set ℝ} {a t₀ T : ℝ}
    (hs : EqualPowerSolution 2 g m z I) (hg : 0 < g) (hm : 0 < m)
    (hc : IsPreconnected I) (hat₀ : a < t₀) (ht₀T : t₀ < T)
    (hseg : Set.Ico a T ⊆ I) (hrest : ∀ j, (z a).2 j = 0)
    (harea : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z a).1 * signedDoubleArea (z t).1)
    (h01 : sideSq (z a).1 1 < sideSq (z a).1 0)
    (h12 : sideSq (z a).1 2 < sideSq (z a).1 1) :
    ∃ δ > 0, ∀ t ∈ Set.Ico t₀ T, ∀ j l : Fin 3, j ≠ l → δ ≤ dist ((z t).1 j) ((z t).1 l) := by
  have ha : a ∈ Set.Ico a T := ⟨le_rfl, hat₀.trans ht₀T⟩
  have htail {t} (ht : t ∈ Set.Ico t₀ T) : t ∈ Set.Ico a T :=
    ⟨hat₀.le.trans ht.1, ht.2⟩
  have hcomp {t} (ht : t ∈ Set.Ico t₀ T) (i : Fin 3) (hi : sideGap (z a).1 i ≠ 0) :=
    power_gap_comparison hs (by norm_num) hg hm hc (htail ht).1
      (fun s (hs' : s ∈ Set.Icc a t) => hseg ⟨hs'.1, hs'.2.trans_lt ht.2⟩) hrest
      (fun s hs' => harea s ⟨hs'.1, hs'.2.trans_lt ht.2⟩) i hi
  obtain ⟨hf₂, hf₀⟩ := (positive_gaps_iff_side_order _).2 ⟨h01, h12⟩
  have hf₁ : sideGap (z a).1 1 < 0 := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    exact sub_neg.mpr (h12.trans h01)
  have hshort {t} (ht : t ∈ Set.Ico t₀ T) :=
    shortest_distance_of_side_order ((positive_gaps_iff_side_order _).1
      ⟨(mul_pos_iff_of_pos_left hf₂).mp ((hcomp ht 2 hf₂.ne').1 t ⟨(htail ht).1, le_rfl⟩),
       (mul_pos_iff_of_pos_left hf₀).mp ((hcomp ht 0 hf₀.ne').1 t ⟨(htail ht).1, le_rfl⟩)⟩)
  let B := signedDoubleArea (z a).1
  let σ : ℝ := if 0 < B then 1 else -1
  have hB : B ≠ 0 := by
    intro h
    have hp : 0 < B * B := harea a ha
    simp [h] at hp
  have hsign {t} (ht : t ∈ Set.Ico t₀ T) :
      0 ≤ σ * powerPairRotation z 1 t ∧
      -(σ * powerPairRotation z 2 t) = |powerPairRotation z 2 t| ∧
      0 < |powerPairRotation z 2 t| := by
    exact signed_rotation_signs hB hf₁ hf₂
      ((hcomp ht 1 hf₁.ne).2.2 t ⟨hat₀.trans_le ht.1, le_rfl⟩)
      ((hcomp ht 2 hf₂.ne').2.2 t ⟨hat₀.trans_le ht.1, le_rfl⟩)
  have ht₀ : t₀ ∈ Set.Ico t₀ T := ⟨le_rfl, ht₀T⟩
  obtain ⟨δ, hδ, hbound⟩ := critical_tail_distance_of_rotation_and_speed
    (k := |powerPairRotation z 2 t₀|) (C := Real.sqrt (12*g/m)) (σ := σ)
    hs (fun _ ht => hseg (htail ht)) ht₀T (hsign ht₀).2.2 (Real.sqrt_nonneg _)
    (by by_cases h : 0 < B <;> simp [σ, h])
    (fun t ht => by
      have hp := harea t (htail ht)
      exact fun h => by simp [h] at hp)
    (fun t ht => by
      refine ⟨(hsign ht).1, ?_⟩
      change |powerPairRotation z 2 t₀| ≤ -(σ * powerPairRotation z 2 t)
      rw [(hsign ht).2.1]
      exact (hcomp ht 2 hf₂.ne').2.1.monotoneOn ⟨hat₀.le, ht.1⟩ ⟨(htail ht).1, le_rfl⟩ ht.1)
    (fun t ht => power_critical_relative_speed hs hg hm hc (hseg ha) (hseg (htail ht))
      hrest (hshort ht))
  exact ⟨δ, hδ, fun t ht j l hjl => (hbound t ht).trans (hshort ht j l hjl)⟩

end
end DroppingThreeBodies.CentralForce
