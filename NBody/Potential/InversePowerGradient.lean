module

public import NBody.Potential.InversePower
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi

@[expose] public section

/-! The configuration derivative and particle gradients of the inverse-power
potential. The factor one half in the ordered-pair sum cancels the two equal
contributions from each unordered pair. No sign restrictions are needed for the
derivative identities; attraction is a separate condition on the parameters. -/

namespace NBody
noncomputable section

private theorem hasFDerivAt_norm_rpow_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => Real.rpow ‖y‖ p)
      ((p * Real.rpow ‖x‖ (p - 2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

omit [DecidableEq ι] in
private theorem hasFDerivAt_pairPower (α : ℝ) (c : SymmetricCouplings ι)
    {q : Config ι d} {i j : ι} (hij : q i ≠ q j) :
    HasFDerivAt (fun p : Config ι d => c.coeff i j * Real.rpow (dist (p i) (p j)) (-α))
      ((-α * c.coeff i j * Real.rpow (dist (q i) (q j)) (-α - 2)) •
        (innerSL ℝ (q i - q j)).comp
          ((ContinuousLinearMap.proj i : Config ι d →L[ℝ] EuclideanSpace ℝ (Fin d)) -
            ContinuousLinearMap.proj j)) q := by
  have hd := ((hasFDerivAt_norm_rpow_of_ne_zero (-α) (sub_ne_zero.mpr hij)).comp q
    ((hasFDerivAt_apply (𝕜 := ℝ) i q).sub
      (hasFDerivAt_apply (𝕜 := ℝ) j q))).const_mul (c.coeff i j)
  simpa only [dist_eq_norm, ContinuousLinearMap.smul_comp, smul_smul,
    mul_assoc, mul_left_comm, mul_comm] using! hd

/-- The full configuration derivative of the potential is minus the pairing
with the existing force. Valid for every real exponent and symmetric coupling. -/
theorem hasFDerivAt_inversePowerPotential (α : ℝ) (c : SymmetricCouplings ι)
    {q : Config ι d} (hq : CollisionFree q) :
    HasFDerivAt (inversePowerPotential α c)
      (-∑ i, (innerSL ℝ (inversePowerForce α c q i)).comp
        (ContinuousLinearMap.proj i)) q := by
  let F : ι → ι → EuclideanSpace ℝ (Fin d) := fun i j =>
    if i = j then 0 else (α * c.coeff i j *
      Real.rpow (dist (q i) (q j)) (-α - 2)) • (q j - q i)
  have hF : ∀ i j, F j i = -F i j := by
    intro i j
    by_cases hij : i = j
    · simp [F, hij]
    · simp only [F, if_neg hij, if_neg (Ne.symm hij)]
      rw [c.symmetric j i, dist_comm (q j), ← neg_sub (q j) (q i), smul_neg]
  have hp : ∀ i j, HasFDerivAt
      (fun p : Config ι d => if i = j then 0 else
        c.coeff i j * Real.rpow (dist (p i) (p j)) (-α))
      ((innerSL ℝ (F i j)).comp
        ((ContinuousLinearMap.proj i : Config ι d →L[ℝ] EuclideanSpace ℝ (Fin d)) -
          ContinuousLinearMap.proj j)) q := by
    intro i j
    by_cases hij : i = j
    · simpa [hij, F] using! (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) q)
    · simp only [if_neg hij]
      convert! hasFDerivAt_pairPower α c (hq i j hij) using 1
      ext v
      simp [F, hij]
      ring
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hp i j).const_mul (-(1 / 2 : ℝ))
  convert! hd using 1
  symm
  ext v
  simp only [smul_apply, neg_apply,
    sum_apply, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply_apply, smul_eq_mul]
  change -(1 / 2 : ℝ) * (∑ i, ∑ j, inner ℝ (F i j) (v i - v j)) =
    -(∑ i, inner ℝ (∑ j, F i j) (v i))
  simp only [inner_sub_right, Finset.sum_sub_distrib, sum_inner]
  have hswap : (∑ i, ∑ j, inner ℝ (F i j) (v j)) =
      -(∑ i, ∑ j, inner ℝ (F i j) (v i)) := by
    calc
      _ = ∑ i, ∑ j, inner ℝ (F j i) (v i) := Finset.sum_comm
      _ = ∑ i, ∑ j, -inner ℝ (F i j) (v i) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hF i j, inner_neg_left]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  rw [hswap]
  ring

/-- Directional form of the genuine Fréchet derivative. -/
theorem fderiv_inversePowerPotential_apply (α : ℝ) (c : SymmetricCouplings ι)
    {q : Config ι d} (hq : CollisionFree q) (v : Config ι d) :
    fderiv ℝ (inversePowerPotential α c) q v =
      -∑ i, inner ℝ (inversePowerForce α c q i) (v i) := by
  rw [(hasFDerivAt_inversePowerPotential α c hq).fderiv]
  simp

/-- The gradient with respect to particle `i`, with all other positions fixed. -/
theorem hasGradientAt_inversePowerPotential_particle (α : ℝ) (c : SymmetricCouplings ι)
    {q : Config ι d} (hq : CollisionFree q) (i : ι) :
    HasGradientAt (fun x => inversePowerPotential α c (Function.update q i x))
      (-inversePowerForce α c q i) (q i) := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hasFDerivAt_inversePowerPotential α c
    (q := Function.update q i (q i)) (by simpa using hq)).comp (q i)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) q (q i))
  simp only [Function.update_eq_self] at hd
  convert! hd using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply, Pi.single_apply, ite_apply, apply_ite]

/-- The existing force is exactly the negative particle gradient. -/
theorem inversePowerForce_eq_neg_gradient (α : ℝ) (c : SymmetricCouplings ι)
    {q : Config ι d} (hq : CollisionFree q) (i : ι) :
    inversePowerForce α c q i =
      -gradient (fun x => inversePowerPotential α c (Function.update q i x)) (q i) := by
  rw [(hasGradientAt_inversePowerPotential_particle α c hq i).gradient, neg_neg]

end
end NBody
