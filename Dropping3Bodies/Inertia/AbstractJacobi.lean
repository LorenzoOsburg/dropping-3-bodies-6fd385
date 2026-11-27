module

public import Dropping3Bodies.Inertia.JacobiRiccati

@[expose] public section

/-! Abstract planar Jacobi dynamics. No force law or particle configuration is
part of the hypotheses. The existing entrywise matrix calculus is reused. -/

namespace DroppingThreeBodies.AbstractJacobi

noncomputable section

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- A second-order matrix equation on an open time domain. -/
structure System (Q V K : ℝ → Mat) (I : Set ℝ) : Prop where
  isOpen : IsOpen I
  position : ∀ t ∈ I, HasDerivAt Q (V t) t
  velocity : ∀ t ∈ I, HasDerivAt V (-(Q t * K t)) t

def PositiveForce (K : ℝ → Mat) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, (K t).transpose = K t ∧
    ∀ w : Fin 2 → ℝ, w ≠ 0 → 0 < matrixQuadratic (K t) w

def riccati (Q V : ℝ → Mat) (t : ℝ) : Mat := (Q t)⁻¹ * V t

/-- Every closed segment from the initial instant stays regular and invertible. -/
def initialBranch (Q : ℝ → Mat) (I : Set ℝ) (a : ℝ) : Set ℝ :=
  {t | a ≤ t ∧ Set.Icc a t ⊆ I ∧ ∀ s ∈ Set.Icc a t, (Q s).det ≠ 0}

variable {Q V K : ℝ → Mat} {I : Set ℝ} {a t : ℝ}

theorem mul_hasDerivAt {A B : ℝ → Mat} {A' B' : Mat} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  simpa only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib] using
    hasDerivAt_matrixMul_entry
      (fun r c => hasDerivAt_pi.1 (hasDerivAt_pi.1 hA r) c)
      (fun r c => hasDerivAt_pi.1 (hasDerivAt_pi.1 hB r) c) i j

theorem System.skew_deriv_zero (h : System Q V K I)
    (hK : ∀ s ∈ I, (K s).transpose = K s) (ht : t ∈ I) (i j : Fin 2) :
    HasDerivAt (fun s => matrixSkewCurve Q V s i j) 0 t :=
  hasDerivAt_matrixSkewCurve_entry_zero
    (fun r c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (h.position t ht) r) c)
    (fun r c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (h.velocity t ht) r) c)
    (hK t ht) i j

theorem System.skew_eq (h : System Q V K I)
    (hK : ∀ s ∈ I, (K s).transpose = K s) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    matrixSkewCurve Q V s = matrixSkewCurve Q V t := by
  ext i j
  change (fun u => matrixSkewCurve Q V u i j) s =
    (fun u => matrixSkewCurve Q V u i j) t
  apply h.isOpen.is_const_of_deriv_eq_zero
    (f := fun u => matrixSkewCurve Q V u i j) hconn
  · intro u hu
    exact (h.skew_deriv_zero hK hu i j).differentiableAt.differentiableWithinAt
  · intro u hu
    exact (h.skew_deriv_zero hK hu i j).deriv
  · exact hs
  · exact ht

theorem System.skew_zero_of_rest (h : System Q V K I)
    (hK : ∀ s ∈ I, (K s).transpose = K s) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : V a = 0) :
    matrixSkewCurve Q V t = 0 := by
  rw [← h.skew_eq hK hconn ha ht]
  simp [matrixSkewCurve, hrest]

theorem System.riccati_symmetric (h : System Q V K I)
    (hK : ∀ s ∈ I, (K s).transpose = K s) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : V a = 0) (hdet : (Q t).det ≠ 0) :
    (riccati Q V t).transpose = riccati Q V t :=
  matrix_nonsingInv_mul_velocity_symmetric_of_skew_zero _ _
    (isUnit_iff_ne_zero.mpr hdet) (h.skew_zero_of_rest hK hconn ha ht hrest)

theorem System.riccati_hasDerivAt (h : System Q V K I)
    (ht : t ∈ I) (hdet : (Q t).det ≠ 0) :
    HasDerivAt (riccati Q V)
      (-(riccati Q V t * riccati Q V t + K t)) t := by
  have hinv : HasDerivAt (fun s => (Q s)⁻¹)
      (-((Q t)⁻¹ * V t * (Q t)⁻¹)) t := by
    apply hasDerivAt_pi.2
    intro i
    apply hasDerivAt_pi.2
    intro j
    exact hasDerivAt_matrixInv_finTwo_formula_entry
      (fun r c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (h.position t ht) r) c)
      hdet i j
  have hd := mul_hasDerivAt hinv (h.velocity t ht)
  have hMQ : (Q t)⁻¹ * Q t = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have heq : -((Q t)⁻¹ * V t * (Q t)⁻¹) * V t +
      (Q t)⁻¹ * -(Q t * K t) =
      -(riccati Q V t * riccati Q V t + K t) := by
    change _ = -(((Q t)⁻¹ * V t) * ((Q t)⁻¹ * V t) + K t)
    calc
      _ = -(((Q t)⁻¹ * V t) * ((Q t)⁻¹ * V t)) -
          ((Q t)⁻¹ * Q t) * K t := by noncomm_ring
      _ = _ := by rw [hMQ]; noncomm_ring
  rw [heq] at hd
  exact hd

theorem System.riccati_deriv (h : System Q V K I)
    (ht : t ∈ I) (hdet : (Q t).det ≠ 0) (i j : Fin 2) :
    HasDerivAt (fun s => riccati Q V s i j)
      (-(riccati Q V t * riccati Q V t + K t) i j) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (h.riccati_hasDerivAt ht hdet) i) j

theorem System.riccati_quadratic_deriv_neg (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : V a = 0) (hdet : (Q t).det ≠ 0)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    deriv (fun s => matrixQuadratic (riccati Q V s) w) t < 0 := by
  rw [(hasDerivAt_matrixQuadratic_curve (h.riccati_deriv ht hdet)).deriv]
  have hn := matrixQuadratic_riccati_rhs_neg _ _ w
    (h.riccati_symmetric (fun s hs => (hK s hs).1) hconn ha ht hrest hdet)
    ((hK t ht).2 w hw)
  have heq : (fun i j => -(riccati Q V t * riccati Q V t + K t) i j) =
      -(riccati Q V t * riccati Q V t) - K t := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [heq]
  exact hn

theorem System.riccati_quadratic_strictAntiOn (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) {s t : ℝ}
    (hIcc : Set.Icc s t ⊆ I) (hdet : ∀ u ∈ Set.Icc s t, (Q u).det ≠ 0)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    StrictAntiOn (fun u => matrixQuadratic (riccati Q V u) w) (Set.Icc s t) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc s t)
  · intro u hu
    exact (hasDerivAt_matrixQuadratic_curve
      (h.riccati_deriv (hIcc hu) (hdet u hu))).continuousAt.continuousWithinAt
  · intro u hu
    exact h.riccati_quadratic_deriv_neg hK hconn ha (hIcc (interior_subset hu))
      hrest (hdet u (interior_subset hu)) w hw

theorem System.riccati_quadratic_neg_of_rest (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0)
    (ht : t ∈ initialBranch Q I a) (hat : a < t)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    matrixQuadratic (riccati Q V t) w < 0 := by
  have hanti := h.riccati_quadratic_strictAntiOn hK hconn ha hrest ht.2.1 ht.2.2 w hw
  have hn := hanti ⟨le_rfl, hat.le⟩ ⟨hat.le, le_rfl⟩ hat
  simpa [riccati, hrest, matrixQuadratic] using hn

end
end DroppingThreeBodies.AbstractJacobi
