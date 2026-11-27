module

public import Dropping3Bodies.Inertia.AbstractJacobi
public import Dropping3Bodies.Inertia.RegularEndpointDerivative

@[expose] public section

/-! Tensor and scalar contraction, including a conditional regular endpoint.
Only the abstract matrix equation is assumed. -/

namespace DroppingThreeBodies.AbstractJacobi
noncomputable section

def spatial (Q : ℝ → Mat) (t : ℝ) : Mat := Q t * (Q t).transpose
def spatialRate (Q V : ℝ → Mat) (t : ℝ) : Mat :=
  V t * (Q t).transpose + Q t * (V t).transpose
def inertia (Q : ℝ → Mat) (t : ℝ) : ℝ := Matrix.trace (spatial Q t)
def inertiaRate (Q V : ℝ → Mat) (t : ℝ) : ℝ :=
  2 * ∑ i : Fin 2, ∑ j : Fin 2, Q t i j * V t i j

variable {Q V K : ℝ → Mat} {I : Set ℝ} {a t : ℝ}

theorem transpose_hasDerivAt {A : ℝ → Mat} {A' : Mat} {t : ℝ}
    (h : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).transpose) A'.transpose t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h j) i

theorem System.spatial_hasDerivAt (h : System Q V K I) (ht : t ∈ I) :
    HasDerivAt (spatial Q) (spatialRate Q V t) t :=
  mul_hasDerivAt (h.position t ht) (transpose_hasDerivAt (h.position t ht))

theorem System.inertia_hasDerivAt (h : System Q V K I) (ht : t ∈ I) :
    HasDerivAt (inertia Q) (inertiaRate Q V t) t := by
  have hd := h.spatial_hasDerivAt ht
  have hh := (hasDerivAt_pi.1 (hasDerivAt_pi.1 hd 0) 0).add
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hd 1) 1)
  have hh' : HasDerivAt (inertia Q)
      (spatialRate Q V t 0 0 + spatialRate Q V t 1 1) t := by
    change HasDerivAt (fun s => Matrix.trace (spatial Q s)) _ t
    simpa only [Matrix.trace, Fin.sum_univ_two, Matrix.diag] using! hh
  apply hh'.congr_deriv
  simp [spatialRate, inertiaRate, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem velocity_eq_mul_riccati (hdet : (Q t).det ≠ 0) :
    V t = Q t * riccati Q V t := by
  simp [riccati, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)]

theorem System.inertiaRate_eq_rows (h : System Q V K I)
    (hK : ∀ s ∈ I, (K s).transpose = K s) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : V a = 0) (hdet : (Q t).det ≠ 0) :
    inertiaRate Q V t = 2 * ∑ i : Fin 2,
      matrixQuadratic (riccati Q V t) (fun j => Q t i j) := by
  exact congrArg (fun x : ℝ => 2 * x)
    (matrixFrobeniusPairing_eq_rowQuadraticSum _ _ _
      (velocity_eq_mul_riccati hdet)
      (h.riccati_symmetric hK hconn ha ht hrest hdet))

theorem System.spatialRate_neg (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0)
    (ht : t ∈ initialBranch Q I a) (hat : a < t)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    matrixQuadratic (spatialRate Q V t) w < 0 := by
  have hdet := ht.2.2 t ⟨hat.le, le_rfl⟩
  have hsym := h.riccati_symmetric (fun s hs => (hK s hs).1) hconn ha
    (ht.2.1 ⟨hat.le, le_rfl⟩) hrest hdet
  have hunit : IsUnit (Q t).transpose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa using (isUnit_iff_ne_zero.mpr hdet)
  have hw' : (Q t).transpose.mulVec w ≠ 0 := by
    intro hz
    apply hw
    apply Matrix.mulVec_injective_of_isUnit hunit
    simpa using hz
  have hn := h.riccati_quadratic_neg_of_rest hK hconn ha hrest ht hat
    ((Q t).transpose.mulVec w) hw'
  have heq : matrixQuadratic (spatialRate Q V t) w =
      2 * matrixQuadratic (riccati Q V t) ((Q t).transpose.mulVec w) := by
    rw [show spatialRate Q V t =
      (Q t * riccati Q V t) * (Q t).transpose +
        Q t * (Q t * riccati Q V t).transpose by
          unfold spatialRate; rw [velocity_eq_mul_riccati (V := V) hdet]]
    have hs : riccati Q V t 1 0 = riccati Q V t 0 1 :=
      congrFun (congrFun hsym 0) 1
    simp [matrixQuadratic, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, hs]
    ring
  rw [heq]
  linarith

theorem System.inertia_deriv_neg (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0)
    (ht : t ∈ initialBranch Q I a) (hat : a < t) :
    deriv (inertia Q) t < 0 := by
  have htI := ht.2.1 ⟨hat.le, le_rfl⟩
  have hdet := ht.2.2 t ⟨hat.le, le_rfl⟩
  rw [(h.inertia_hasDerivAt htI).deriv,
    h.inertiaRate_eq_rows (fun s hs => (hK s hs).1) hconn ha htI hrest hdet]
  have hQ : Q t ≠ 0 := by
    intro hz
    rw [hz, Matrix.det_fin_two] at hdet
    norm_num at hdet
  have hn := matrixQuadratic_rowSum_lt_zero_of_negDef _ _
    (h.riccati_quadratic_neg_of_rest hK hconn ha hrest ht hat) hQ
  linarith

theorem System.inertia_strictAntiOn_initialBranch (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) :
    StrictAntiOn (inertia Q) (initialBranch Q I a) := by
  intro s hs t ht hst
  have hanti : StrictAntiOn (inertia Q) (Set.Icc a t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a t)
    · intro u hu
      exact (h.inertia_hasDerivAt (ht.2.1 hu)).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : a < u ∧ u < t := by simpa using hu
      exact h.inertia_deriv_neg hK hconn ha hrest
        ⟨hu'.1.le, fun x hx => ht.2.1 ⟨hx.1, hx.2.trans hu'.2.le⟩,
          fun x hx => ht.2.2 x ⟨hx.1, hx.2.trans hu'.2.le⟩⟩ hu'.1
  exact hanti ⟨hs.1, hst.le⟩ ⟨ht.1, le_rfl⟩ hst

/-- The endpoint may be singular as a matrix. Only its nonzero size and
regularity as a matrix curve are used; no inverse is evaluated there. -/
theorem System.inertia_deriv_neg_at_endpoint (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) {T : ℝ} (haT : a < T)
    (hI : Set.Icc a T ⊆ I) (hdet : ∀ u ∈ Set.Ico a T, (Q u).det ≠ 0)
    (hQT : Q T ≠ 0) : deriv (inertia Q) T < 0 := by
  let s := (a + T) / 2
  have has : a < s := by dsimp [s]; linarith
  have hsT : s < T := by dsimp [s]; linarith
  have hsbranch : s ∈ initialBranch Q I a :=
    ⟨has.le, fun u hu => hI ⟨hu.1, hu.2.trans hsT.le⟩,
      fun u hu => hdet u ⟨hu.1, hu.2.trans_lt hsT⟩⟩
  let bound : ℝ → ℝ := fun u =>
    2 * ∑ i : Fin 2, matrixQuadratic (riccati Q V s) (fun j => Q u i j)
  have hbT : bound T < 0 := by
    have hn := matrixQuadratic_rowSum_lt_zero_of_negDef _ _
      (h.riccati_quadratic_neg_of_rest hK hconn ha hrest hsbranch has) hQT
    dsimp [bound]
    linarith
  have hQcont : ContinuousOn Q (Set.Icc s T) := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j u hu
    have hp := hasDerivAt_pi.1 (hasDerivAt_pi.1
      (h.position u (hI ⟨has.le.trans hu.1, hu.2⟩)) i) j
    exact hp.continuousAt.continuousWithinAt
  have hVcont : ContinuousOn V (Set.Icc s T) := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j u hu
    have hp := hasDerivAt_pi.1 (hasDerivAt_pi.1
      (h.velocity u (hI ⟨has.le.trans hu.1, hu.2⟩)) i) j
    exact hp.continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun u => inertiaRate Q V u - bound u) (Set.Icc s T) := by
    dsimp [inertiaRate, bound, matrixQuadratic]
    simp only [Fin.sum_univ_succ]
    fun_prop
  have hle : ∀ u ∈ Set.Ico s T, inertiaRate Q V u - bound u ≤ 0 := by
    intro u hu
    have hau := has.le.trans hu.1
    rw [h.inertiaRate_eq_rows (fun x hx => (hK x hx).1) hconn ha
      (hI ⟨hau, hu.2.le⟩) hrest (hdet u ⟨hau, hu.2⟩)]
    have hrows : ∀ i : Fin 2,
        matrixQuadratic (riccati Q V u) (fun j => Q u i j) ≤
          matrixQuadratic (riccati Q V s) (fun j => Q u i j) := by
      intro i
      by_cases hz : (fun j => Q u i j) = 0
      · simp [hz, matrixQuadratic]
      · exact (h.riccati_quadratic_strictAntiOn hK hconn ha hrest
          (fun x hx => hI ⟨has.le.trans hx.1, hx.2.trans hu.2.le⟩)
          (fun x hx => hdet x ⟨has.le.trans hx.1, hx.2.trans_lt hu.2⟩)
          (fun j => Q u i j) hz).antitoneOn
          ⟨le_rfl, hu.1⟩ ⟨hu.1, le_rfl⟩ hu.1
    have hn := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2)))
      (fun i _ => hrows i)
    dsimp [bound]
    linarith
  have hend := continuousOn_nonpos_right_of_nonpos_Ico hsT hcont hle
  rw [(h.inertia_hasDerivAt (hI ⟨haT.le, le_rfl⟩)).deriv]
  linarith

end
end DroppingThreeBodies.AbstractJacobi
