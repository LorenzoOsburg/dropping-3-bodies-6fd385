module

public import Dropping3Bodies.Inertia.AbstractJacobi
public import Dropping3Bodies.Inertia.AreaConcavity
public import Mathlib.Analysis.Calculus.Deriv.Abs

@[expose] public section

/-! Determinant contraction, square-root area concavity, and boundedness for
abstract planar Jacobi dynamics. Both determinant orientations are treated
directly through the absolute determinant; no force-law symmetry adapter is used. -/

namespace DroppingThreeBodies.AbstractJacobi

noncomputable section

open Filter
open scoped Topology

variable {Q V K : ℝ → Mat} {I : Set ℝ} {a s t : ℝ}

/-- A fixed orientation selected from the initial matrix. -/
def orientedDet (Q : ℝ → Mat) (a t : ℝ) : ℝ :=
  if (Q a).det < 0 then -(Q t).det else (Q t).det

theorem initialBranch_mono (ht : t ∈ initialBranch Q I a)
    (has : a ≤ s) (hst : s ≤ t) : s ∈ initialBranch Q I a :=
  ⟨has, fun _ hu => ht.2.1 ⟨hu.1, hu.2.trans hst⟩,
    fun u hu => ht.2.2 u ⟨hu.1, hu.2.trans hst⟩⟩

theorem initialBranch_convex (Q : ℝ → Mat) (I : Set ℝ) (a : ℝ) :
    Convex ℝ (initialBranch Q I a) := by
  apply convex_iff_ordConnected.mpr
  rw [Set.ordConnected_iff]
  intro x hx y hy _hxy z hz
  exact initialBranch_mono hy (hx.1.trans hz.1) hz.2

theorem System.det_hasDerivAt (h : System Q V K I)
    (ht : t ∈ I) (hdet : (Q t).det ≠ 0) :
    HasDerivAt (fun u => (Q u).det)
      ((Q t).det * Matrix.trace (riccati Q V t)) t :=
  hasDerivAt_matrixDet_finTwo_mul_trace
    (fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 (h.position t ht) i) j) hdet

/-- The absolute determinant has the same logarithmic derivative as the
signed determinant, for either orientation. -/
theorem System.absDet_hasDerivAt (h : System Q V K I)
    (ht : t ∈ I) (hdet : (Q t).det ≠ 0) :
    HasDerivAt (fun u => |(Q u).det|)
      (|(Q t).det| * Matrix.trace (riccati Q V t)) t := by
  have hd := h.det_hasDerivAt ht hdet
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · have heq : (fun u => |(Q u).det|) =ᶠ[nhds t] (fun u => -(Q u).det) := by
      filter_upwards [hd.continuousAt.eventually (Iio_mem_nhds hneg)] with u hu
      exact abs_of_neg hu
    simpa only [abs_of_neg hneg, neg_mul] using hd.neg.congr_of_eventuallyEq heq
  · have heq : (fun u => |(Q u).det|) =ᶠ[nhds t] (fun u => (Q u).det) := by
      filter_upwards [hd.continuousAt.eventually (Ioi_mem_nhds hpos)] with u hu
      exact abs_of_pos hu
    simpa only [abs_of_pos hpos] using hd.congr_of_eventuallyEq heq

theorem System.orientedDet_eq_abs (h : System Q V K I)
    (ht : t ∈ initialBranch Q I a) :
    orientedDet Q a t = |(Q t).det| := by
  have hda : (Q a).det ≠ 0 := ht.2.2 a ⟨le_rfl, ht.1⟩
  have hdt : (Q t).det ≠ 0 := ht.2.2 t ⟨ht.1, le_rfl⟩
  have hcont : ContinuousOn (fun u => (Q a).det * (Q u).det) (Set.Icc a t) := by
    intro u hu
    exact ((h.det_hasDerivAt (ht.2.1 hu) (ht.2.2 u hu)).const_mul
      (Q a).det).continuousAt.continuousWithinAt
  have hprod : 0 < (Q a).det * (Q t).det := by
    rcases lt_or_gt_of_ne (mul_ne_zero hda hdt) with hneg | hpos
    · obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc' ht.1 hcont
        (show (0 : ℝ) ∈ Set.Icc ((Q a).det * (Q t).det)
          ((Q a).det * (Q a).det) from ⟨hneg.le, mul_self_nonneg _⟩)
      exact False.elim ((mul_ne_zero hda (ht.2.2 u hu)) hzero)
    · exact hpos
  rcases mul_pos_iff.mp hprod with hpos | hneg
  · simp [orientedDet, not_lt_of_ge hpos.1.le, abs_of_pos hpos.2]
  · simp [orientedDet, hneg.1, abs_of_neg hneg.2]

theorem positiveForce_trace_pos (hK : PositiveForce K I) (ht : t ∈ I) :
    0 < Matrix.trace (K t) := by
  have h0 := (hK t ht).2 ![1, 0]
    (by intro hz; have := congrFun hz 0; norm_num at this)
  have h1 := (hK t ht).2 ![0, 1]
    (by intro hz; have := congrFun hz 1; norm_num at this)
  simp [matrixQuadratic, Fin.sum_univ_succ] at h0 h1
  simpa [Matrix.trace, Fin.sum_univ_succ] using add_pos h0 h1

theorem System.riccati_trace_neg_of_rest (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0)
    (ht : t ∈ initialBranch Q I a) (hat : a < t) :
    Matrix.trace (riccati Q V t) < 0 := by
  have hneg := h.riccati_quadratic_neg_of_rest hK hconn ha hrest ht hat
  have h0 := hneg ![1, 0]
    (by intro hz; have := congrFun hz 0; norm_num at this)
  have h1 := hneg ![0, 1]
    (by intro hz; have := congrFun hz 1; norm_num at this)
  simp [matrixQuadratic, Fin.sum_univ_succ] at h0 h1
  simpa [Matrix.trace, Fin.sum_univ_succ] using add_neg h0 h1

theorem System.absDet_deriv_neg (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0)
    (ht : t ∈ initialBranch Q I a) (hat : a < t) :
    deriv (fun u => |(Q u).det|) t < 0 := by
  have hdet := ht.2.2 t ⟨ht.1, le_rfl⟩
  rw [(h.absDet_hasDerivAt (ht.2.1 ⟨ht.1, le_rfl⟩) hdet).deriv]
  exact mul_neg_of_pos_of_neg (abs_pos.mpr hdet)
    (h.riccati_trace_neg_of_rest hK hconn ha hrest ht hat)

theorem System.absDet_strictAntiOn_initialBranch (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) :
    StrictAntiOn (fun u => |(Q u).det|) (initialBranch Q I a) := by
  intro s hs t ht hst
  have hanti : StrictAntiOn (fun u => |(Q u).det|) (Set.Icc s t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s t)
    · intro u hu
      have hub := initialBranch_mono ht (hs.1.trans hu.1) hu.2
      exact (h.absDet_hasDerivAt (ht.2.1 ⟨hs.1.trans hu.1, hu.2⟩)
        (hub.2.2 u ⟨hub.1, le_rfl⟩)).continuousAt.continuousWithinAt
    · intro u hu
      have hui : u ∈ Set.Ioo s t := by simpa only [interior_Icc] using hu
      exact h.absDet_deriv_neg hK hconn ha hrest
        (initialBranch_mono ht (hs.1.trans hui.1.le) hui.2.le)
        (hs.1.trans_lt hui.1)
  exact hanti ⟨le_rfl, hst.le⟩ ⟨hst.le, le_rfl⟩ hst

theorem System.orientedDet_strictAntiOn_initialBranch (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) :
    StrictAntiOn (orientedDet Q a) (initialBranch Q I a) := by
  intro s hs t ht hst
  rw [h.orientedDet_eq_abs ht, h.orientedDet_eq_abs hs]
  exact h.absDet_strictAntiOn_initialBranch hK hconn ha hrest hs ht hst

theorem System.sqrtAbsDet_hasDerivAt (h : System Q V K I)
    (ht : t ∈ I) (hdet : (Q t).det ≠ 0) :
    HasDerivAt (fun u => Real.sqrt |(Q u).det|)
      (Real.sqrt |(Q t).det| * Matrix.trace (riccati Q V t) / 2) t := by
  have hp := abs_pos.mpr hdet
  have hd := (h.absDet_hasDerivAt ht hdet).sqrt hp.ne'
  apply hd.congr_deriv
  have hn := (Real.sqrt_pos.2 hp).ne'
  field_simp
  linear_combination -Matrix.trace (riccati Q V t) * Real.sq_sqrt hp.le

/-- Exact second-order square-root area identity. No derivative of K occurs. -/
theorem System.sqrtAbsDetRate_hasDerivAt (h : System Q V K I)
    (hK : ∀ u ∈ I, (K u).transpose = K u) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : V a = 0)
    (hdet : (Q t).det ≠ 0) :
    HasDerivAt
      (fun u => Real.sqrt |(Q u).det| * Matrix.trace (riccati Q V u) / 2)
      (-Real.sqrt |(Q t).det| *
        (Matrix.trace (K t) / 2 +
          (riccati Q V t 0 0 - riccati Q V t 1 1) ^ 2 / 4 +
          (riccati Q V t 0 1) ^ 2)) t := by
  let C := riccati Q V t
  have hC := h.riccati_deriv ht hdet
  have htr : HasDerivAt (fun u => Matrix.trace (riccati Q V u))
      (Matrix.trace (-(C * C + K t))) t := by
    simpa [Matrix.trace, Fin.sum_univ_succ, C] using! (hC 0 0).add (hC 1 1)
  have hd := ((h.sqrtAbsDet_hasDerivAt ht hdet).mul htr).div_const 2
  apply hd.congr_deriv
  have hid := matrix_trace_riccati_sqrt_identity C (K t)
    (h.riccati_symmetric hK hconn ha ht hrest hdet)
  change _ = -Real.sqrt |(Q t).det| *
    (Matrix.trace (K t) / 2 + (C 0 0 - C 1 1) ^ 2 / 4 + (C 0 1) ^ 2)
  change (Real.sqrt |(Q t).det| * Matrix.trace C / 2 *
    Matrix.trace C + Real.sqrt |(Q t).det| *
      Matrix.trace (-(C * C + K t))) / 2 = _
  linear_combination Real.sqrt |(Q t).det| * hid

theorem System.sqrtAbsDet_second_deriv_neg (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : V a = 0)
    (hdet : (Q t).det ≠ 0) :
    deriv (deriv (fun u => Real.sqrt |(Q u).det|)) t < 0 := by
  have hnear := (h.det_hasDerivAt ht hdet).continuousAt.eventually_ne hdet
  have heq : deriv (fun u => Real.sqrt |(Q u).det|) =ᶠ[nhds t]
      (fun u => Real.sqrt |(Q u).det| * Matrix.trace (riccati Q V u) / 2) := by
    filter_upwards [h.isOpen.mem_nhds ht, hnear] with u hu hdu
    exact (h.sqrtAbsDet_hasDerivAt hu hdu).deriv
  rw [heq.deriv_eq]
  rw [(h.sqrtAbsDetRate_hasDerivAt (fun u hu => (hK u hu).1)
    hconn ha ht hrest hdet).deriv]
  have htrace := positiveForce_trace_pos hK ht
  have hp : 0 < Matrix.trace (K t) / 2 +
      (riccati Q V t 0 0 - riccati Q V t 1 1) ^ 2 / 4 +
      (riccati Q V t 0 1) ^ 2 := by positivity
  exact mul_neg_of_neg_of_pos
    (neg_neg_of_pos (Real.sqrt_pos.2 (abs_pos.mpr hdet))) hp

theorem System.sqrtAbsDet_strictConcaveOn_Icc (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0)
    (hIcc : Set.Icc s t ⊆ I)
    (hdet : ∀ u ∈ Set.Icc s t, (Q u).det ≠ 0) :
    StrictConcaveOn ℝ (Set.Icc s t) (fun u => Real.sqrt |(Q u).det|) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc s t)
  · intro u hu
    exact (h.sqrtAbsDet_hasDerivAt (hIcc hu) (hdet u hu)).continuousAt.continuousWithinAt
  · intro u hu
    exact h.sqrtAbsDet_second_deriv_neg hK hconn ha
      (hIcc (interior_subset hu)) hrest (hdet u (interior_subset hu))

theorem System.sqrtAbsDet_strictConcaveOn_initialBranch (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) :
    StrictConcaveOn ℝ (initialBranch Q I a) (fun u => Real.sqrt |(Q u).det|) := by
  apply strictConcaveOn_of_deriv2_neg (initialBranch_convex Q I a)
  · intro u hu
    exact (h.sqrtAbsDet_hasDerivAt (hu.2.1 ⟨hu.1, le_rfl⟩)
      (hu.2.2 u ⟨hu.1, le_rfl⟩)).continuousAt.continuousWithinAt
  · intro u hu
    have hub := interior_subset hu
    exact h.sqrtAbsDet_second_deriv_neg hK hconn ha
      (hub.2.1 ⟨hub.1, le_rfl⟩) hrest (hub.2.2 u ⟨hub.1, le_rfl⟩)

theorem System.sqrtAbsDet_tangent_bound (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) (hst : s ≤ t)
    (hIcc : Set.Icc s t ⊆ I)
    (hdet : ∀ u ∈ Set.Icc s t, (Q u).det ≠ 0) :
    Real.sqrt |(Q t).det| ≤ Real.sqrt |(Q s).det| +
      (t - s) * (Real.sqrt |(Q s).det| *
        Matrix.trace (riccati Q V s) / 2) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hconc := (h.sqrtAbsDet_strictConcaveOn_Icc hK hconn ha hrest hIcc hdet).concaveOn
  have hs : s ∈ Set.Icc s t := ⟨le_rfl, hst.le⟩
  have ht : t ∈ Set.Icc s t := ⟨hst.le, le_rfl⟩
  have hd := hconc.slope_le_of_hasDerivAt hs ht hst
    (h.sqrtAbsDet_hasDerivAt (hIcc hs) (hdet s hs))
  rw [slope_def_field] at hd
  have := (div_le_iff₀ (sub_pos.mpr hst)).mp hd
  nlinarith

theorem System.initialBranch_remainingTime_bound (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0)
    (hs : s ∈ initialBranch Q I a) (has : a < s)
    (ht : t ∈ initialBranch Q I a) (hst : s ≤ t) :
    t < s + 2 / (-Matrix.trace (riccati Q V s)) := by
  have htr := h.riccati_trace_neg_of_rest hK hconn ha hrest hs has
  have hIcc : Set.Icc s t ⊆ I :=
    fun u hu => ht.2.1 ⟨has.le.trans hu.1, hu.2⟩
  have hdet : ∀ u ∈ Set.Icc s t, (Q u).det ≠ 0 :=
    fun u hu => ht.2.2 u ⟨has.le.trans hu.1, hu.2⟩
  have htan := h.sqrtAbsDet_tangent_bound hK hconn ha hrest hst hIcc hdet
  have hρs := Real.sqrt_pos.2 (abs_pos.mpr (hs.2.2 s ⟨has.le, le_rfl⟩))
  have hρt := Real.sqrt_pos.2 (abs_pos.mpr (ht.2.2 t ⟨ht.1, le_rfl⟩))
  have hremaining : 0 < Real.sqrt |(Q s).det| *
      (2 - (t - s) * (-Matrix.trace (riccati Q V s))) := by
    nlinarith only [htan, hρt]
  have hprod : (t - s) * (-Matrix.trace (riccati Q V s)) < 2 := by
    have := (mul_pos_iff_of_pos_left hρs).mp hremaining
    linarith
  have := (lt_div_iff₀ (neg_pos.mpr htr)).mpr hprod
  linarith

/-- Boundedness requires neither an endpoint nor a finite lifetime hypothesis. -/
theorem System.initialBranch_bddAbove (h : System Q V K I)
    (hK : PositiveForce K I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : V a = 0) :
    BddAbove (initialBranch Q I a) := by
  by_cases hex : ∃ s ∈ initialBranch Q I a, a < s
  · obtain ⟨s, hs, has⟩ := hex
    let T := s + 2 / (-Matrix.trace (riccati Q V s))
    have htr := h.riccati_trace_neg_of_rest hK hconn ha hrest hs has
    have hsT : s < T := lt_add_of_pos_right s (div_pos (by norm_num) (neg_pos.mpr htr))
    refine ⟨T, fun t ht => ?_⟩
    by_cases hst : s ≤ t
    · exact (h.initialBranch_remainingTime_bound hK hconn ha hrest hs has ht hst).le
    · exact (lt_trans (lt_of_not_ge hst) hsT).le
  · refine ⟨a, fun t ht => ?_⟩
    by_contra hn
    exact hex ⟨t, ht, lt_of_not_ge hn⟩

/-- Continuity and an invertible initial matrix provide a genuinely later branch time. -/
theorem System.exists_lt_mem_initialBranch (h : System Q V K I)
    (ha : a ∈ I) (hdet : (Q a).det ≠ 0) :
    ∃ t > a, t ∈ initialBranch Q I a := by
  have hcont := (h.det_hasDerivAt ha hdet).continuousAt
  have hnhds : {s | s ∈ I ∧ (Q s).det ≠ 0} ∈ nhds a :=
    Filter.inter_mem (h.isOpen.mem_nhds ha) (hcont.eventually_ne hdet)
  obtain ⟨l, r, haLR, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  refine ⟨(a + r) / 2, by linarith [haLR.2], ?_⟩
  have hseg : ∀ s ∈ Set.Icc a ((a + r) / 2), s ∈ I ∧ (Q s).det ≠ 0 := by
    intro s hs
    exact hsub ⟨by linarith [haLR.1, hs.1], by linarith [haLR.2, hs.2]⟩
  exact ⟨by linarith [haLR.2], fun s hs => (hseg s hs).1,
    fun s hs => (hseg s hs).2⟩

end
end DroppingThreeBodies.AbstractJacobi

