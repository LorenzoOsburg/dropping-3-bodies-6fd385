module

public import Dropping3Bodies.EqualMass.PowerLawModel
public import Dropping3Bodies.Dynamics.FirstSyzygyCertificate
public import Dropping3Bodies.Dynamics.PhaseLipschitz
public import NBody.ODE.Continuation

@[expose] public section

namespace DroppingThreeBodies.CentralForce

open Set Filter
open scoped Topology
noncomputable section

/-- Below the supremum, the entire closed segment lies on the initial branch. -/
theorem mem_initialBranch_of_lt_lub {z : ℝ → Phase} {I : Set ℝ} {a t T : ℝ}
    (hT : IsLUB (BeforeFirstCollinearity z I a) T) (hat : a ≤ t) (ht : t < T) :
    t ∈ BeforeFirstCollinearity z I a := by
  obtain ⟨u, hu, htu⟩ := hT.exists_between ht
  exact ⟨hat, fun s hs => hu.2.1 ⟨hs.1, hs.2.trans htu.1.le⟩,
    fun s hs => hu.2.2 s ⟨hs.1, hs.2.trans htu.1.le⟩⟩

private theorem signedArea_continuous : Continuous (fun w : Phase => signedDoubleArea w.1) := by
  unfold signedDoubleArea cross
  fun_prop

/-- Both orientations give a positive product with the starting area throughout
the initial noncollinear interval. -/
theorem initialBranch_area_product_pos {κ : Coefficients} {m : Fin 3 → ℝ}
    {z : ℝ → Phase} {I : Set ℝ} {a t : ℝ}
    (hsol : Solution κ m z I) (hbranch : t ∈ BeforeFirstCollinearity z I a) :
    0 < signedDoubleArea (z a).1 * signedDoubleArea (z t).1 := by
  let f := fun u => signedDoubleArea (z a).1 * signedDoubleArea (z u).1
  have hc : ContinuousOn f (Icc a t) := by
    intro u hu
    exact (continuousAt_const.mul (signedArea_continuous.continuousAt.comp
      (hsol.2 u (hbranch.2.1 hu)).2.continuousAt)).continuousWithinAt
  have hAa := hbranch.2.2 a ⟨le_rfl, hbranch.1⟩
  by_contra h
  obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc' hbranch.1 hc
    (show (0 : ℝ) ∈ Icc (f t) (f a) from ⟨le_of_not_gt h, mul_self_nonneg _⟩)
  exact (mul_ne_zero hAa (hbranch.2.2 s hs)) hzero

/-- A uniform separation and field bound on a final subinterval permit
continuation of the maximal trajectory through the finite branch endpoint. -/
theorem firstRegularSyzygy_of_tail_bounds
    {κ : Coefficients} {m : Fin 3 → ℝ} {z₀ : Phase} {b T δ C : ℝ}
    (hreg : κ.C1) (hcf : CollisionFree z₀.1)
    (hpos : 0 < T) (hbT : b < T) (hb : 0 ≤ b)
    (hT : IsLUB (BeforeFirstCollinearity (maximalTrajectory κ m z₀)
      (maximalDomain κ m z₀) 0) T)
    (hδ : 0 < δ)
    (hsep : ∀ t ∈ Ico b T, ∀ i j : Fin 3, i ≠ j →
      δ ≤ dist ((maximalTrajectory κ m z₀ t).1 i) ((maximalTrajectory κ m z₀ t).1 j))
    (hbound : ∀ t ∈ Ico b T, ‖vectorField κ m (maximalTrajectory κ m z₀ t)‖ ≤ C) :
    FirstRegularSyzygy (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0 T := by
  let I := maximalDomain κ m z₀
  let z := maximalTrajectory κ m z₀
  have hsol : Solution κ m z I := maximalTrajectory_solution κ hreg m z₀
  have hzero : (0 : ℝ) ∈ I := maximalDomain_initial_mem κ hreg m hcf
  have hinit : z 0 = z₀ := maximalTrajectory_initial κ hreg m hcf
  have hpre (t : ℝ) (ht : t ∈ Ico 0 T) :
      t ∈ I ∧ signedDoubleArea (z t).1 ≠ 0 := by
    have ht' := mem_initialBranch_of_lt_lub hT ht.1 ht.2
    exact ⟨ht'.2.1 ⟨ht.1, le_rfl⟩, ht'.2.2 t ⟨ht.1, le_rfl⟩⟩
  have htail : Ico b T ⊆ I := fun t ht => (hpre t ⟨hb.trans ht.1, ht.2⟩).1
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound b ⟨le_rfl, hbT⟩)
  have hLip : LipschitzOnWith ⟨C, hC⟩ z (Ico b T) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun t ht => (hsol.2 t (htail ht)).2.differentiableAt)
      (fun t ht => by rw [(hsol.2 t (htail ht)).2.deriv]; exact hbound t ht)
      (convex_Ico b T)
  obtain ⟨zT, hlim⟩ := exists_left_limit_of_lipschitzOnWith_finiteDimensional hbT hLip
  have hsepT := left_limit_preserves_pairwise_distance_lower_bound hbT hlim hsep
  have hregT : CollisionFree zT.1 := fun i j hne =>
    dist_pos.mp (hδ.trans_le (hsepT i j hne))
  obtain ⟨l, r, hlr, hlocal⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hsol.1.mem_nhds hzero)
  have hleft : Ioo l T ⊆ I := by
    intro t ht
    by_cases hneg : t < 0
    · exact hlocal ⟨ht.1, hneg.trans hlr.2⟩
    · exact (hpre t ⟨le_of_not_gt hneg, ht.2⟩).1
  obtain ⟨ε, hε, w, _, hw, hagree⟩ := NBody.exists_local_extension_of_right_limit
    (NBody.isOpen_regularPhaseSet (ι := Fin 3) 2) (hlr.1.trans hpos)
    (hsol.restrict isOpen_Ioo hleft) hlim hregT (vectorField_contDiffAt κ hreg m zT hregT)
  have hw0 : w 0 = z₀ := (hagree 0 ⟨hlr.1, hpos⟩).trans hinit
  have hdom := maximalDomain_contains_initialInterval hlr.1 (add_pos hpos hε) hw0 hw
  have hTI : T ∈ I := hdom ⟨hlr.1.trans hpos, lt_add_of_pos_right T hε⟩
  refine ⟨hpos, (maximalDomain_isPreconnected κ m z₀).Icc_subset hzero hTI,
    ?_, fun t ht => (hpre t ht).2, (hsol.2 T hTI).1⟩
  by_contra hne
  have hcont : ContinuousAt (fun t => signedDoubleArea (z t).1) T :=
    signedArea_continuous.continuousAt.comp (hsol.2 T hTI).2.continuousAt
  have hnb : {s | s ∈ I ∧ signedDoubleArea (z s).1 ≠ 0} ∈ 𝓝 T :=
    inter_mem (hsol.1.mem_nhds hTI) (hcont.eventually_ne hne)
  obtain ⟨u, v, huv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnb
  obtain ⟨T', hTT', hT'v⟩ := exists_between huv.2
  have hnew (s : ℝ) (hs : s ∈ Icc 0 T') : s ∈ I ∧ signedDoubleArea (z s).1 ≠ 0 := by
    by_cases hlt : s < T
    · exact hpre s ⟨hs.1, hlt⟩
    · exact hsub ⟨huv.1.trans_le (le_of_not_gt hlt), hs.2.trans_lt hT'v⟩
  exact hTT'.not_ge (hT.1 (show T' ∈ BeforeFirstCollinearity z I 0 from
    ⟨(hpos.trans hTT').le, fun s hs => (hnew s hs).1, fun s hs => (hnew s hs).2⟩))

end
end DroppingThreeBodies.CentralForce
