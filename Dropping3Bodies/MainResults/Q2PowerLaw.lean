module

public import Dropping3Bodies.EqualMass.PowerLawCollision
public import Dropping3Bodies.EqualMass.PowerLawCritical
public import Dropping3Bodies.EqualMass.PowerLawEndpoint

@[expose] public section

/-! Montgomery's second question for equal masses and a common inverse-power coupling. -/

namespace DroppingThreeBodies.CentralForce

open Set
noncomputable section

/-- Strict ordering for every attractive power on the initial noncollinear branch. -/
theorem power_side_order_on_initialBranch
    {α g m a t : ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hs : EqualPowerSolution α g m z I) (hα : 0 < α) (hg : 0 < g) (hm : 0 < m)
    (hc : IsPreconnected I) (ht : t ∈ BeforeFirstCollinearity z I a)
    (hrest : ∀ j, (z a).2 j = 0) (horder : orderedOppositeSides (z a).1) :
    orderedOppositeSides (z t).1 := by
  have hstart := ht.2.1 (show a ∈ Icc a t from ⟨le_rfl, ht.1⟩)
  have hfinish := ht.2.1 (show t ∈ Icc a t from ⟨ht.1, le_rfl⟩)
  have hsq := (orderedOppositeSides_iff _ (hs.2 a hstart).1).mp horder
  apply (orderedOppositeSides_iff _ (hs.2 t hfinish).1).mpr
  apply power_order_on_segment hs hα hg hm hc ht.1 ht.2.1 hrest _ hsq.1 hsq.2
  intro u hu
  exact initialBranch_area_product_pos hs
    ⟨hu.1, fun s h => ht.2.1 ⟨h.1, h.2.trans hu.2⟩,
      fun s h => ht.2.2 s ⟨h.1, h.2.trans hu.2⟩⟩

/-- The finite initial noncollinear endpoint is regular for the full range
`0 < α ≤ 2`. The singular endpoint is ruled out by uniform separation. -/
theorem power_firstRegularSyzygy
    (α g m : ℝ) (hα : 0 < α) (hα2 : α ≤ 2) (hg : 0 < g) (hm : 0 < m)
    (q : Fin 3 → Point) (harea : signedDoubleArea q ≠ 0)
    (horder : orderedOppositeSides q) :
    let κ := powerCoefficients α (commonCouplings g)
    let masses : Fin 3 → ℝ := fun _ => m
    let z₀ : Phase := (q, fun _ => 0)
    FirstRegularSyzygy (maximalTrajectory κ masses z₀) (maximalDomain κ masses z₀)
      0 (initialNoncollinearEndpoint κ masses z₀) := by
  dsimp only
  let κ := powerCoefficients α (commonCouplings g)
  let masses : Fin 3 → ℝ := fun _ => m
  let z₀ : Phase := (q, fun _ => 0)
  let z := maximalTrajectory κ masses z₀
  let I := maximalDomain κ masses z₀
  let T := initialNoncollinearEndpoint κ masses z₀
  have hcf := collisionFree_of_signedDoubleArea_ne_zero harea
  have hreg : κ.C1 := powerCoefficients_C1 α (commonCouplings g)
  have hinit : z 0 = z₀ := maximalTrajectory_initial κ hreg masses hcf
  have hzero : (0 : ℝ) ∈ I := maximalDomain_initial_mem κ hreg masses hcf
  have hs : EqualPowerSolution α g m z I := maximalTrajectory_solution κ hreg masses z₀
  have hc : IsPreconnected I := maximalDomain_isPreconnected κ masses z₀
  have hrest : ∀ j, (z 0).2 j = 0 := by simp [hinit, z₀]
  have hsq := (orderedOppositeSides_iff _ (hs.2 0 hzero).1).mp
    (show orderedOppositeSides (z 0).1 by simpa [hinit, z₀] using horder)
  obtain ⟨_, _, hT, hpos, _⟩ := power_maximal_initialBranch_endpoint_pos_finite
    (g := commonCouplings g) (m := masses) (z₀ := z₀) hα
    (fun i j hij => by simpa [hij] using hg) (fun _ => hm) harea (fun _ => rfl)
  have hT' : IsLUB (BeforeFirstCollinearity z I 0) T := hT
  obtain ⟨b, hb, hbT⟩ := exists_between (show 0 < T from hpos)
  have hbranch (t) (ht : t ∈ Ico 0 T) := mem_initialBranch_of_lt_lub hT' ht.1 ht.2
  have hseg : Ico 0 T ⊆ I := fun t ht => (hbranch t ht).2.1 ⟨ht.1, le_rfl⟩
  have hA (t) (ht : t ∈ Ico 0 T) : 0 < signedDoubleArea (z 0).1 * signedDoubleArea (z t).1 :=
    initialBranch_area_product_pos hs (hbranch t ht)
  have hsep : ∃ δ > 0, ∀ t ∈ Ico b T, ∀ i j : Fin 3, i ≠ j →
      δ ≤ dist ((z t).1 i) ((z t).1 j) := by
    rcases lt_or_eq_of_le hα2 with hlt | heq
    · exact power_subcritical_separation hs hα hlt hg hm hc hb hbT hseg hrest hA hsq.1 hsq.2
    · exact power_critical_shortest_distance_uniform (heq ▸ hs) hg hm hc hb hbT hseg hrest hA hsq.1 hsq.2
  obtain ⟨δ, hδ, hδsep⟩ := hsep
  exact firstRegularSyzygy_of_tail_bounds hreg hcf hpos hbT hb.le hT' hδ hδsep
    (fun t ht => power_field_bound hs hα hg hm hc hzero (hseg ⟨hb.le.trans ht.1, ht.2⟩)
      hrest hδ (hδsep t ht))

/-- For the physical potential with common coupling `g` and common mass `m`,
the maximal classical trajectory has a first regular syzygy, preserves the
strict side ordering through it, and has body 0 between bodies 2 and 1 there. -/
theorem power_q2
    (α g m : ℝ) (hα : 0 < α) (hα2 : α ≤ 2) (hg : 0 < g) (hm : 0 < m)
    (q : Fin 3 → Point) (harea : signedDoubleArea q ≠ 0)
    (horder : orderedOppositeSides q) :
    let κ := powerCoefficients α (commonCouplings g)
    let masses : Fin 3 → ℝ := fun _ => m
    let z₀ : Phase := (q, fun _ => 0)
    let z := maximalTrajectory κ masses z₀
    let I := maximalDomain κ masses z₀
    let T := initialNoncollinearEndpoint κ masses z₀
    EqualPowerSolution α g m z I ∧ z 0 = z₀ ∧
      FirstRegularSyzygy z I 0 T ∧
      (∀ t ∈ Icc 0 T, CollisionFree (z t).1 ∧ orderedOppositeSides (z t).1) ∧
      Sbtw ℝ ((z T).1 2) ((z T).1 0) ((z T).1 1) := by
  dsimp only
  let κ := powerCoefficients α (commonCouplings g)
  let masses : Fin 3 → ℝ := fun _ => m
  let z₀ : Phase := (q, fun _ => 0)
  let z := maximalTrajectory κ masses z₀
  let I := maximalDomain κ masses z₀
  let T := initialNoncollinearEndpoint κ masses z₀
  have hcf := collisionFree_of_signedDoubleArea_ne_zero harea
  have hreg : κ.C1 := powerCoefficients_C1 α (commonCouplings g)
  have hinit : z 0 = z₀ := maximalTrajectory_initial κ hreg masses hcf
  have hs : EqualPowerSolution α g m z I := maximalTrajectory_solution κ hreg masses z₀
  have hc : IsPreconnected I := maximalDomain_isPreconnected κ masses z₀
  have hrest : ∀ j, (z 0).2 j = 0 := by simp [hinit, z₀]
  have horder₀ : orderedOppositeSides (z 0).1 := by simpa [hinit, z₀] using horder
  have hfirst : FirstRegularSyzygy z I 0 T := power_firstRegularSyzygy α g m hα hα2 hg hm q harea horder
  obtain ⟨hpos, hseg, hcol, hpre, hcfT⟩ := hfirst
  have hmem (t) (ht : t ∈ Ico 0 T) : t ∈ BeforeFirstCollinearity z I 0 :=
    ⟨ht.1, fun s h => hseg ⟨h.1, h.2.trans ht.2.le⟩,
      fun s h => hpre s ⟨h.1, h.2.trans_lt ht.2⟩⟩
  have hA (t) (ht : t ∈ Ico 0 T) : 0 < signedDoubleArea (z 0).1 * signedDoubleArea (z t).1 :=
    initialBranch_area_product_pos hs (hmem t ht)
  have hgaps := (positive_gaps_iff_side_order _).2
    ((orderedOppositeSides_iff _ (by simpa [hinit, z₀] using hcf)).1 horder₀)
  have hpositive (i) (hi : 0 < sideGap (z 0).1 i) : 0 < sideGap (z T).1 i :=
    pos_of_mul_pos_right
      (power_gap_at_regular_endpoint hs hα hg hm hc hpos hseg hrest hA hcol i hi.ne') hi.le
  have horderT := (positive_gaps_iff_side_order _).1 ⟨hpositive 2 hgaps.1, hpositive 0 hgaps.2⟩
  refine ⟨hs, hinit, ⟨hpos, hseg, hcol, hpre, hcfT⟩, ?_, middle_body_of_side_order hcol hcfT horderT⟩
  intro t ht
  refine ⟨(hs.2 t (hseg ht)).1, ?_⟩
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact power_side_order_on_initialBranch hs hα hg hm hc (hmem t ⟨ht.1, hlt⟩) hrest horder₀
  · exact (orderedOppositeSides_iff _ hcfT).2 horderT

end
end DroppingThreeBodies.CentralForce
