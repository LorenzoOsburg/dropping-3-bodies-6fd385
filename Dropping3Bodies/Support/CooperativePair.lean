module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact

@[expose] public section

namespace DroppingThreeBodies

/-- The integral of the product of two continuous, strictly positive
    coefficients is strictly positive on every nontrivial compact interval. -/
theorem intervalIntegral_pos_mul_of_continuousOn_pos
    {a b : ℝ} {f g : ℝ → ℝ} (hab : a < b)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfpos : ∀ x ∈ Set.Icc a b, 0 < f x)
    (hgpos : ∀ x ∈ Set.Icc a b, 0 < g x) :
    0 < ∫ x in a..b, f x * g x := by
  apply intervalIntegral.integral_pos hab (hfcont.mul hgcont)
  · intro x hx
    exact le_of_lt (mul_pos
      (hfpos x ⟨le_of_lt hx.1, hx.2⟩)
      (hgpos x ⟨le_of_lt hx.1, hx.2⟩))
  · exact ⟨b, ⟨le_of_lt hab, le_rfl⟩,
      mul_pos (hfpos b ⟨le_of_lt hab, le_rfl⟩)
        (hgpos b ⟨le_of_lt hab, le_rfl⟩)⟩

/-- A continuous function with nonnegative pointwise derivative is monotone
    on a convex set, stated using `HasDerivAt` data. -/
theorem monotoneOn_of_hasDerivAt_nonneg
    {D : Set ℝ} {f g : ℝ → ℝ} (hD : Convex ℝ D)
    (hderiv : ∀ x ∈ D, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ D, 0 ≤ g x) : MonotoneOn f D := by
  apply monotoneOn_of_deriv_nonneg hD
  · intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hderiv x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

/-- A continuous function with strictly positive derivative is strictly
    monotone on a convex set, stated using `HasDerivAt` data. -/
theorem strictMonoOn_of_hasDerivAt_pos
    {D : Set ℝ} {f g : ℝ → ℝ} (hD : Convex ℝ D)
    (hderiv : ∀ x ∈ D, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ D, 0 < g x) : StrictMonoOn f D := by
  apply strictMonoOn_of_deriv_pos hD
  · intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [(hderiv x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

/-- On an interval where `X` is positive, the equation `Y' = b X` with `b>0`
    forces `Y` to be strictly increasing. -/
theorem cooperative_second_strictMono
    {a b₀ : ℝ} {X Y b : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc a b₀, HasDerivAt Y (b t * X t) t)
    (hX : ∀ t ∈ Set.Icc a b₀, 0 < X t)
    (hb : ∀ t ∈ Set.Icc a b₀, 0 < b t) :
    StrictMonoOn Y (Set.Icc a b₀) := by
  apply strictMonoOn_of_hasDerivAt_pos (convex_Icc a b₀) hderiv
  intro t ht
  exact mul_pos (hb t ht) (hX t ht)

/-- If additionally `Y(a)=0`, then its second component is strictly positive
    at every later time in the interval. -/
theorem cooperative_second_pos_of_first_pos
    {a b₀ t : ℝ} {X Y b : ℝ → ℝ}
    (hab : a ≤ b₀) (ht : t ∈ Set.Icc a b₀) (hat : a < t)
    (hY₀ : Y a = 0)
    (hderiv : ∀ s ∈ Set.Icc a b₀, HasDerivAt Y (b s * X s) s)
    (hX : ∀ s ∈ Set.Icc a b₀, 0 < X s)
    (hb : ∀ s ∈ Set.Icc a b₀, 0 < b s) : 0 < Y t := by
  have hm := cooperative_second_strictMono hderiv hX hb
  have hlt := hm (⟨le_rfl, hab⟩) ht hat
  rw [hY₀] at hlt
  exact hlt

/-- While `Y` is nonnegative, the equation `X' = c Y` with `c≥0` makes the
    first component nondecreasing. -/
theorem cooperative_first_monotone
    {a b₀ : ℝ} {X Y c : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc a b₀, HasDerivAt X (c t * Y t) t)
    (hY : ∀ t ∈ Set.Icc a b₀, 0 ≤ Y t)
    (hc : ∀ t ∈ Set.Icc a b₀, 0 ≤ c t) :
    MonotoneOn X (Set.Icc a b₀) := by
  apply monotoneOn_of_hasDerivAt_nonneg (convex_Icc a b₀) hderiv
  intro t ht
  exact mul_nonneg (hc t ht) (hY t ht)

/-- A cooperative pair cannot reach a nonpositive first component from
    positive/zero initial data. This is the compact first-zero argument. -/
theorem cooperative_no_nonpositive_endpoint
    {a T : ℝ} (haT : a < T) {X Y b c : ℝ → ℝ}
    (hXcont : ContinuousOn X (Set.Icc a T))
    (hYcont : ContinuousOn Y (Set.Icc a T))
    (hX₀ : 0 < X a) (hY₀ : Y a = 0)
    (hXderiv : ∀ t ∈ Set.Icc a T, HasDerivAt X (c t * Y t) t)
    (hYderiv : ∀ t ∈ Set.Icc a T, HasDerivAt Y (b t * X t) t)
    (hc : ∀ t ∈ Set.Icc a T, 0 ≤ c t)
    (hb : ∀ t ∈ Set.Icc a T, 0 < b t)
    (hXT : X T ≤ 0) : False := by
  have hXcontinuous : ContinuousOn X (Set.Icc a T) := hXcont
  have hYcontinuous : ContinuousOn Y (Set.Icc a T) := hYcont
  let Z : Set ℝ := Set.Icc a T ∩ X ⁻¹' ({0} : Set ℝ)
  have hZne : Z.Nonempty := by
    by_cases hXT0 : X T = 0
    · exact ⟨T, ⟨⟨haT.le, le_rfl⟩, hXT0⟩⟩
    · have hXTneg : X T < 0 := lt_of_le_of_ne hXT hXT0
      have hIV := intermediate_value_Icc' haT.le hXcontinuous
      have hzero_mem : 0 ∈ Set.Icc (X T) (X a) :=
        ⟨le_of_lt hXTneg, le_of_lt hX₀⟩
      obtain ⟨u, hu, hXu⟩ := hIV hzero_mem
      exact ⟨u, ⟨hu, hXu⟩⟩
  letI : CompactSpace (Set.Icc a T) :=
    (isCompact_iff_compactSpace (s := Set.Icc a T)).mp isCompact_Icc
  let Zsub : Set (Set.Icc a T) := {u | X u = 0}
  have hXrestrict : Continuous (fun u : Set.Icc a T => X u) := hXcont.restrict
  have hZsubcompact : IsCompact Zsub :=
    isCompact_singleton.preimage_continuous hXrestrict
  have hZeq : (Subtype.val : Set.Icc a T → ℝ) '' Zsub = Z := by
    ext x
    simp [Z, Zsub, and_assoc, and_comm]
  have hZcompact : IsCompact Z := by
    rw [← hZeq]
    exact hZsubcompact.image continuous_subtype_val
  obtain ⟨t₀, ht₀Z, hmin⟩ := hZcompact.exists_isMinOn hZne continuousOn_id
  have ht₀ : t₀ ∈ Set.Icc a T := ht₀Z.1
  have hXt₀ : X t₀ = 0 := by
    simpa [Z] using ht₀Z.2
  have hat₀ : a < t₀ := by
    by_contra hnot
    have hle : t₀ ≤ a := le_of_not_gt hnot
    have heq : t₀ = a := le_antisymm hle ht₀.1
    subst t₀
    exact (ne_of_gt hX₀) hXt₀
  have hXbefore : ∀ s ∈ Set.Icc a t₀, s < t₀ → 0 < X s := by
    intro s hs hst
    have hXne : X s ≠ 0 := by
      intro hXs
      have hsZ : s ∈ Z := by
        refine ⟨⟨hs.1, hs.2.trans ht₀.2⟩, ?_⟩
        simp [hXs]
      have hmin_s := hmin hsZ
      change t₀ ≤ s at hmin_s
      exact (not_le_of_gt hst) hmin_s
    have hXnotneg : ¬ X s < 0 := by
      intro hneg
      have hXas : ContinuousOn X (Set.Icc a s) := hXcontinuous.mono (by
        intro x hx
        exact ⟨hx.1, le_trans hx.2 (le_trans hs.2 ht₀.2)⟩)
      have hIV := intermediate_value_Icc' hs.1 hXas
      have hzero_mem : 0 ∈ Set.Icc (X s) (X a) :=
        ⟨le_of_lt hneg, le_of_lt hX₀⟩
      obtain ⟨u, hu, hXu⟩ := hIV hzero_mem
      have huZ : u ∈ Z := by
        refine ⟨⟨hu.1, le_trans hu.2 (le_trans (le_of_lt hst) ht₀.2)⟩, ?_⟩
        simp [hXu]
      have hmin_u := hmin huZ
      change t₀ ≤ u at hmin_u
      exact (not_le_of_gt hst) (hmin_u.trans hu.2)
    exact lt_of_le_of_ne (le_of_not_gt hXnotneg) (Ne.symm hXne)
  have hYpositive_before : ∀ s ∈ Set.Icc a t₀, a < s → s < t₀ → 0 < Y s := by
    intro s hs has hst
    have hXpos : ∀ r ∈ Set.Icc a s, 0 < X r := by
      intro r hr
      exact hXbefore r ⟨hr.1, le_trans hr.2 (le_of_lt hst)⟩
        (lt_of_le_of_lt hr.2 hst)
    exact cooperative_second_pos_of_first_pos has.le ⟨has.le, le_rfl⟩ has hY₀
      (fun r hr => hYderiv r ⟨hr.1, le_trans hr.2 (le_trans (le_of_lt hst) ht₀.2)⟩)
      hXpos (fun r hr => hb r ⟨hr.1, le_trans hr.2 (le_trans (le_of_lt hst) ht₀.2)⟩)
  have hYnonneg : ∀ s ∈ Set.Icc a t₀, 0 ≤ Y s := by
    intro s hs
    by_cases hsa : s = a
    · subst s
      simp [hY₀]
    by_cases hst : s < t₀
    · have has : a < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
      exact le_of_lt (hYpositive_before s hs has hst)
    · have hseq : s = t₀ := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hst hlt
        · exact (not_lt_of_ge hs.2) hgt
      subst s
      by_contra hnegative
      have hYtneg : Y t₀ < 0 := lt_of_not_ge hnegative
      have hmid_mem : Y t₀ / 2 ∈ Set.Icc (Y t₀) (Y a) := by
        constructor
        · linarith
        · rw [hY₀]
          linarith
      have hYat₀ : ContinuousOn Y (Set.Icc a t₀) := hYcontinuous.mono (by
        intro x hx
        exact ⟨hx.1, le_trans hx.2 ht₀.2⟩)
      have hIV := intermediate_value_Icc' ht₀.1 hYat₀
      obtain ⟨u, hu, hYu⟩ := hIV hmid_mem
      have hau : a < u := by
        by_contra hnot
        have heq : u = a := le_antisymm (le_of_not_gt hnot) hu.1
        subst u
        rw [hY₀] at hYu
        linarith
      have hut₀ : u < t₀ := by
        by_contra hnot
        have heq : u = t₀ := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hnot hlt
          · exact (not_lt_of_ge hu.2) hgt
        subst u
        linarith
      have hYupos := hYpositive_before u hu hau hut₀
      rw [hYu] at hYupos
      linarith
  have hXmono := cooperative_first_monotone
    (fun s hs => hXderiv s ⟨hs.1, le_trans hs.2 ht₀.2⟩)
    hYnonneg (fun s hs => hc s ⟨hs.1, le_trans hs.2 ht₀.2⟩)
  have hXle := hXmono ⟨le_rfl, hat₀.le⟩ ⟨ht₀.1, le_rfl⟩ hat₀.le
  rw [hXt₀] at hXle
  linarith


/-- A positive-start solution has a positive first coordinate throughout its
    interval. This uses the compact first-zero argument and is conditional on
    the displayed differentiable curves; it makes no ODE-existence claim. -/
theorem cooperative_first_pos_on_Icc
    {a T : ℝ} {X Y b c : ℝ → ℝ}
    (hXcont : ContinuousOn X (Set.Icc a T))
    (hYcont : ContinuousOn Y (Set.Icc a T))
    (hX₀ : 0 < X a) (hY₀ : Y a = 0)
    (hXderiv : ∀ t ∈ Set.Icc a T, HasDerivAt X (c t * Y t) t)
    (hYderiv : ∀ t ∈ Set.Icc a T, HasDerivAt Y (b t * X t) t)
    (hc : ∀ t ∈ Set.Icc a T, 0 ≤ c t)
    (hb : ∀ t ∈ Set.Icc a T, 0 < b t) :
    ∀ t ∈ Set.Icc a T, 0 < X t := by
  intro t ht
  by_contra hnot
  have hnonpos : X t ≤ 0 := le_of_not_gt hnot
  by_cases hat : a < t
  · have hXcont_t : ContinuousOn X (Set.Icc a t) := hXcont.mono (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 ht.2⟩)
    have hYcont_t : ContinuousOn Y (Set.Icc a t) := hYcont.mono (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 ht.2⟩)
    have hfalse := cooperative_no_nonpositive_endpoint hat hXcont_t hYcont_t hX₀ hY₀
      (fun s hs => hXderiv s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (fun s hs => hYderiv s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (fun s hs => hc s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (fun s hs => hb s ⟨hs.1, le_trans hs.2 ht.2⟩)
      hnonpos
    exact hfalse
  · have hta : t = a := le_antisymm (le_of_not_gt hat) ht.1
    subst t
    exact (not_le_of_gt hX₀) hnonpos

/-- Positive-start solutions of a cooperative pair retain X>0, while Y becomes
    strictly positive immediately after the initial time. -/
theorem cooperative_pair_signs
    {a T : ℝ} (haT : a ≤ T) {X Y b c : ℝ → ℝ}
    (hXcont : ContinuousOn X (Set.Icc a T))
    (hYcont : ContinuousOn Y (Set.Icc a T))
    (hX₀ : 0 < X a) (hY₀ : Y a = 0)
    (hXderiv : ∀ t ∈ Set.Icc a T, HasDerivAt X (c t * Y t) t)
    (hYderiv : ∀ t ∈ Set.Icc a T, HasDerivAt Y (b t * X t) t)
    (hc : ∀ t ∈ Set.Icc a T, 0 ≤ c t)
    (hb : ∀ t ∈ Set.Icc a T, 0 < b t) :
    (∀ t ∈ Set.Icc a T, 0 < X t) ∧
      (∀ t ∈ Set.Icc a T, a < t → 0 < Y t) := by
  constructor
  · exact cooperative_first_pos_on_Icc hXcont hYcont hX₀ hY₀
      hXderiv hYderiv hc hb
  · intro t ht hat
    exact cooperative_second_pos_of_first_pos haT ht hat hY₀ hYderiv
      (cooperative_first_pos_on_Icc hXcont hYcont hX₀ hY₀
        hXderiv hYderiv hc hb) hb

end DroppingThreeBodies