module

public import Dropping3Bodies.Support.CooperativePair
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

/-!
# Scalar second-order comparison

A constant upper or lower bound for the second derivative yields a quadratic
comparison estimate from initial position and velocity. The proof uses only
monotonicity on compact intervals and explicit derivative data.
-/

namespace DroppingThreeBodies

/-- If `f'' ≤ -c` on `[0,T]` and `f(0)=a`, `f'(0)=0`, then
    `f(t) ≤ a - c t²/2` throughout the interval. -/
theorem secondOrder_upper_bound_of_deriv_le
    {T a c : ℝ} {f f' f'' : ℝ → ℝ}
    (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc 0 T, HasDerivAt f' (f'' t) t)
    (hsecond : ∀ t ∈ Set.Icc 0 T, f'' t ≤ -c)
    (hinit : f 0 = a) (hinit' : f' 0 = 0) :
    ∀ t ∈ Set.Icc 0 T, f t ≤ a - c * t ^ 2 / 2 := by
  let g : ℝ → ℝ := fun t => -f' t - c * t
  have hgderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt g (-f'' t - c) t := by
    intro t ht
    have h := (hf' t ht).neg.sub
      (HasDerivAt.const_mul c (hasDerivAt_id t))
    change HasDerivAt (fun s => -f' s - c * s) (-f'' t - c) t
    convert h using 1 <;> try rfl
    ring
  have hg_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ -f'' t - c := by
    intro t ht
    linarith [hsecond t ht]
  have hgmono : MonotoneOn g (Set.Icc 0 T) :=
    monotoneOn_of_hasDerivAt_nonneg (convex_Icc 0 T) hgderiv hg_nonneg
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hgnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ g t := by
    intro t ht
    have hm := hgmono h0 ht ht.1
    dsimp [g] at hm
    simp [hinit'] at hm
    linarith
  intro t ht
  have hgt := hgnonneg t ht
  let k : ℝ → ℝ := fun s => -f s - (c / 2) * s ^ 2
  have hkderiv : ∀ s ∈ Set.Icc 0 T, HasDerivAt k (g s) s := by
    intro s hs
    have hpow := hasDerivAt_pow 2 s
    have h := (hf s hs).neg.sub (HasDerivAt.const_mul (c / 2) hpow)
    change HasDerivAt (fun r => -f r - (c / 2) * r ^ 2)
      (-f' s - c * s) s
    convert h using 1 <;> try rfl
    ring
  have hkmono : MonotoneOn k (Set.Icc 0 T) :=
    monotoneOn_of_hasDerivAt_nonneg (convex_Icc 0 T) hkderiv hgnonneg
  have hkt := hkmono h0 ht ht.1
  dsimp [k] at hkt
  simp [hinit] at hkt
  nlinarith [hgt, hkt]

/-- A nonincreasing positive function whose acceleration strengthens to
    `f'' ≤ -1/(4a²)` below its initial value cannot remain positive as far as
    `sqrt (8a³)`. -/
theorem no_positive_segment_to_sqrt_eight_scale
    {a T : ℝ} {f f' f'' : ℝ → ℝ}
    (ha : 0 < a)
    (hT : T = Real.sqrt (8 * a ^ 3))
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc 0 T, HasDerivAt f' (f'' t) t)
    (hconcave : ∀ t ∈ Set.Icc 0 T, f'' t ≤ 0)
    (hforce : ∀ t ∈ Set.Icc 0 T, f t ≤ a →
      f'' t ≤ -(1 / (4 * a ^ 2)))
    (hinit : f 0 = a) (hinit' : f' 0 = 0)
    (hpositive : ∀ t ∈ Set.Icc 0 T, 0 < f t) : False := by
  have hTnonneg : 0 ≤ T := by rw [hT]; positivity
  have hweak := secondOrder_upper_bound_of_deriv_le hTnonneg
    (a := a) (c := 0) hf hf'
    (by intro t ht; simpa using hconcave t ht) hinit hinit'
  have hstrong := secondOrder_upper_bound_of_deriv_le hTnonneg
    (a := a) (c := 1 / (4 * a ^ 2)) hf hf'
    (by intro t ht; apply hforce t ht; simpa using hweak t ht) hinit hinit'
  have hTpos : 0 < T := by rw [hT]; positivity
  have hT2 : T ^ 2 = 8 * a ^ 3 := by
    rw [hT, Real.sq_sqrt (by positivity)]
  have hdrop : a - (1 / (4 * a ^ 2)) * T ^ 2 / 2 = 0 := by
    rw [hT2]
    field_simp [ne_of_gt ha]
    ring
  have hbound := hstrong T ⟨le_of_lt hTpos, le_rfl⟩
  rw [hdrop] at hbound
  have hpos := hpositive T ⟨le_of_lt hTpos, le_rfl⟩
  linarith
/-- If `h'' ≥ -c` with initial data `h(0)=H`, `h'(0)=0`, then
    `h(t) ≥ H - c t²/2` on `[0,T]`. -/
theorem secondOrder_lower_bound_of_deriv_ge
    {T H c : ℝ} {h h' h'' : ℝ → ℝ}
    (hT : 0 ≤ T)
    (hh : ∀ t ∈ Set.Icc 0 T, HasDerivAt h (h' t) t)
    (hh' : ∀ t ∈ Set.Icc 0 T, HasDerivAt h' (h'' t) t)
    (hsecond : ∀ t ∈ Set.Icc 0 T, -c ≤ h'' t)
    (hinit : h 0 = H) (hinit' : h' 0 = 0) :
    ∀ t ∈ Set.Icc 0 T, H - c * t ^ 2 / 2 ≤ h t := by
  have hneg := secondOrder_upper_bound_of_deriv_le
    (T := T) (a := -H) (c := -c)
    (f := fun t => -h t) (f' := fun t => -h' t)
    (f'' := fun t => -h'' t) hT
    (fun t ht => (hh t ht).neg)
    (fun t ht => (hh' t ht).neg)
    (by intro t ht; linarith [hsecond t ht])
    (by simp [hinit]) (by simp [hinit'])
  intro t ht
  have h := hneg t ht
  nlinarith [h]

/-- A lower height barrier is invariant if its second derivative has a
    uniform lower bound whenever the height is above the barrier, and the
    corresponding quadratic comparison stays strictly above the barrier. -/
theorem lower_barrier_preserved_of_second_deriv_bound
    {T L C : ℝ} {h h' h'' : ℝ → ℝ}
    (hT : 0 ≤ T)
    (hh : ∀ t ∈ Set.Icc 0 T, HasDerivAt h (h' t) t)
    (hh' : ∀ t ∈ Set.Icc 0 T, HasDerivAt h' (h'' t) t)
    (hC : 0 ≤ C)
    (hsecond : ∀ t ∈ Set.Icc 0 T, L ≤ h t → -C ≤ h'' t)
    (hinit : L < h 0) (hinit' : h' 0 = 0)
    (hmargin : L < h 0 - C * T ^ 2 / 2) :
    ∀ t ∈ Set.Icc 0 T, L < h t := by
  have hcont : ContinuousOn h (Set.Icc 0 T) := by
    intro t ht
    exact (hh t ht).continuousAt.continuousWithinAt
  intro t ht
  by_contra hnot
  have hbad : h t ≤ L := not_lt.mp hnot
  let D := Set.Icc 0 t
  let S : Set D := {s | h s.val ≤ L}
  have htSub : Set.Icc 0 t ⊆ Set.Icc 0 T := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 ht.2⟩
  haveI : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_Icc
  have hSclosed : IsClosed S := by
    change IsClosed ((fun s : D => h s.val) ⁻¹' Set.Iic L)
    exact isClosed_Iic.preimage
      (continuousOn_iff_continuous_restrict.mp (hcont.mono htSub))
  have hScompact : IsCompact S := hSclosed.isCompact
  have hSne : S.Nonempty := ⟨⟨t, ⟨ht.1, le_rfl⟩⟩, hbad⟩
  obtain ⟨τ, hτ⟩ := hScompact.exists_isLeast hSne
  have hτbad : h (τ : ℝ) ≤ L := hτ.1
  have hτleT : (τ : ℝ) ≤ t := τ.property.2
  have h0τ : 0 < (τ : ℝ) := by
    by_contra hnotpos
    have hτeq : (τ : ℝ) = 0 := by linarith [τ.property.1]
    rw [hτeq] at hτbad
    exact (not_le_of_gt hinit) hτbad
  have hfirst : ∀ s ∈ Set.Ioo 0 (τ : ℝ), L < h s := by
    intro s hs
    have hsD : s ∈ D := ⟨le_of_lt hs.1, le_trans (le_of_lt hs.2) hτleT⟩
    by_contra hnotAbove
    have hsBad : h s ≤ L := not_lt.mp hnotAbove
    have hsMem : (⟨s, hsD⟩ : D) ∈ S := hsBad
    have hτleS : (τ : ℝ) ≤ s := hτ.2 hsMem
    exact (not_le_of_gt hs.2) hτleS
  have hcontSeg : ContinuousOn h (Set.Icc 0 (τ : ℝ)) :=
    hcont.mono (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 (le_trans hτleT ht.2)⟩)
  have hτge : L ≤ h (τ : ℝ) := by
    by_contra hnotge
    have hτlt : h (τ : ℝ) < L := not_le.mp hnotge
    have hLmem : L ∈ Set.Icc (h (τ : ℝ)) (h 0) := ⟨le_of_lt hτlt, le_of_lt hinit⟩
    have himage := (intermediate_value_Icc' h0τ.le hcontSeg) hLmem
    rcases himage with ⟨s, hs, hseq⟩
    have hsD : s ∈ D := ⟨hs.1, le_trans hs.2 hτleT⟩
    have hsMem : (⟨s, hsD⟩ : D) ∈ S := by
      change h s ≤ L
      rw [hseq]
    have hτles : (τ : ℝ) ≤ s := hτ.2 hsMem
    have hτeq : (τ : ℝ) = s := le_antisymm hτles hs.2
    rw [← hτeq] at hseq
    linarith
  have hlower : ∀ s ∈ Set.Icc 0 (τ : ℝ), L ≤ h s := by
    intro s hs
    by_cases hseq : s = (τ : ℝ)
    · simpa [hseq] using hτge
    · have hst : s < (τ : ℝ) := by
        rcases lt_or_eq_of_le hs.2 with hlt | heq
        · exact hlt
        · exact False.elim (hseq heq)
      by_cases hs0 : s = 0
      · subst s
        exact le_of_lt hinit
      · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        exact le_of_lt (hfirst s ⟨hspos, hst⟩)
  have hsecondτ : ∀ s ∈ Set.Icc 0 (τ : ℝ), -C ≤ h'' s := by
    intro s hs
    exact hsecond s (⟨hs.1, le_trans hs.2 (le_trans hτleT ht.2)⟩) (hlower s hs)
  have hcompare := secondOrder_lower_bound_of_deriv_ge
    (T := (τ : ℝ)) (H := h 0) (c := C) h0τ.le
    (fun s hs => hh s ⟨hs.1, le_trans hs.2 (le_trans hτleT ht.2)⟩)
    (fun s hs => hh' s ⟨hs.1, le_trans hs.2 (le_trans hτleT ht.2)⟩)
    hsecondτ rfl hinit'
  have hτcompare := hcompare (τ : ℝ) ⟨h0τ.le, le_rfl⟩
  have hτsq : (τ : ℝ) ^ 2 ≤ T ^ 2 := by
    have hprod : 0 ≤ (T - (τ : ℝ)) * (T + (τ : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr (le_trans hτleT ht.2)) (by positivity)
    nlinarith [hprod]
  have hscale : C / 2 * (τ : ℝ) ^ 2 ≤ C / 2 * T ^ 2 :=
    mul_le_mul_of_nonneg_left hτsq (div_nonneg hC (by norm_num))
  nlinarith [hτbad, hτge, hmargin, hτcompare, hscale]
end DroppingThreeBodies