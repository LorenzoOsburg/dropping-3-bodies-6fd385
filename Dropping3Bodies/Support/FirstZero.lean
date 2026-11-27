module

public import Mathlib

@[expose] public section

namespace DroppingThreeBodies

/-- On a compact interval, a continuous real-valued curve which starts
positive and is zero at the right endpoint has a first zero. It stays
strictly positive before that zero. This is the reusable topological part of
the first-syzygy argument; no dynamics or collision convention is assumed. -/
theorem exists_first_zero_Icc (f : ℝ → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hstart : 0 < f 0)
    (hend : f T = 0) :
    ∃ τ ∈ Set.Icc 0 T, 0 < τ ∧ f τ = 0 ∧
      ∀ t ∈ Set.Ico 0 τ, 0 < f t := by
  let Z : Set ℝ := Set.Icc 0 T ∩ f ⁻¹' ({0} : Set ℝ)
  have hZne : Z.Nonempty := ⟨T, ⟨⟨le_of_lt hT, le_rfl⟩, hend⟩⟩
  letI : CompactSpace (Set.Icc 0 T) :=
    (isCompact_iff_compactSpace (s := Set.Icc 0 T)).mp isCompact_Icc
  let Zsub : Set (Set.Icc 0 T) := {x | f x = 0}
  have hfrestrict : Continuous (fun x : Set.Icc 0 T => f x) := hcont.restrict
  have hZsubcompact : IsCompact Zsub :=
    isCompact_singleton.preimage_continuous hfrestrict
  have hZeq : (Subtype.val : Set.Icc 0 T → ℝ) '' Zsub = Z := by
    ext x
    simp [Z, Zsub, and_comm]
  have hZcompact : IsCompact Z := by
    rw [← hZeq]
    exact hZsubcompact.image continuous_subtype_val
  obtain ⟨τ, hτZ, hmin⟩ := hZcompact.exists_isMinOn hZne continuousOn_id
  have hτinterval : τ ∈ Set.Icc 0 T := hτZ.1
  have hτzero : f τ = 0 := by
    simpa [Z] using hτZ.2
  have hτpos : 0 < τ := by
    by_contra hnot
    have hτzeroTime : τ = 0 := le_antisymm (le_of_not_gt hnot) hτinterval.1
    subst τ
    linarith
  have hτmin : ∀ t ∈ Set.Icc 0 T, f t = 0 → τ ≤ t := by
    intro t ht hft
    have htZ : t ∈ Z := ⟨ht, hft⟩
    have hmin' := hmin htZ
    change τ ≤ t at hmin'
    exact hmin'
  have hbefore : ∀ t ∈ Set.Ico 0 τ, 0 < f t := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 T :=
      ⟨ht.1, le_trans (le_of_lt ht.2) hτinterval.2⟩
    have hftne : f t ≠ 0 := by
      intro hft
      have hle := hτmin t htIcc hft
      exact (not_le_of_gt ht.2) hle
    have hftnonneg : ¬ f t < 0 := by
      intro hneg
      have hcont' : ContinuousOn f (Set.Icc 0 t) := hcont.mono (by
        intro x hx
        exact ⟨hx.1, le_trans hx.2 (le_trans (le_of_lt ht.2) hτinterval.2)⟩)
      have hIV := intermediate_value_Icc' ht.1 hcont'
      have hzero : 0 ∈ Set.Icc (f t) (f 0) :=
        ⟨le_of_lt hneg, le_of_lt hstart⟩
      obtain ⟨u, hu, hfu⟩ := hIV hzero
      have hminu := hτmin u
        ⟨hu.1, le_trans (le_trans hu.2 (le_of_lt ht.2)) hτinterval.2⟩ hfu
      exact (not_le_of_gt (lt_of_le_of_lt hu.2 ht.2)) hminu
    exact lt_of_le_of_ne (le_of_not_gt hftnonneg) (Ne.symm hftne)
  exact ⟨τ, hτinterval, hτpos, hτzero, hbefore⟩

end DroppingThreeBodies
