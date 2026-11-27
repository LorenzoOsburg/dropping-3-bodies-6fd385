module

public import NBody.Basic
public import NBody.Configuration.MassPairing

@[expose] public section

namespace NBody

noncomputable section

/-- A phase point with momenta represented by Euclidean-space configurations.
This wrapper is distinct from the existing position/velocity phase; the
continuous dual identification is not yet part of the API. -/
structure MomentumState (ι : Type*) [Fintype ι] (d : ℕ) where
  position : Config ι d
  momentum : Config ι d

/-- The finite-dimensional configuration-cotangent pairing. -/
def configurationPairing {ι : Type*} [Fintype ι] {d : ℕ}
    (q p : Config ι d) : ℝ :=
  ∑ i, inner ℝ (q i) (p i)

/-- Canonical symplectic form, with convention
ω((δq,δp),(ηq,ηp)) = δq·ηp - ηq·δp. -/
def canonicalForm {ι : Type*} [Fintype ι] {d : ℕ}
    (x y : MomentumState ι d) : ℝ :=
  configurationPairing x.position y.momentum -
    configurationPairing y.position x.momentum

theorem canonicalForm_self {ι : Type*} [Fintype ι] {d : ℕ}
    (x : MomentumState ι d) : canonicalForm x x = 0 := by
  simp [canonicalForm]

theorem canonicalForm_skew {ι : Type*} [Fintype ι] {d : ℕ}
    (x y : MomentumState ι d) : canonicalForm x y = -canonicalForm y x := by
  simp [canonicalForm, sub_eq_add_neg, add_comm, configurationPairing]

/-- The mass Legendre map from velocities to momenta, represented in the
finite-dimensional Euclidean configuration space. -/
def legendreMap {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (v : Config ι d) : Config ι d := fun i => m i • v i

theorem legendreMap_injective {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (hm : ∀ i, m i ≠ 0) :
    Function.Injective (legendreMap (d := d) m) := by
  intro v w h
  funext i
  have hi := congrFun h i
  have hsmul : m i • (v i - w i) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr hi
  rcases smul_eq_zero.mp hsmul with hm0 | hdiff
  · exact (hm i hm0).elim
  · exact sub_eq_zero.mp hdiff

theorem legendreMap_surjective {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (hm : ∀ i, m i ≠ 0) :
    Function.Surjective (legendreMap (d := d) m) := by
  intro p
  refine ⟨fun i => (m i)⁻¹ • p i, ?_⟩
  funext i
  simp [legendreMap, hm i]

/-- The unweighted configuration pairing is positive definite. -/
theorem configurationPairing_self_pos {ι : Type*} [Fintype ι] {d : ℕ}
    {q : Config ι d} (hq : q ≠ 0) : 0 < configurationPairing q q := by
  have h := massPairing_self_pos (fun _ : ι => (1 : ℝ))
    (by intro i; norm_num) hq
  simpa [configurationPairing, massPairing] using h

/-- Nondegeneracy of the canonical alternating form: every nonzero phase
vector pairs nontrivially with some test vector. -/
theorem canonicalForm_nondegenerate_left {ι : Type*} [Fintype ι] {d : ℕ}
    {x : MomentumState ι d}
    (hx : x.position ≠ 0 ∨ x.momentum ≠ 0) :
    ∃ y, canonicalForm x y ≠ 0 := by
  by_cases hq : x.position = 0
  · have hp : x.momentum ≠ 0 := by
      rcases hx with hpos | hm
      · exact (hpos hq).elim
      · exact hm
    let y : MomentumState ι d := ⟨x.momentum, 0⟩
    refine ⟨y, ?_⟩
    have hpos := configurationPairing_self_pos hp
    have hval : canonicalForm x y = -configurationPairing x.momentum x.momentum := by
      simp [canonicalForm, configurationPairing, y, hq]
    rw [hval]
    exact neg_ne_zero.mpr (ne_of_gt hpos)
  · let y : MomentumState ι d := ⟨0, x.position⟩
    refine ⟨y, ?_⟩
    have hpos : x.position ≠ 0 := fun h => hq h
    have hpos' := configurationPairing_self_pos hpos
    have hval : canonicalForm x y = configurationPairing x.position x.position := by
      simp [canonicalForm, configurationPairing, y]
    rw [hval]
    exact ne_of_gt hpos'


end

end NBody
