module

public import Dropping3Bodies.Dynamics.MaximalInterval
public import Dropping3Bodies.Dynamics.OrthogonalSymmetry
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

/-! Maximal-union transport under orthogonal maps and body permutations. -/

namespace DroppingThreeBodies

noncomputable section

theorem orthogonalPhase_inverse (O : Point ≃ₗᵢ[ℝ] Point) (z : Phase) :
    orthogonalPhase O.symm (orthogonalPhase O z) = z := by
  cases z with
  | mk q v =>
      apply Prod.ext <;> funext i <;>
        simp [orthogonalPhase, orthogonalConfiguration]

noncomputable def orthogonalNewtonInitialIntervalWitness
    {z₀ : Phase} (O : Point ≃ₗᵢ[ℝ] Point)
    (w : NewtonInitialIntervalWitness z₀) :
    NewtonInitialIntervalWitness (orthogonalPhase O z₀) where
  left := w.left
  right := w.right
  trajectory := fun t => orthogonalPhase O (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by rw [w.initial]
  solution := classicalNewtonSolution_orthogonal O w.solution

noncomputable def unorthogonalNewtonInitialIntervalWitness
    {z₀ : Phase} (O : Point ≃ₗᵢ[ℝ] Point)
    (w : NewtonInitialIntervalWitness (orthogonalPhase O z₀)) :
    NewtonInitialIntervalWitness z₀ where
  left := w.left
  right := w.right
  trajectory := fun t => orthogonalPhase O.symm (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by
    rw [w.initial]
    exact orthogonalPhase_inverse O z₀
  solution := classicalNewtonSolution_orthogonal O.symm w.solution

theorem maximalNewtonUnionDomain_orthogonal
    (z₀ : Phase) (O : Point ≃ₗᵢ[ℝ] Point) :
    maximalNewtonUnionDomain (orthogonalPhase O z₀) =
      maximalNewtonUnionDomain z₀ := by
  ext t
  constructor
  · intro ht
    obtain ⟨w, hwt⟩ :=
      maximalNewtonUnionDomain_covered (orthogonalPhase O z₀) ht
    exact maximalNewtonWitness_interval_subset z₀
      (unorthogonalNewtonInitialIntervalWitness O w) hwt
  · intro ht
    obtain ⟨w, hwt⟩ := maximalNewtonUnionDomain_covered z₀ ht
    exact maximalNewtonWitness_interval_subset (orthogonalPhase O z₀)
      (orthogonalNewtonInitialIntervalWitness O w) hwt

theorem maximalNewtonUnionTrajectory_orthogonal
    (z₀ : Phase) (O : Point ≃ₗᵢ[ℝ] Point) {t : ℝ}
    (ht : t ∈ maximalNewtonUnionDomain z₀) :
    maximalNewtonUnionTrajectory (orthogonalPhase O z₀) t =
      orthogonalPhase O (maximalNewtonUnionTrajectory z₀ t) := by
  let original := maximalNewtonChosenWitness z₀ t ht
  let transformedInitial := orthogonalPhase O z₀
  have htO : t ∈ maximalNewtonUnionDomain transformedInitial := by
    rw [maximalNewtonUnionDomain_orthogonal]
    exact ht
  let transformed := maximalNewtonChosenWitness transformedInitial t htO
  let image := orthogonalNewtonInitialIntervalWitness O original
  have himageSol : ClassicalNewtonSolution image.trajectory
      (Set.Ioo image.left image.right) := image.solution
  have htransformedSol : ClassicalNewtonSolution transformed.trajectory
      (Set.Ioo transformed.left transformed.right) := transformed.solution
  have hzero : (0 : ℝ) ∈
      Set.Ioo image.left image.right ∩ Set.Ioo transformed.left transformed.right := by
    constructor
    · exact ⟨image.left_lt_zero, image.zero_lt_right⟩
    · exact ⟨transformed.left_lt_zero, transformed.zero_lt_right⟩
  have hinit : image.trajectory 0 = transformed.trajectory 0 :=
    image.initial.trans transformed.initial.symm
  have hoverlap := classicalNewton_eq_on_of_preconnected_overlap
    himageSol htransformedSol
    (isPreconnected_inter_openIntervals image.left image.right
      transformed.left transformed.right) hzero hinit
  have htImage : t ∈ Set.Ioo image.left image.right :=
    maximalNewtonChosenWitness_spec z₀ t ht
  have htTransformed : t ∈ Set.Ioo transformed.left transformed.right :=
    maximalNewtonChosenWitness_spec transformedInitial t htO
  have heq := hoverlap t ⟨htImage, htTransformed⟩
  calc
    maximalNewtonUnionTrajectory transformedInitial t = transformed.trajectory t := by
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos htO]
    _ = image.trajectory t := heq.symm
    _ = orthogonalPhase O (maximalNewtonUnionTrajectory z₀ t) := by
      change orthogonalPhase O (original.trajectory t) = _
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos ht]

theorem permutePhase_inverse (σ : Equiv.Perm (Fin 3)) (z : Phase) :
    permutePhase σ.symm (permutePhase σ z) = z := by
  cases z with
  | mk q v =>
      apply Prod.ext <;> funext i <;>
        simp [permutePhase, permuteConfiguration]

noncomputable def permuteNewtonInitialIntervalWitness
    {z₀ : Phase} (σ : Equiv.Perm (Fin 3))
    (w : NewtonInitialIntervalWitness z₀) :
    NewtonInitialIntervalWitness (permutePhase σ z₀) where
  left := w.left
  right := w.right
  trajectory := fun t => permutePhase σ (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by rw [w.initial]
  solution := classicalNewtonSolution_permute σ w.solution

noncomputable def unpermuteNewtonInitialIntervalWitness
    {z₀ : Phase} (σ : Equiv.Perm (Fin 3))
    (w : NewtonInitialIntervalWitness (permutePhase σ z₀)) :
    NewtonInitialIntervalWitness z₀ where
  left := w.left
  right := w.right
  trajectory := fun t => permutePhase σ.symm (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by
    rw [w.initial]
    exact permutePhase_inverse σ z₀
  solution := classicalNewtonSolution_permute σ.symm w.solution

theorem maximalNewtonUnionDomain_permute
    (z₀ : Phase) (σ : Equiv.Perm (Fin 3)) :
    maximalNewtonUnionDomain (permutePhase σ z₀) =
      maximalNewtonUnionDomain z₀ := by
  ext t
  constructor
  · intro ht
    obtain ⟨w, hwt⟩ := maximalNewtonUnionDomain_covered (permutePhase σ z₀) ht
    exact maximalNewtonWitness_interval_subset z₀
      (unpermuteNewtonInitialIntervalWitness σ w) hwt
  · intro ht
    obtain ⟨w, hwt⟩ := maximalNewtonUnionDomain_covered z₀ ht
    exact maximalNewtonWitness_interval_subset (permutePhase σ z₀)
      (permuteNewtonInitialIntervalWitness σ w) hwt

theorem maximalNewtonUnionTrajectory_permute
    (z₀ : Phase) (σ : Equiv.Perm (Fin 3)) {t : ℝ}
    (ht : t ∈ maximalNewtonUnionDomain z₀) :
    maximalNewtonUnionTrajectory (permutePhase σ z₀) t =
      permutePhase σ (maximalNewtonUnionTrajectory z₀ t) := by
  let original := maximalNewtonChosenWitness z₀ t ht
  let transformedInitial := permutePhase σ z₀
  have htP : t ∈ maximalNewtonUnionDomain transformedInitial := by
    rw [maximalNewtonUnionDomain_permute]
    exact ht
  let transformed := maximalNewtonChosenWitness transformedInitial t htP
  let image := permuteNewtonInitialIntervalWitness σ original
  have himageSol : ClassicalNewtonSolution image.trajectory
      (Set.Ioo image.left image.right) := image.solution
  have htransformedSol : ClassicalNewtonSolution transformed.trajectory
      (Set.Ioo transformed.left transformed.right) := transformed.solution
  have hzero : (0 : ℝ) ∈
      Set.Ioo image.left image.right ∩ Set.Ioo transformed.left transformed.right := by
    constructor
    · exact ⟨image.left_lt_zero, image.zero_lt_right⟩
    · exact ⟨transformed.left_lt_zero, transformed.zero_lt_right⟩
  have hinit : image.trajectory 0 = transformed.trajectory 0 :=
    image.initial.trans transformed.initial.symm
  have hoverlap := classicalNewton_eq_on_of_preconnected_overlap
    himageSol htransformedSol
    (isPreconnected_inter_openIntervals image.left image.right
      transformed.left transformed.right) hzero hinit
  have htImage : t ∈ Set.Ioo image.left image.right :=
    maximalNewtonChosenWitness_spec z₀ t ht
  have htTransformed : t ∈ Set.Ioo transformed.left transformed.right :=
    maximalNewtonChosenWitness_spec transformedInitial t htP
  have heq := hoverlap t ⟨htImage, htTransformed⟩
  calc
    maximalNewtonUnionTrajectory transformedInitial t = transformed.trajectory t := by
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos htP]
    _ = image.trajectory t := heq.symm
    _ = permutePhase σ (maximalNewtonUnionTrajectory z₀ t) := by
      change permutePhase σ (original.trajectory t) = _
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos ht]

end

end DroppingThreeBodies
