module

public import NBody.LocalExistence

@[expose] public section

namespace NBody

/-- With one particle there are no collisions and no gravitational force. -/
theorem acceleration_eq_zero_of_subsingleton {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Subsingleton ι] {d : ℕ}
    (G : ℝ) (m : ι → ℝ) (q : Config ι d) (i : ι) :
    acceleration G m q i = 0 := by
  classical
  unfold acceleration
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j = i := Subsingleton.elim j i
  simp [hji]

/-- The single-particle Newton problem has an explicit solution for all real
 times: uniform motion on the whole (open) real line. -/
theorem exists_global_solution_of_subsingleton {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] [Subsingleton ι] {d : ℕ}
    (G : ℝ) (m : ι → ℝ) (a : ℝ)
    (z₀ : Phase ι d) :
    ∃ z : ℝ → Phase ι d, z a = z₀ ∧ ClassicalSolution G m z Set.univ := by
  classical
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let q₀ := z₀.1 i₀
  let v₀ := z₀.2 i₀
  let z : ℝ → Phase ι d := fun t =>
    (fun i => q₀ + (t - a) • v₀, fun _ => v₀)
  have hinit : z a = z₀ := by
    apply Prod.ext
    · funext i
      have hi : i = i₀ := Subsingleton.elim i i₀
      subst i
      simp [z, q₀, v₀]
    · funext i
      have hi : i = i₀ := Subsingleton.elim i i₀
      subst i
      rfl
  refine ⟨z, hinit, isOpen_univ, ?_⟩
  intro t ht
  constructor
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · have hpos : HasDerivAt (fun s => fun _ : ι => q₀ + (s - a) • v₀)
        (fun _ => v₀) t := by
      apply hasDerivAt_pi.mpr
      intro i
      have hid : HasDerivAt (fun s : ℝ => s - a) 1 t := by
        simpa using (hasDerivAt_id t).sub_const a
      simpa [smul_eq_mul] using (hid.smul_const v₀).const_add q₀
    have hvel : HasDerivAt (fun _ : ℝ => fun _ : ι => v₀)
        (fun _ : ι => (0 : EuclideanSpace ℝ (Fin d))) t := by
      exact hasDerivAt_const t (fun _ : ι => v₀)
    have hphase : HasDerivAt z
        ((fun _ => v₀), fun _ : ι => (0 : EuclideanSpace ℝ (Fin d))) t := by
      exact (hpos.prodMk hvel)
    have hacc : acceleration G m (z t).1 = fun _ => (0 : EuclideanSpace ℝ (Fin d)) := by
      funext i
      exact acceleration_eq_zero_of_subsingleton G m (z t).1 i
    simpa [z, vectorField, hacc] using hphase

end NBody
