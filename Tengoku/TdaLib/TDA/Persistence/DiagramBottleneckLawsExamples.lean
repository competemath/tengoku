import Tengoku.TdaLib.TDA.Persistence.DiagramBottleneckLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace TDA.Persistence

private def singletonMatch : OccurrenceMatching (Fin 1) (Fin 1) (Fin 0) (Fin 0) where
  finite _ := some 0
  finite_injective := by intro i i' _ _ _; exact Subsingleton.elim i i'
  essential := Equiv.refl _

private def singletonDelete : OccurrenceMatching (Fin 1) (Fin 0) (Fin 0) (Fin 0) where
  finite _ := none
  finite_injective := by intro _ _ j; exact Fin.elim0 j
  essential := Equiv.refl _

private def singletonInsert : OccurrenceMatching (Fin 0) (Fin 1) (Fin 0) (Fin 0) where
  finite := Fin.elim0
  finite_injective := by intro i; exact Fin.elim0 i
  essential := Equiv.refl _

/-- Reindexing both finite and essential occurrences, even with repeated values,
does not change the diagram or its zero self-distance.-/
theorem bottleneck_permuted_presentations (m n : ℕ)
    (x : Fin m → ℝ × ℝ) (b : Fin n → ℝ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    bottleneck (orderedQ m n (x ∘ σ, b ∘ τ)) (orderedQ m n (x, b)) = 0 := by
  rw [orderedQ_perm]
  exact bottleneck_self _

/-- Deleting one of two identical finite occurrences has positive cost.-/
theorem bottleneck_repeated_pair_ne_zero :
    bottleneck (orderedQ 2 0 (fun _ => ((0 : ℝ), 2), Fin.elim0))
      (orderedQ 1 0 (fun _ => ((0 : ℝ), 2), Fin.elim0)) ≠ 0 := by
  intro hz
  have heq := (bottleneck_eq_zero_iff _ _).mp hz
  have hc := congrArg (fun D : Diagram ℝ => (finitePart D.points).card) heq
  simp [finitePart_orderedQ] at hc

end TDA.Persistence
