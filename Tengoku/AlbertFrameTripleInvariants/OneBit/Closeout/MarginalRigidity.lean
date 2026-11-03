import Tengoku.AlbertFrameTripleInvariants.OneBit.Closeout.FiniteRelabelling

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The pair traces of the first configuration have no relabelling symmetry

`marginal r s i j` (defined in `FiniteRelabelling`) is the explicit rational matrix of
pair traces between frames r and s. `edges_determine_frame`: a permutation σ of the
frames that preserves, for each pair of frames, the set of values occurring in that
matrix must be the identity (the three frame pairs are told apart by whether 0 and 1/36
occur). `marginal_zero_01` and `marginal_column_injective`: the first column of P, the first row
of P, and the first column of R (called S in the mathematical exposition) each have pairwise distinct entries, so a permutation of
idempotents preserving the matrices is the identity. `marginal_stabilizer_trivial` combines the two.
-/

namespace OneBit.Closeout

def edgeHas (r s : Fin 3) (v : ℚ) : Prop := ∃ i j, marginal r s i j = v
instance (r s : Fin 3) (v : ℚ) : Decidable (edgeHas r s v) := inferInstanceAs (Decidable (∃ i j, marginal r s i j = v))

theorem edges_determine_frame (σ : Equiv.Perm (Fin 3))
    (h : ∀ r s, r ≠ s → ∀ v : ℚ, edgeHas r s v ↔ edgeHas (σ r) (σ s) v) :
    σ = Equiv.refl _ := by
  have h01z := h 0 1 (by decide) 0
  have h01v := h 0 1 (by decide) (1/36)
  have h12z := h 1 2 (by decide) 0
  have hi01 := σ.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hi02 := σ.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hi12 := σ.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hs : σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 := by
    clear h
    generalize h0 : σ 0 = a at *
    generalize h1 : σ 1 = b at *
    generalize h2 : σ 2 = c at *
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      norm_num [edgeHas, marginal, Fin.exists_fin_succ] at *
    all_goals rfl
  ext r
  fin_cases r <;> simp [hs.1, hs.2.1, hs.2.2]

theorem marginal_zero_01 (i j : Fin 3) :
    marginal 0 1 i j = 0 ↔ i = 0 ∧ j = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [marginal]

theorem marginal_column_injective (r : Fin 3) (i j : Fin 3) :
    (if r = 0 then marginal 0 1 i 0 else marginal r 0 i 0) =
    (if r = 0 then marginal 0 1 j 0 else marginal r 0 j 0) → i = j := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> norm_num [marginal]

theorem marginal_stabilizer_trivial (σ : Equiv.Perm (Fin 3))
    (π : Fin 3 → Equiv.Perm (Fin 3))
    (h : ∀ r s, r ≠ s → ∀ i j,
      marginal r s i j = marginal (σ r) (σ s) (π r i) (π s j)) :
    σ = Equiv.refl _ ∧ ∀ r, π r = Equiv.refl _ := by
  have hs := edges_determine_frame σ (by
    intro r s hrs v
    constructor
    · rintro ⟨i,j,hij⟩
      exact ⟨π r i, π s j, (h r s hrs i j).symm.trans hij⟩
    · rintro ⟨i,j,hij⟩
      refine ⟨(π r).symm i, (π s).symm j, ?_⟩
      have he := h r s hrs ((π r).symm i) ((π s).symm j)
      simp only [Equiv.apply_symm_apply] at he
      exact he.trans hij)
  subst σ
  simp only [Equiv.refl_apply] at h
  have hz : marginal 0 1 (π 0 0) (π 1 0) = 0 := by
    rw [← h 0 1 (by decide) 0 0]
    norm_num [marginal]
  obtain ⟨h0,h1⟩ := (marginal_zero_01 _ _).mp hz
  refine ⟨rfl, ?_⟩
  intro r
  apply Equiv.ext
  intro i
  apply marginal_column_injective r
  fin_cases r
  · simpa [h1] using (h 0 1 (by decide) i 0).symm
  · simpa [h0] using (h 1 0 (by decide) i 0).symm
  · simpa [h0] using (h 2 0 (by decide) i 0).symm

end OneBit.Closeout
