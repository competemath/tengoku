import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticPairStepCoverage
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_four_step_pair` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_fixed_twelve_triple_alignment` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

structure HyperbolicTriple (omega : BilinForm (K := K) (V := V))
    (u v : Fin 3 → V) : Prop where
  pair : ∀ i, omega (u i) (v i) = 1
  uu : ∀ i j, i ≠ j → omega (u i) (u j) = 0
  uv : ∀ i j, i ≠ j → omega (u i) (v j) = 0
  vu : ∀ i j, i ≠ j → omega (v i) (u j) = 0
  vv : ∀ i j, i ≠ j → omega (v i) (v j) = 0

theorem exists_four_step_pair
    (omega : BilinForm (K := K) (V := V)) (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (x v y f : V) (hxv : omega x v = 1) (hyf : omega y f = 1) :
    ∃ word : List (Step (K := K) (V := V)), word.length = 4 ∧
      wordMap omega word x = y ∧ wordMap omega word v = f := by
  have hx : x ≠ 0 := by intro h; subst x; simpa using hxv
  have hy : y ≠ 0 := by intro h; subst y; simpa using hyf
  obtain ⟨z, hzx, hyz⟩ := exists_common_detour omega hleft hright x y hx hy
  let word := fourStepPairWord omega halt x z y v f hzx hyz
  exact ⟨word, by simp [word, fourStepPairWord],
    fourStepPairWord_source omega halt x z y v f hzx hyz hxv hyf,
    fourStepPairWord_partner omega halt x z y v f hzx hyz hxv hyf⟩

/-! Three explicit four-step blocks cover two ordered hyperbolic triples.
The later blocks are constructed in the complements of the pairs already
aligned, so the concatenated word has exactly twelve slots. -/
theorem exists_fixed_twelve_triple_alignment
    (omega : BilinForm (K := K) (V := V)) (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (u v e f : Fin 3 → V) (hsrc : HyperbolicTriple omega u v)
    (htgt : HyperbolicTriple omega e f) :
    ∃ word : List (Step (K := K) (V := V)), word.length = 12 ∧
      (∀ i, wordMap omega word (u i) = e i) ∧
      (∀ i, wordMap omega word (v i) = f i) := by
  obtain ⟨w0, hw0len, hw0u, hw0v⟩ := exists_four_step_pair omega halt hleft hright
    (u 0) (v 0) (e 0) (f 0) (hsrc.pair 0) (htgt.pair 0)
  let u1 := wordMap omega w0 (u 1)
  let v1 := wordMap omega w0 (v 1)
  have hu1v1 : omega u1 v1 = 1 := by
    rw [wordMap_preserves omega halt w0, hsrc.pair]
  have he0u1 : omega (e 0) u1 = 0 := by
    rw [← hw0u, wordMap_preserves omega halt w0]
    exact hsrc.uu 0 1 (by decide)
  have hf0u1 : omega (f 0) u1 = 0 := by
    rw [← hw0v, wordMap_preserves omega halt w0]
    exact hsrc.vu 0 1 (by decide)
  have he0v1 : omega (e 0) v1 = 0 := by
    rw [← hw0u, wordMap_preserves omega halt w0]
    exact hsrc.uv 0 1 (by decide)
  have hf0v1 : omega (f 0) v1 = 0 := by
    rw [← hw0v, wordMap_preserves omega halt w0]
    exact hsrc.vv 0 1 (by decide)
  obtain ⟨w1, hw1len, hw1u, hw1v, hw1e0, hw1f0⟩ :=
    exists_four_step_fixing_one_pair omega halt hleft hright
      (e 0) (f 0) u1 v1 (e 1) (f 1) (htgt.pair 0) hu1v1 (htgt.pair 1)
      he0u1 hf0u1 he0v1 hf0v1
      (htgt.uu 1 0 (by decide)) (htgt.uv 1 0 (by decide))
      (htgt.vu 1 0 (by decide)) (htgt.vv 1 0 (by decide))
  let w10 := w1 ++ w0
  let u2 := wordMap omega w10 (u 2)
  let v2 := wordMap omega w10 (v 2)
  have hw10u0 : wordMap omega w10 (u 0) = e 0 := by
    dsimp only [w10]
    rw [wordMap_append, LinearMap.comp_apply, hw0u, hw1e0]
  have hw10v0 : wordMap omega w10 (v 0) = f 0 := by
    dsimp only [w10]
    rw [wordMap_append, LinearMap.comp_apply, hw0v, hw1f0]
  have hw10u1 : wordMap omega w10 (u 1) = e 1 := by
    dsimp only [w10]
    rw [wordMap_append, LinearMap.comp_apply]
    exact hw1u
  have hw10v1 : wordMap omega w10 (v 1) = f 1 := by
    dsimp only [w10]
    rw [wordMap_append, LinearMap.comp_apply]
    exact hw1v
  have hu2v2 : omega u2 v2 = 1 := by
    rw [wordMap_preserves omega halt w10, hsrc.pair]
  have mapped_u (i : Fin 3) (hi : i ≠ 2) :
      wordMap omega w10 (u i) = e i := by
    fin_cases i
    · exact hw10u0
    · exact hw10u1
    · exact False.elim (hi rfl)
  have mapped_v (i : Fin 3) (hi : i ≠ 2) :
      wordMap omega w10 (v i) = f i := by
    fin_cases i
    · exact hw10v0
    · exact hw10v1
    · exact False.elim (hi rfl)
  have prev_u (i : Fin 3) (hi : i ≠ 2) :
      omega (e i) u2 = 0 ∧ omega (f i) u2 = 0 ∧
      omega (e i) v2 = 0 ∧ omega (f i) v2 = 0 := by
    rw [← mapped_u i hi, ← mapped_v i hi]
    exact ⟨(wordMap_preserves omega halt w10 (u i) (u 2)).trans
        (hsrc.uu i 2 hi),
      (wordMap_preserves omega halt w10 (v i) (u 2)).trans
        (hsrc.vu i 2 hi),
      (wordMap_preserves omega halt w10 (u i) (v 2)).trans
        (hsrc.uv i 2 hi),
      (wordMap_preserves omega halt w10 (v i) (v 2)).trans
        (hsrc.vv i 2 hi)⟩
  obtain ⟨w2, hw2len, hw2u, hw2v, hw2e0, hw2f0, hw2e1, hw2f1⟩ :=
    exists_four_step_fixing_two_pairs omega halt hleft hright
      (e 0) (f 0) (e 1) (f 1) u2 v2 (e 2) (f 2)
      (htgt.pair 0) (htgt.pair 1) hu2v2 (htgt.pair 2)
      (htgt.uu 1 0 (by decide)) (htgt.vu 1 0 (by decide))
      (htgt.uv 1 0 (by decide)) (htgt.vv 1 0 (by decide))
      (prev_u 0 (by decide)).1 (prev_u 0 (by decide)).2.1
      (prev_u 1 (by decide)).1 (prev_u 1 (by decide)).2.1
      (prev_u 0 (by decide)).2.2.1 (prev_u 0 (by decide)).2.2.2
      (prev_u 1 (by decide)).2.2.1 (prev_u 1 (by decide)).2.2.2
      (htgt.uu 2 0 (by decide)) (htgt.uv 2 0 (by decide))
      (htgt.uu 2 1 (by decide)) (htgt.uv 2 1 (by decide))
      (htgt.vu 2 0 (by decide)) (htgt.vv 2 0 (by decide))
      (htgt.vu 2 1 (by decide)) (htgt.vv 2 1 (by decide))
  refine ⟨w2 ++ w10, by simp [w10, hw0len, hw1len, hw2len], ?_, ?_⟩
  · intro i
    fin_cases i
    · change wordMap omega (w2 ++ w10) (u (0 : Fin 3)) = e 0
      rw [wordMap_append, LinearMap.comp_apply, hw10u0, hw2e0]
    · change wordMap omega (w2 ++ w10) (u (1 : Fin 3)) = e 1
      rw [wordMap_append, LinearMap.comp_apply, hw10u1, hw2e1]
    · change wordMap omega (w2 ++ w10) (u (2 : Fin 3)) = e 2
      rw [wordMap_append, LinearMap.comp_apply]
      exact hw2u
  · intro i
    fin_cases i
    · change wordMap omega (w2 ++ w10) (v (0 : Fin 3)) = f 0
      rw [wordMap_append, LinearMap.comp_apply, hw10v0, hw2f0]
    · change wordMap omega (w2 ++ w10) (v (1 : Fin 3)) = f 1
      rw [wordMap_append, LinearMap.comp_apply, hw10v1, hw2f1]
    · change wordMap omega (w2 ++ w10) (v (2 : Fin 3)) = f 2
      rw [wordMap_append, LinearMap.comp_apply]
      exact hw2v

end AlbertLean.Generic.SymplecticTransvection
