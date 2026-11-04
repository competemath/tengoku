import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticComplementFixing
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticComplementDetour

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_four_step_fixing_one_pair` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_four_step_fixing_two_pairs` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/--
@isnad1 id=ex.14h9v.s12.dbc934710492 from=translated src=- shape=5a8473aa vocab=c3f0f2ed
-/
theorem exists_four_step_fixing_one_pair
    (omega : BilinForm (K := K) (V := V)) (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (e0 f0 x v y f : V) (he0f0 : omega e0 f0 = 1)
    (hxv : omega x v = 1) (hyf : omega y f = 1)
    (he0x : omega e0 x = 0) (hf0x : omega f0 x = 0)
    (he0v : omega e0 v = 0) (hf0v : omega f0 v = 0)
    (hye0 : omega y e0 = 0) (hyf0 : omega y f0 = 0)
    (hfe0 : omega f e0 = 0) (hff0 : omega f f0 = 0) :
    ∃ word : List (Step (K := K) (V := V)), word.length = 4 ∧
      wordMap omega word x = y ∧ wordMap omega word v = f ∧
      wordMap omega word e0 = e0 ∧ wordMap omega word f0 = f0 := by
  have hx : x ≠ 0 := by intro h; subst x; simpa using hxv
  have hy : y ≠ 0 := by intro h; subst y; simpa using hyf
  obtain ⟨z, hzx, hyz, hze0, hzf0⟩ := exists_detour_orthogonal_one_pair
    omega halt hleft hright e0 f0 x y he0f0 hx hy he0x hf0x hye0 hyf0
  let word := fourStepPairWord omega halt x z y v f hzx hyz
  refine ⟨word, by simp [word, fourStepPairWord],
    fourStepPairWord_source omega halt x z y v f hzx hyz hxv hyf,
    fourStepPairWord_partner omega halt x z y v f hzx hyz hxv hyf, ?_, ?_⟩
  · apply fourStepPairWord_fixes omega halt x z y v f e0 hzx hyz
    · exact (skew_of_alternating omega halt x e0).trans (by rw [he0x]; simp)
    · exact hze0
    · exact hye0
    · exact (skew_of_alternating omega halt v e0).trans (by rw [he0v]; simp)
    · exact hfe0
  · apply fourStepPairWord_fixes omega halt x z y v f f0 hzx hyz
    · exact (skew_of_alternating omega halt x f0).trans (by rw [hf0x]; simp)
    · exact hzf0
    · exact hyf0
    · exact (skew_of_alternating omega halt v f0).trans (by rw [hf0v]; simp)
    · exact hff0

/--
@isnad1 id=ex.27h11v.s13.17285237c8f5 from=translated src=- shape=bc59abb4 vocab=c3f0f2ed
-/
theorem exists_four_step_fixing_two_pairs
    (omega : BilinForm (K := K) (V := V)) (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (e0 f0 e1 f1 x v y f : V)
    (he0f0 : omega e0 f0 = 1) (he1f1 : omega e1 f1 = 1)
    (hxv : omega x v = 1) (hyf : omega y f = 1)
    (he1e0 : omega e1 e0 = 0) (hf1e0 : omega f1 e0 = 0)
    (he1f0 : omega e1 f0 = 0) (hf1f0 : omega f1 f0 = 0)
    (he0x : omega e0 x = 0) (hf0x : omega f0 x = 0)
    (he1x : omega e1 x = 0) (hf1x : omega f1 x = 0)
    (he0v : omega e0 v = 0) (hf0v : omega f0 v = 0)
    (he1v : omega e1 v = 0) (hf1v : omega f1 v = 0)
    (hye0 : omega y e0 = 0) (hyf0 : omega y f0 = 0)
    (hye1 : omega y e1 = 0) (hyf1 : omega y f1 = 0)
    (hfe0 : omega f e0 = 0) (hff0 : omega f f0 = 0)
    (hfe1 : omega f e1 = 0) (hff1 : omega f f1 = 0) :
    ∃ word : List (Step (K := K) (V := V)), word.length = 4 ∧
      wordMap omega word x = y ∧ wordMap omega word v = f ∧
      wordMap omega word e0 = e0 ∧ wordMap omega word f0 = f0 ∧
      wordMap omega word e1 = e1 ∧ wordMap omega word f1 = f1 := by
  have hx : x ≠ 0 := by intro h; subst x; simpa using hxv
  have hy : y ≠ 0 := by intro h; subst y; simpa using hyf
  obtain ⟨z, hzx, hyz, hze0, hzf0, hze1, hzf1⟩ :=
    exists_detour_orthogonal_two_pairs omega halt hleft hright
      e0 f0 e1 f1 x y he0f0 he1f1 hx hy he1e0 hf1e0 he1f0 hf1f0
      he0x hf0x he1x hf1x hye0 hyf0 hye1 hyf1
  let word := fourStepPairWord omega halt x z y v f hzx hyz
  refine ⟨word, by simp [word, fourStepPairWord],
    fourStepPairWord_source omega halt x z y v f hzx hyz hxv hyf,
    fourStepPairWord_partner omega halt x z y v f hzx hyz hxv hyf,
    ?_, ?_, ?_, ?_⟩
  · exact fourStepPairWord_fixes omega halt x z y v f e0 hzx hyz
      ((skew_of_alternating omega halt x e0).trans (by rw [he0x]; simp))
      hze0 hye0
      ((skew_of_alternating omega halt v e0).trans (by rw [he0v]; simp)) hfe0
  · exact fourStepPairWord_fixes omega halt x z y v f f0 hzx hyz
      ((skew_of_alternating omega halt x f0).trans (by rw [hf0x]; simp))
      hzf0 hyf0
      ((skew_of_alternating omega halt v f0).trans (by rw [hf0v]; simp)) hff0
  · exact fourStepPairWord_fixes omega halt x z y v f e1 hzx hyz
      ((skew_of_alternating omega halt x e1).trans (by rw [he1x]; simp))
      hze1 hye1
      ((skew_of_alternating omega halt v e1).trans (by rw [he1v]; simp)) hfe1
  · exact fourStepPairWord_fixes omega halt x z y v f f1 hzx hyz
      ((skew_of_alternating omega halt x f1).trans (by rw [hf1x]; simp))
      hzf1 hyf1
      ((skew_of_alternating omega halt v f1).trans (by rw [hf1v]; simp)) hff1

end AlbertLean.Generic.SymplecticTransvection
