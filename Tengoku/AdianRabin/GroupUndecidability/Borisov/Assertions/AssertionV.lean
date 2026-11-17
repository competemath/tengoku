import Tengoku.AdianRabin.GroupUndecidability.Borisov.Assertions.AssertionIV

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borisov's Assertion V

This file proves the support statement called Assertion V in Borisov's
normal-form argument.  A reduced word in the displayed rank-five basis is
expanded literally in the two stable letters.  Flat Britton normal form then
detects every stable-letter color which occurs in that expansion.
-/

namespace Undecidability
namespace BorisovAssertionV

open BorisovHNNModel
open BorisovIntersections
open BorisovG0HNN
open BorisovG0NormalForm
open BorisovAssertionIV
open BorisovAssertionIVBoundary

noncomputable section

/-! ## Literal color support -/

/--
@isnad1 id=eq.1h3v.s5.468b0f875447 from=translated src=- shape=e2186f69 vocab=bceb75a9
-/
theorem run_color_map (colors : List (Fin 2)) (hne : colors ≠ [])
    (u : ℤˣ) (lastCoeff : BorisovHNNModel.Base) :
    (run colors hne u lastCoeff).map
        MultipleHNNFlat.Syllable.color = colors := by
  unfold run
  rw [List.map_append, List.map_map, List.map_singleton]
  have hdrop : colors.dropLast.map
      (MultipleHNNFlat.Syllable.color ∘ fun color =>
        ({ color := color, sign := u, coeff := 1 } : FlatSyllable)) =
      colors.dropLast := by
    conv_rhs => rw [← List.map_id' colors.dropLast]
    apply List.map_congr_left
    intro color _
    rfl
  rw [hdrop]
  exact List.dropLast_append_getLast hne

/--
@isnad1 id=ex.2h4v.s6.43c4432387be from=translated src=- shape=4a1796c4 vocab=690b5d9c
-/
theorem run_contains_color (colors : List (Fin 2)) (hne : colors ≠ [])
    (u : ℤˣ) (lastCoeff : BorisovHNNModel.Base) {color : Fin 2}
    (hcolor : color ∈ colors) :
    ∃ s ∈ run colors hne u lastCoeff, s.color = color := by
  have hmapped : color ∈
      (run colors hne u lastCoeff).map
        MultipleHNNFlat.Syllable.color := by
    rw [run_color_map]
    exact hcolor
  simpa only [List.mem_map] using hmapped

/--
@isnad1 id=ex.2h4v.s6.aa17fb3a41bb from=translated src=- shape=4d73d597 vocab=51692db4
-/
theorem factorRun_contains_color
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (x : Basis × Bool) (lastCoeff : BorisovHNNModel.Base)
    {color : Fin 2}
    (hcolor : color ∈ factorColors rules x) :
    ∃ s ∈ factorRun rules hne x lastCoeff, s.color = color :=
  run_contains_color _ _ _ _ hcolor

/--
@isnad1 id=ex.3h4v.s6.b6e9d0b773e9 from=translated src=- shape=99ee6e8d vocab=cc9f4a3a
-/
theorem expansionTail_contains_color
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (letters : List (Basis × Bool)) (x : Basis × Bool)
    (hx : x ∈ letters) {color : Fin 2}
    (hcolor : color ∈ factorColors rules x) :
    ∃ s ∈ expansionTail rules hne letters, s.color = color := by
  induction letters with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.mem_cons] at hx
      rw [expansionTail]
      rcases hx with rfl | hx
      · rcases factorRun_contains_color rules hne x
          (suffix x * nextPrefix ys) hcolor with ⟨s, hs, hc⟩
        exact ⟨s, List.mem_append_left _ hs, hc⟩
      · rcases ih hx with ⟨s, hs, hc⟩
        exact ⟨s, List.mem_append_right _ hs, hc⟩

/--
@isnad1 id=ex.3h3v.s6.71dc7c3f10ed from=translated src=- shape=d4b0d4ad vocab=6b99b8fd
-/
theorem expansionTail_contains_of_usesStable
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (hsupport : ∀ i, Thue.ContainsBoth (rules i))
    (w : FreeGroup Basis) (gamma : Fin 2)
    (huses : UsesStable w gamma) :
    ∃ s ∈ expansionTail rules hne w.toWord, s.color = gamma := by
  rcases huses with ⟨⟨q, sign⟩, hletter, hq⟩
  apply expansionTail_contains_color rules hne w.toWord (q, sign) hletter
  cases q with
  | inl beta =>
      change beta = gamma at hq
      subst beta
      cases sign <;> simp [factorColors]
  | inr i =>
      have hgamma : gamma ∈ rules i := by
        fin_cases gamma
        · exact (hsupport i).1
        · exact (hsupport i).2
      cases sign <;> simpa [factorColors] using hgamma

/--
@isnad1 id=ex.1h3v.s5.36f0657a97f8 from=translated src=- shape=515d2a1c vocab=24a56a0c
-/
theorem uExpansion_contains_of_usesStable
    (datum : Thue.StandingDatum) (w : FreeGroup Basis) (gamma : Fin 2)
    (huses : UsesStable w gamma) :
    ∃ s ∈ (uExpansion datum w).toList, s.color = gamma := by
  simpa [uExpansion, expansionWord] using
    expansionTail_contains_of_usesStable datum.F datum.F_nonempty
      datum.F_support w gamma huses

/--
@isnad1 id=ex.1h3v.s5.4a93e3ed2d15 from=translated src=- shape=515d2a1c vocab=d4fb6590
-/
theorem vExpansion_contains_of_usesStable
    (datum : Thue.StandingDatum) (w : FreeGroup Basis) (gamma : Fin 2)
    (huses : UsesStable w gamma) :
    ∃ s ∈ (vExpansion datum w).toList, s.color = gamma := by
  simpa [vExpansion, expansionWord] using
    expansionTail_contains_of_usesStable datum.E datum.E_nonempty
      datum.E_support w gamma huses

private structure ExpansionWitness where
  basis : Basis → G0
  word : FreeGroup Basis → FlatWord
  contains : ∀ w gamma, UsesStable w gamma →
    ∃ s ∈ (word w).toList, s.color = gamma
  eval : ∀ w, MultipleHNNFlat.eval A0 B0 phi0 (word w) =
    toHNN (FreeGroup.lift basis w)

private def uWitness (datum : Thue.StandingDatum) : ExpansionWitness where
  basis := uBasis datum
  word := uExpansion datum
  contains := uExpansion_contains_of_usesStable datum
  eval := uExpansion_eval datum

private def vWitness (datum : Thue.StandingDatum) : ExpansionWitness where
  basis := vBasis datum
  word := vExpansion datum
  contains := vExpansion_contains_of_usesStable datum
  eval := vExpansion_eval datum

/-! ## The base subgroup -/

/--
@isnad1 id=mem.1h1v.s9.22099968b978 from=translated src=- shape=4b45f55f vocab=49be4bb2
-/
theorem toHNN_mem_base_of_mem_DE {x : G0} (hx : x ∈ DE) :
    toHNN x ∈
      MonoidHom.range (MultipleHNN.baseEmbedding A0 B0 phi0) := by
  let H := (MonoidHom.range
    (MultipleHNN.baseEmbedding A0 B0 phi0)).comap toHNN
  have hle : DE ≤ H := by
    unfold DE
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨BorisovHNNModel.d, rfl⟩
    · exact ⟨BorisovHNNModel.e, rfl⟩
  exact hle hx

private theorem not_usesStable_of_mem_DE
    (M : ExpansionWitness) (w : FreeGroup Basis)
    (hmem : FreeGroup.lift M.basis w ∈ DE)
    (gamma : Fin 2) : ¬ UsesStable w gamma := by
  intro huses
  have hnonempty : (M.word w).toList ≠ [] := by
    intro hempty
    rcases M.contains w gamma huses with ⟨s, hs, _⟩
    simp [hempty] at hs
  have hnot := MultipleHNNFlat.eval_not_mem_base A0 B0 phi0
    (M.word w) hnonempty
  apply hnot
  rw [M.eval]
  exact toHNN_mem_base_of_mem_DE hmem

/-! ## The subgroup `J 0` -/

private theorem not_uses_one_of_mem_J_zero
    (M : ExpansionWitness) (w : FreeGroup Basis)
    (hmem : FreeGroup.lift M.basis w ∈ J 0) :
    ¬ UsesStable w 1 := by
  intro huses
  have hcolor := M.contains w 1 huses
  have hnot := MultipleHNNFlat.eval_not_mem_stageOne_of_contains_color_one
    A0 B0 phi0 (M.word w) hcolor
  apply hnot
  rw [M.eval]
  exact toHNN_mem_stageOne_of_mem_J_zero hmem

/-! ## Swapping the two stable letters -/

/-- The endomorphism of the concrete HNN model induced by interchanging the
two symmetric stable generators of the presentation.-/
def swapHNN : MultipleHNN.Extension A0 B0 phi0 →*
    MultipleHNN.Extension A0 B0 phi0 :=
  swappedToHNN.comp fromHNN

/--
@isnad1 id=eq.0h1v.s9.c6a3821fd8ad from=translated src=- shape=d049ef1c vocab=f186cf16
-/
@[simp] theorem swapHNN_toHNN (x : G0) :
    swapHNN (toHNN x) = swappedToHNN x := by
  have h := DFunLike.congr_fun fromHNN_comp_toHNN x
  change fromHNN (toHNN x) = x at h
  change swappedToHNN (fromHNN (toHNN x)) = swappedToHNN x
  rw [h]

/--
@isnad1 id=eq.0h0v.s9.d96611f264af from=translated src=- shape=358714af vocab=3f6d0fc1
-/
@[simp] theorem swapHNN_hnnD : swapHNN hnnD = hnnD := by
  change swappedToHNN (fromHNN hnnD) = hnnD
  rw [fromHNN_hnnD, presentedD_eq_of, swappedToHNN_of]
  rfl

/--
@isnad1 id=eq.0h0v.s9.fd57686c64f7 from=translated src=- shape=358714af vocab=a524e33b
-/
@[simp] theorem swapHNN_hnnE : swapHNN hnnE = hnnE := by
  change swappedToHNN (fromHNN hnnE) = hnnE
  rw [fromHNN_hnnE, presentedE_eq_of, swappedToHNN_of]
  rfl

/--
@isnad1 id=eq.0h0v.s9.e9bef99f205f from=translated src=- shape=358714af vocab=06a37265
-/
@[simp] theorem swapHNN_hnnS1 : swapHNN hnnS1 = hnnS2 := by
  change swappedToHNN (fromHNN hnnS1) = hnnS2
  rw [fromHNN_hnnS1, presentedS1_eq_of, swappedToHNN_of]
  rfl

/--
@isnad1 id=eq.0h0v.s9.2311b1d6e502 from=translated src=- shape=358714af vocab=06a37265
-/
@[simp] theorem swapHNN_hnnS2 : swapHNN hnnS2 = hnnS1 := by
  change swappedToHNN (fromHNN hnnS2) = hnnS1
  rw [fromHNN_hnnS2, presentedS2_eq_of, swappedToHNN_of]
  rfl

private theorem swapHNN_comp_baseToG0HNN :
    swapHNN.comp baseToG0HNN = baseToG0HNN := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i
  · change swapHNN hnnD = hnnD
    exact swapHNN_hnnD
  · change swapHNN hnnE = hnnE
    exact swapHNN_hnnE

/--
@isnad1 id=eq.0h1v.s10.83da69707504 from=translated src=- shape=2eac8beb vocab=05bcadf8
-/
@[simp] theorem swapHNN_baseEmbedding (g : BorisovHNNModel.Base) :
    swapHNN (MultipleHNN.baseEmbedding A0 B0 phi0 g) =
      MultipleHNN.baseEmbedding A0 B0 phi0 g := by
  change swapHNN (baseToG0HNN g) = baseToG0HNN g
  exact DFunLike.congr_fun swapHNN_comp_baseToG0HNN g

def swapColor : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

/--
@isnad1 id=injectiv.0h0v.s3.1edc33602561 from=translated src=- shape=44762807 vocab=8948927a
-/
theorem swapColor_injective : Function.Injective swapColor := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp [swapColor] at h ⊢

/--
@isnad1 id=eq.0h1v.s9.db7e42bafc90 from=translated src=- shape=39d80a64 vocab=d41d389f
-/
@[simp] theorem swapHNN_stableLetter (color : Fin 2) :
    swapHNN (MultipleHNNFlat.stableLetter A0 B0 phi0 color) =
      MultipleHNNFlat.stableLetter A0 B0 phi0 (swapColor color) := by
  fin_cases color
  · exact swapHNN_hnnS1
  · exact swapHNN_hnnS2

def swapSyllable (s : FlatSyllable) : FlatSyllable where
  color := swapColor s.color
  sign := s.sign
  coeff := s.coeff

def swapFlatWord (w : FlatWord) : FlatWord where
  head := w.head
  toList := w.toList.map swapSyllable
  chain := by
    rw [List.isChain_map]
    apply w.chain.imp
    intro a b hab hcolor hmem
    exact hab (swapColor_injective hcolor) hmem

/--
@isnad1 id=eq.0h1v.s9.e6621a67743d from=translated src=- shape=748f5521 vocab=2101e27a
-/
theorem swapFlatWord_eval (w : FlatWord) :
    MultipleHNNFlat.eval A0 B0 phi0 (swapFlatWord w) =
      swapHNN (MultipleHNNFlat.eval A0 B0 phi0 w) := by
  unfold MultipleHNNFlat.eval
  simp only [swapFlatWord]
  rw [map_mul, swapHNN_baseEmbedding, map_list_prod]
  simp only [List.map_map]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, swapSyllable, map_mul, map_zpow,
    swapHNN_stableLetter, swapHNN_baseEmbedding]

/--
@isnad1 id=ex.1h1v.s6.6429b6c11b9b from=translated src=- shape=ada6046c vocab=a927977f
-/
theorem swapFlatWord_contains_one_of_contains_zero (w : FlatWord)
    (hzero : ∃ s ∈ w.toList, s.color = 0) :
    ∃ s ∈ (swapFlatWord w).toList, s.color = 1 := by
  rcases hzero with ⟨s, hs, hcolor⟩
  refine ⟨swapSyllable s, ?_, ?_⟩
  · change swapSyllable s ∈ w.toList.map swapSyllable
    exact List.mem_map.mpr ⟨s, hs, rfl⟩
  · simp [swapSyllable, swapColor, hcolor]

private theorem swappedExpansion_eval (M : ExpansionWitness)
    (w : FreeGroup Basis) :
    MultipleHNNFlat.eval A0 B0 phi0
        (swapFlatWord (M.word w)) =
      swappedToHNN (FreeGroup.lift M.basis w) := by
  rw [swapFlatWord_eval, M.eval, swapHNN_toHNN]

/-! ## The subgroup `J 1` -/

private theorem not_uses_zero_of_mem_J_one
    (M : ExpansionWitness) (w : FreeGroup Basis)
    (hmem : FreeGroup.lift M.basis w ∈ J 1) :
    ¬ UsesStable w 0 := by
  intro huses
  have hzero := M.contains w 0 huses
  have hone := swapFlatWord_contains_one_of_contains_zero
    (M.word w) hzero
  have hnot := MultipleHNNFlat.eval_not_mem_stageOne_of_contains_color_one
    A0 B0 phi0 (swapFlatWord (M.word w)) hone
  apply hnot
  rw [swappedExpansion_eval]
  exact swappedToHNN_mem_stageOne_of_mem_J_one hmem

/-! ## Assertion V -/

private theorem not_uses_of_mem_J
    (M : ExpansionWitness) (w : FreeGroup Basis) (beta gamma : Fin 2)
    (hmem : FreeGroup.lift M.basis w ∈ J beta) (hne : gamma ≠ beta) :
    ¬ UsesStable w gamma := by
  fin_cases beta <;> fin_cases gamma
  · exact (hne rfl).elim
  · exact not_uses_one_of_mem_J_zero M w hmem
  · exact not_uses_zero_of_mem_J_one M w hmem
  · exact (hne rfl).elim

/-- Borisov's Assertion V, for any proof of Assertion IV.  The argument is
independent of the particular proof object supplied for Assertion IV.
@isnad1 id=assertio.1h1v.s3.eb82a4620088 from=translated src=- shape=b3b449db vocab=549d8ddf
-/
theorem assertionV (datum : Thue.StandingDatum) (hIV : AssertionIV datum) :
    AssertionV datum hIV := by
  exact
    { u_mem_J := not_uses_of_mem_J (uWitness datum)
      v_mem_J := not_uses_of_mem_J (vWitness datum)
      u_mem_DE := not_usesStable_of_mem_DE (uWitness datum)
      v_mem_DE := not_usesStable_of_mem_DE (vWitness datum) }

/-- The canonical unconditional package, using the proved Assertion IV.
@isnad1 id=assertio.0h1v.s2.0e7ff2bc6fd1 from=translated src=- shape=220d6ca8 vocab=041b946e
-/
theorem assertionV_canonical (datum : Thue.StandingDatum) :
    AssertionV datum (BorisovAssertionIV.assertionIV datum) :=
  assertionV datum (BorisovAssertionIV.assertionIV datum)

end

end BorisovAssertionV
end Undecidability

/-!
# Borisov's subgroup-intersection lemma

This file packages Borisov's Assertions IV and V into the four subgroup
intersections used in Lemma 3.5 of the paper.
-/

namespace Undecidability
namespace BorisovLemmaFourTwo

open BorisovIntersections

/-- Lemma 3.5 of the paper for the canonical first-stage presentation `G₀`.
@isnad1 id=and.0h1v.s8.8b96d0356306 from=translated src=- shape=00659702 vocab=b4a178bb
-/
theorem lemma4_2 (datum : Thue.StandingDatum) :
    (∀ beta : Fin 2,
      Uc datum ⊓ J beta = stableCyclic beta ∧
      Vc datum ⊓ J beta = stableCyclic beta) ∧
    Uc datum ⊓ DE = ⊥ ∧ Vc datum ⊓ DE = ⊥ :=
  BorisovIntersections.lemma4_2 datum
    (BorisovAssertionIV.assertionIV datum)
    (BorisovAssertionV.assertionV_canonical datum)

end BorisovLemmaFourTwo
end Undecidability
