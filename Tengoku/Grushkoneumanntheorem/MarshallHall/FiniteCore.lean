import Tengoku.Grushkoneumanntheorem.MarshallHall.PartialAction
import Tengoku.Seed.GroupTheory.FreeGroup.Reduce

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Function

noncomputable section

namespace MarshallHall

universe u

variable {α : Type u}
variable [DecidableEq α]

/-!
## Finite word states

When a word is read by a left action, its tail is applied first.  The finite
state set therefore records suffix products.  This is the same finite core
that appears in the usual folded covering-graph proof, but expressed directly
in the free group.
-/

def signedLetter (x : α × Bool) : FreeGroup α :=
  if x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹

def wordValue : List (α × Bool) → FreeGroup α
  | [] => 1
  | x :: w => signedLetter x * wordValue w

def actionStates : List (α × Bool) → List (FreeGroup α)
  | [] => [1]
  | x :: w => actionStates w ++ [signedLetter x * wordValue w]

def allActionStates : List (α × Bool) → Finset (FreeGroup α)
  | [] => (actionStates []).toFinset
  | x :: w => allActionStates w ∪ (actionStates (x :: w)).toFinset

/--
@isnad1 id=eq.0h1v.s4.c23323fe2445 from=translated src=- shape=5efb74ab vocab=630330a7
-/
@[simp]
theorem wordValue_nil : wordValue ([] : List (α × Bool)) = 1 := rfl

/--
@isnad1 id=eq.0h3v.s5.d6777af642b0 from=translated src=- shape=2ffbeb08 vocab=734aab65
-/
@[simp]
theorem wordValue_cons (x : α × Bool) (w : List (α × Bool)) :
    wordValue (x :: w) = signedLetter x * wordValue w := rfl

/--
@isnad1 id=eq.0h1v.s4.cad9684347b2 from=translated src=- shape=753e510f vocab=2de3ed30
-/
@[simp]
theorem actionStates_nil : actionStates ([] : List (α × Bool)) = [1] := rfl

/--
@isnad1 id=eq.0h3v.s6.94984a78eb5c from=translated src=- shape=1514a746 vocab=1ea9288f
-/
@[simp]
theorem actionStates_cons (x : α × Bool) (w : List (α × Bool)) :
    actionStates (x :: w) = actionStates w ++ [signedLetter x * wordValue w] := rfl

/--
@isnad1 id=eq.0h2v.s4.b26dfba64162 from=translated src=- shape=b7575917 vocab=48efbfbb
-/
@[simp]
theorem wordValue_eq_freeGroup_mk (w : List (α × Bool)) :
    wordValue w = FreeGroup.mk w := by
  induction w with
  | nil => simp [wordValue, FreeGroup.one_eq_mk]
  | cons x w ih =>
      calc
        wordValue (x :: w) = signedLetter x * wordValue w := rfl
        _ = FreeGroup.mk [x] * FreeGroup.mk w := by
          rw [ih]
          congr 1
          cases x with
          | mk a b =>
              cases b <;> simp [signedLetter, FreeGroup.of, FreeGroup.invRev]
        _ = FreeGroup.mk ([x] ++ w) := FreeGroup.mul_mk
        _ = FreeGroup.mk (x :: w) := rfl

/--
@isnad1 id=mem.0h2v.s4.2bf230a174ef from=translated src=- shape=ba98f7c7 vocab=fe26a560
-/
theorem wordValue_mem_actionStates (w : List (α × Bool)) :
    wordValue w ∈ actionStates w := by
  induction w with
  | nil => simp [actionStates, FreeGroup.one_eq_mk]
  | cons x w ih =>
      simp only [actionStates_cons, List.mem_append, List.mem_singleton]
      exact Or.inr rfl

/--
@isnad1 id=mem.0h2v.s4.cd1f98c89ba6 from=translated src=- shape=e60a0cd5 vocab=6f8fba6e
-/
theorem one_mem_actionStates (w : List (α × Bool)) :
    (1 : FreeGroup α) ∈ actionStates w := by
  induction w with
  | nil => simp [actionStates]
  | cons x w ih =>
      simp only [actionStates_cons, List.mem_append, List.mem_singleton]
      exact Or.inl ih

/--
@isnad1 id=mem.1h3v.s5.044cdb94ec28 from=translated src=- shape=fcd0f5f7 vocab=d602d75e
-/
theorem actionStates_subset_allActionStates (w : List (α × Bool)) :
    ∀ x ∈ actionStates w, x ∈ allActionStates w := by
  induction w with
  | nil =>
      intro x hx
      simpa [allActionStates] using hx
  | cons y w ih =>
      intro x hx
      simp only [actionStates_cons, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact Finset.mem_union_left _ (ih x hx)
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (by
          simp only [actionStates_cons, List.mem_append, List.mem_singleton]
          exact Or.inr hx))

/--
@isnad1 id=mem.0h2v.s5.7a0fa60edc12 from=translated src=- shape=58719945 vocab=c6b4cbbd
-/
theorem one_mem_allActionStates (w : List (α × Bool)) :
    (1 : FreeGroup α) ∈ allActionStates w := by
  exact actionStates_subset_allActionStates w 1 (one_mem_actionStates w)

/--
@isnad1 id=mem.2h4v.s6.4ae89f010c90 from=translated src=- shape=114602ff vocab=76848da3
-/
theorem allActionStates_tail_mem (w u : List (α × Bool))
    (hu : u ∈ List.tails w) :
    ∀ x ∈ actionStates u, x ∈ allActionStates w := by
  induction w with
  | nil =>
      simp only [List.tails, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst u
      exact actionStates_subset_allActionStates []
  | cons y w ih =>
      simp only [List.tails, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact actionStates_subset_allActionStates (y :: w)
      · exact fun x hx => by
          exact Finset.mem_union_left _ (ih hu x hx)

/-!
The recursive version above is intentionally kept local to the finite-core
construction.  The following finite union is the set of all suffix states of
the finitely many words under consideration.
-/

def corePoints [DecidableEq (FreeGroup α)] (S : Finset (FreeGroup α)) (g : FreeGroup α) :
    Finset (FreeGroup α) :=
  S.biUnion (fun s => (allActionStates s.toWord)) ∪ allActionStates g.toWord

/--
@isnad1 id=mem.2h5v.s6.d317aabf2685 from=translated src=- shape=486c23fc vocab=298aedad
-/
theorem mem_corePoints_of_generator [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g s : FreeGroup α}
    (hs : s ∈ S) (x : FreeGroup α) (hx : x ∈ allActionStates s.toWord) :
    x ∈ corePoints S g := by
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨s, hs, hx⟩)

/--
@isnad1 id=mem.1h4v.s6.57c779c2c9c0 from=translated src=- shape=21b0ce74 vocab=298aedad
-/
theorem mem_corePoints_of_separating [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g x : FreeGroup α}
    (hx : x ∈ allActionStates g.toWord) : x ∈ corePoints S g := by
  exact Finset.mem_union_right _ hx

/--
@isnad1 id=mem.3h6v.s6.c963f38dd9ae from=translated src=- shape=d78ca4dd vocab=f9a33ddb
-/
theorem mem_corePoints_of_generator_suffix [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g s : FreeGroup α} {u : List (α × Bool)}
    (hs : s ∈ S) (hu : u ∈ List.tails s.toWord)
    {x : FreeGroup α} (hx : x ∈ actionStates u) : x ∈ corePoints S g := by
  exact mem_corePoints_of_generator hs x
    (allActionStates_tail_mem s.toWord u hu x hx)

/--
@isnad1 id=mem.2h5v.s6.eecfb1ffc29b from=translated src=- shape=58f2f05c vocab=f9a33ddb
-/
theorem mem_corePoints_of_separating_suffix [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g : FreeGroup α} {u : List (α × Bool)}
    (hu : u ∈ List.tails g.toWord) {x : FreeGroup α}
    (hx : x ∈ actionStates u) : x ∈ corePoints S g := by
  exact mem_corePoints_of_separating
    (allActionStates_tail_mem g.toWord u hu x hx)

/--
@isnad1 id=ex.1h3v.s6.fd4f12614d96 from=translated src=- shape=42863039 vocab=59924012
-/
theorem exists_wordValue_of_mem_actionStates (u : List (α × Bool))
    {x : FreeGroup α} (hx : x ∈ actionStates u) :
    ∃ v ∈ List.tails u, x = wordValue v := by
  induction u with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [List.tails]
      · simpa [actionStates, wordValue] using hx
  | cons y u ih =>
      simp only [actionStates_cons, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · obtain ⟨v, hv, hvx⟩ := ih hx
        refine ⟨v, ?_, hvx⟩
        simp only [List.tails, List.mem_cons]
        exact Or.inr hv
      · refine ⟨y :: u, ?_, ?_⟩
        · simp [List.tails]
        · simpa [wordValue] using hx

/--
@isnad1 id=ex.1h3v.s6.02645ebb5204 from=translated src=- shape=1637049a vocab=ef525ddb
-/
theorem exists_wordValue_of_mem_allActionStates (u : List (α × Bool))
    {x : FreeGroup α} (hx : x ∈ allActionStates u) :
    ∃ v ∈ List.tails u, x = wordValue v := by
  induction u with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [List.tails]
      · simpa [allActionStates, actionStates, wordValue] using hx
  | cons y u ih =>
      simp only [allActionStates, Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨v, hv, hvx⟩ := ih hx
        refine ⟨v, ?_, hvx⟩
        simp only [List.tails, List.mem_cons]
        exact Or.inr hv
      · obtain ⟨v, hv, hvx⟩ :=
          exists_wordValue_of_mem_actionStates (y :: u) (List.mem_toFinset.mp hx)
        exact ⟨v, hv, hvx⟩

end MarshallHall
