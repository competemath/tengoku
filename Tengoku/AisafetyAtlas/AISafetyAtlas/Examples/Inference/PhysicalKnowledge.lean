module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.PhysicalKnowledge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Physical knowledge — an executable Wolpert 2018 certificate

The observer chooses which value of a Boolean target it is testing. Its
conclusion says whether the target equals that chosen value. Over the worlds in
which the target is true, the resulting selector satisfies every clause of
Wolpert's Definition 11 for knowing that the target is true.

This example is deliberately stronger than a bare weak-inference witness: both
the positive selected block and the alternative block meet `W`, and their
conclusions have the signs Definition 11 requires. It also exercises Lemma 17
and Corollary 19 on a non-singleton universe.
-/

namespace AISafetyAtlas.Examples.Inference.PhysicalKnowledge

open AISafetyAtlas.Inference

/-- The fact to be known is the world's second bit.-/
public abbrev target : Bool × Bool → Bool := Prod.snd

/-- The device chooses a candidate value in its first bit and reports whether
that candidate agrees with the target in the second bit.-/
public abbrev observer : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun u => decide (u.2 = u.1)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨(false, true), rfl⟩
    · exact ⟨(false, false), rfl⟩

/-- The context in which the target is true.-/
public abbrev trueWorlds : Set (Bool × Bool) := {u | target u = true}

/-- Select the setup block whose candidate is the realized target value.-/
private def selectedBlock (g : ImageValue target) : SetupBlock observer :=
  ⟨g.1, ⟨(g.1, g.1), rfl⟩⟩

/-- All three clauses of Definition 11 hold for this concrete observer.-/
public def knowsTrueWitness :
    PhysicalKnowledgeWitness observer target true trueWorlds := by
  refine {
    target_realized := ⟨(false, true), rfl⟩
    selector := selectedBlock
    correct := ?_
    yes_nonempty := ?_
    yes_on := ?_
    no_nonempty := ?_
    no_on := ?_ }
  · intro g u hu
    cases u with
    | mk candidate actual =>
      simp only [observer, selectedBlock] at hu
      subst candidate
      cases actual <;> cases g.1 <;> decide
  · exact ⟨(true, true), rfl, rfl⟩
  · intro u huW huX
    cases u with
    | mk candidate actual =>
      simp only [trueWorlds, target, Set.mem_ofPred_eq] at huW
      simp only [observer, selectedBlock] at huX
      subst actual
      subst candidate
      rfl
  · intro g hg
    have hfalse : g.1 = false := by
      cases h : g.1
      · rfl
      · exact (hg h).elim
    exact ⟨(false, true), rfl, by simp [selectedBlock, hfalse]⟩
  · intro g hg u huW huX
    have hfalse : g.1 = false := by
      cases h : g.1
      · rfl
      · exact (hg h).elim
    cases u with
    | mk candidate actual =>
      simp only [trueWorlds, target, Set.mem_ofPred_eq] at huW
      simp only [observer, selectedBlock] at huX
      subst actual
      rw [hfalse] at huX
      subst candidate
      rfl

end AISafetyAtlas.Examples.Inference.PhysicalKnowledge
