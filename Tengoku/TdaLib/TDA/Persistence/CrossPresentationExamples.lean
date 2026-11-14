import Tengoku.TdaLib.TDA.Persistence.CrossPresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cross-presentation examples

The positive-parameter example has a genuine nonzero relation: one generator
born at zero is killed at grade two. The opposite presentation delays both
that generator and that relation by one.
-/

set_option autoImplicit false

namespace TDA.Persistence.GradedFree.CrossPresentationExamples

open CategoryTheory
open scoped TDA.Persistence NNReal

def oneGrade (t : ℝ) : GradedGenerators (Fin 1 → ℝ) where
  Carrier := Unit
  grade _ _ := t

def noGrades : GradedGenerators (Fin 1 → ℝ) where
  Carrier := Empty
  grade := Empty.elim

private noncomputable def deathVector :
    (module (R := ℤ) (crossLeft 1 (oneGrade 0) noGrades)).obj ((oneGrade 2).grade ()) :=
  generator (crossLeft 1 (oneGrade 0) noGrades) (Sum.inl ()) (by
    intro i
    change (0 : ℝ) ≤ 2
    norm_num)

/-- Two finite cross-presentations with a nonzero primitive relation.-/
noncomputable def delayedDeath : CrossData (R := ℤ) (n := 1) 1 where
  W₁ := oneGrade 0
  W₂ := noGrades
  Y₁ := oneGrade 2
  Y₂ := noGrades
  r₁ := lift (oneGrade 2) (module (crossLeft 1 (oneGrade 0) noGrades))
    (fun _ => deathVector)
  r₂ := 0

/--
@isnad1 id=and.0h0v.s6.ef95f4156c5e from=translated src=- shape=a9a37909 vocab=d3a3cd58
-/
theorem delayedDeath_finite :
    delayedDeath.leftPresentation.IsFinite ∧ delayedDeath.rightPresentation.IsFinite :=
  delayedDeath.finite ⟨inferInstanceAs (Finite Unit), inferInstanceAs (Finite Empty),
    inferInstanceAs (Finite Unit), inferInstanceAs (Finite Empty)⟩

/--
@isnad1 id=ne.0h0v.s10.4c6e7c9801c4 from=translated src=- shape=d2f12b13 vocab=914fa258
-/
theorem delayedDeath_relation_ne_zero : delayedDeath.r₁ ≠ 0 := by
  intro h
  have hv := congrArg (fun f : module (R := ℤ) (oneGrade 2) ⟶
      module (crossLeft 1 (oneGrade 0) noGrades) =>
    (f.app (fun _ => 2) (birth (oneGrade 2) ())).val (Sum.inl ())) h
  have hb : delayedDeath.r₁.app ((oneGrade 2).grade ()) (birth (oneGrade 2) ()) =
      deathVector := lift_birth (oneGrade 2) _ (fun _ => deathVector) ()
  change (delayedDeath.r₁.app ((oneGrade 2).grade ())
    (birth (oneGrade 2) ())).val (Sum.inl ()) = 0 at hv
  rw [hb] at hv
  change (Finsupp.single (Sum.inl () : Unit ⊕ Empty) (1 : ℤ)) (Sum.inl ()) = 0 at hv
  rw [Finsupp.single_eq_same] at hv
  exact Int.one_ne_zero hv

/--
@isnad1 id=nonempty.0h0v.s6.3a9ffcc57b7a from=translated src=- shape=f50c9747 vocab=f3534ec7
-/
theorem delayedDeath_interleaved :
    Nonempty (CoordinateInterleaving 1 delayedDeath.leftPresentation.presented
      delayedDeath.rightPresentation.presented) :=
  ⟨delayedDeath.quotientInterleaving⟩

/-- Zero-parameter descent works without changing the supplied relation families.
@isnad1 id=nonempty.0h1v.s7.0ab80515e093 from=translated src=- shape=818bc01a vocab=1dc3ceaf
-/
theorem zero_parameter (C : CrossData (R := ℤ) (n := 1) 0) :
    Nonempty (C.leftPresentation.presented ≅ C.rightPresentation.presented) :=
  ⟨C.zeroIso⟩

/-- The construction also includes dimension zero and the zero ring.
@isnad1 id=nonempty.0h2v.s7.7ae4e2dc492a from=translated src=- shape=ec9e1ed9 vocab=89356fd0
-/
theorem zero_ring_zero_dimension (ε : ℝ≥0)
    (C : CrossData (R := ZMod 1) (n := 0) ε) :
    Nonempty (CoordinateInterleaving ε C.leftPresentation.presented
      C.rightPresentation.presented) :=
  ⟨C.quotientInterleaving⟩

end TDA.Persistence.GradedFree.CrossPresentationExamples
