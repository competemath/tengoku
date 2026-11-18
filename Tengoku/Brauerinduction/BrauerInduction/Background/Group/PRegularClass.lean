import Tengoku.Brauerinduction.BrauerInduction.Background.Group.PDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `p`-regular conjugacy classes

This file defines the subtype of conjugacy classes consisting of `p`-regular
elements. It also provides a chosen representative for such a class and proves
that every `p`-regular element lies in a unique `p`-regular conjugacy class.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u
variable {G : Type u} [Group G]
variable (p : ℕ)

namespace ConjClass

/--
A conjugacy class is `p`-regular if its chosen representative is `p`-regular.

This is independent of the chosen representative, since `p`-regularity is
invariant under conjugacy.-/
def isPRegular (C : ConjClasses G) : Prop := IsPRegular p (C.out)

/--
The conjugacy class of an element is `p`-regular iff the element itself is
`p`-regular.
@isnad1 id=iff.0h3v.s4.ff4cfaca70fc from=translated src=- shape=a3698713 vocab=3fa1a3f5
-/
@[simp] lemma mk_isPRegular (p : ℕ) (g : G) :
  ConjClass.isPRegular p ⟦g⟧ ↔ IsPRegular p g :=
by
  unfold ConjClass.isPRegular
  apply IsPRegular.iff_isConj
  have h := Quot.out_eq (⟦g⟧ : ConjClasses G)
  exact ConjClasses.mk_eq_mk_iff_isConj.mp h

end ConjClass

/-- The type of `p`-regular conjugacy classes of `G`.-/
def _root_.Tengoku.Brauerinduction.PRegularClass (G : Type u) [Group G] := { C : ConjClasses G // ConjClass.isPRegular p C }

namespace Tengoku.Brauerinduction.PRegularClass

/-- A chosen representative of a `p`-regular conjugacy class.-/
noncomputable def repr {p : ℕ} (C : PRegularClass p G) : G :=
  C.1.out

/-- The chosen representative of a `p`-regular conjugacy class is `p`-regular.
@isnad1 id=ispregul.0h3v.s4.4e62f8a1902d from=translated src=- shape=21cb1911 vocab=28edcb91
-/
lemma repr_isPRegular {p : ℕ} (C : PRegularClass p G) :
    IsPRegular p (repr C) := by
  dsimp [repr, PRegularClass, ConjClass.isPRegular] at C
  exact C.2

/--
@isnad1 id=eq.1h4v.s6.9dd0eb1ec8e9 from=translated src=- shape=b89c1613 vocab=32f2a412
-/
@[ext] lemma ext {C₁ C₂ : PRegularClass p G} (h : C₁.val = C₂.val) : C₁ = C₂ :=
  Subtype.ext h

/--
Every `p`-regular element belongs to a unique `p`-regular conjugacy class.

The class is characterized by the condition that its chosen representative is
conjugate to the given element.
@isnad1 id=existsun.1h3v.s5.e7bd035e090f from=translated src=- shape=0c9f4f29 vocab=62495172
-/
lemma unique_of_isPRegular
  (g : G) (hg : IsPRegular p g) :
  ∃! C : PRegularClass p G, IsConj (repr C) g := by
  let C0 : PRegularClass p G :=
    ⟨ConjClasses.mk g, by
      simpa [ConjClasses.quotient_mk_eq_mk] using
        (ConjClass.mk_isPRegular p g).2 hg⟩
  refine ⟨C0, ?_, ?_⟩
  · have hm : ConjClasses.mk ((ConjClasses.mk g).out) = ConjClasses.mk g := by
      exact Quotient.out_eq (ConjClasses.mk g)

    simpa [C0, repr] using (ConjClasses.mk_eq_mk_iff_isConj).1 hm
  · intro C hC
    apply ext p (G := G)
    have hmk : ConjClasses.mk (repr C) = ConjClasses.mk g :=
      (ConjClasses.mk_eq_mk_iff_isConj).2 (by
        simpa using hC)
    have hmk_out :
        ConjClasses.mk (repr C) = C.1 := by
      change ConjClasses.mk C.1.out = C.1
      exact Quotient.out_eq C.1
    have : C.1 = ConjClasses.mk g := by
      calc
        C.1 = ConjClasses.mk (repr C) := by
                symm; exact hmk_out
        _   = ConjClasses.mk g := hmk
    simpa [C0] using this

noncomputable instance [Finite G] : Fintype (PRegularClass p G) := by
  letI : Finite (ConjClasses G) := Quotient.finite (IsConj.setoid G)
  letI : Finite (PRegularClass p G) := Subtype.finite
  exact Fintype.ofFinite (PRegularClass p G)

end Tengoku.Brauerinduction.PRegularClass
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
