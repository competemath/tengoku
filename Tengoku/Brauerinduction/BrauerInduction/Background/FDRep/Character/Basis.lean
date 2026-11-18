import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.SimpleDecomposition
import Tengoku.Brauerinduction.BrauerInduction.Background.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace FDRep

variable {k : Type u} {G : Type u}
variable [Field k] [Group G]

/--
The character of any finite-dimensional representation lies in the `ℤ`-span of
the characters of simple representations.

This is proved by decomposing the representation as a finite biproduct of simple
representations and using additivity of characters over finite biproducts.
@isnad1 id=mem.0h3v.s9.39e3f39af040 from=translated src=- shape=53f0138a vocab=9664a26c
-/
theorem character_mem_span_simple_characters
    [Finite G] [CharZero k] [IsAlgClosed k]
    (V : FDRep k G) :
    V.character ∈
      Submodule.span ℤ
        { χ : G → k |
            ∃ (S : FDRep k G)
              (_ : CategoryTheory.Simple S),
              χ = S.character } := by

  haveI : NeZero (Nat.card G : k) := ⟨One.natCast_natCard_ne_zero_of_finite G k⟩

  obtain ⟨ι, f, hι, hsimple, ⟨e⟩⟩ :=
    FDRep.exists_simple_decomposition V

  letI : Fintype ι := hι

  rw [FDRep.char_eq_of_iso e]
  rw [FDRep.char_biproduct]

  exact Submodule.sum_mem _ fun i _ =>
    Submodule.subset_span
      ⟨f i, hsimple i, rfl⟩

/--
A family of finite-dimensional representations containing exactly one
representative of every simple isomorphism class.-/
structure IsCompleteSetOfSimples
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    (S : ι → FDRep k G) : Prop where
  is_simple : ∀ i, CategoryTheory.Simple (S i)
  is_distinct : ∀ i j, Nonempty (S i ≅ S j) → i = j
  is_exhaustive :
    ∀ T : FDRep k G,
      CategoryTheory.Simple T → ∃ i, Nonempty (T ≅ S i)

namespace IsCompleteSetOfSimples

/-- Distinct members of a complete set of simples are not isomorphic.
@isnad1 id=isempty.2h6v.s6.78b04b29062b from=translated src=- shape=44fd6a5d vocab=3af242ea
-/
lemma isEmpty_iso_of_ne
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    {S : ι → FDRep k G}
    (hS : FDRep.IsCompleteSetOfSimples S)
    {i j : ι}
    (hij : i ≠ j) :
    IsEmpty (S i ≅ S j) := by
  refine ⟨?_⟩
  intro e
  exact hij (hS.is_distinct i j ⟨e⟩)

/--
For a complete set of simple representatives, two indexed simples are
isomorphic iff their indices are equal.
@isnad1 id=iff.1h6v.s6.585d2ce61988 from=translated src=- shape=363b2c93 vocab=caceec2e
-/
lemma iso_iff_eq
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    {S : ι → FDRep k G}
    (hS : FDRep.IsCompleteSetOfSimples S)
    (i j : ι) :
    Nonempty (S i ≅ S j) ↔ i = j := by
  constructor
  · exact hS.is_distinct i j
  · rintro rfl
    exact ⟨CategoryTheory.Iso.refl (S i)⟩

end IsCompleteSetOfSimples

end FDRep
