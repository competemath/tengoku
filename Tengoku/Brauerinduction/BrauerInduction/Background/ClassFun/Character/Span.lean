import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.SimpleDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spans of irreducible characters

This file proves that characters of finite-dimensional representations are
integer linear combinations of characters of simple representations.

Under the hypothesis that the order of the finite group is nonzero in the
coefficient field, Maschke's theorem decomposes every representation as a
finite biproduct of simple representations. Taking characters gives the
corresponding decomposition into a finite sum of irreducible characters.
Consequently, every virtual character lies in their `ℤ`-linear span.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v

namespace Tengoku.Brauerinduction.ClassFun

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

variable {k : Type u} {G : Type u}
variable [Field k] [Group G]

/--
The character of a finite-dimensional representation is a finite sum of
characters of simple representations.
@isnad1 id=ex.0h3v.s8.698a93667175 from=translated src=- shape=aa8ddd44 vocab=95a07763
-/
theorem char_eq_sum_simples
    [Finite G] [NeZero (Nat.card G : k)]
    (V : FDRep k G) :
    ∃ (ι : Type) (S : ι → FDRep k G)
      (_ : Fintype ι) (_ : ∀ i, Simple (S i)),
      ClassFun.character V =
        ∑ i : ι, ClassFun.character (S i) := by

  obtain ⟨ι, S, hι, hSimple, ⟨e⟩⟩ :=
    FDRep.exists_simple_decomposition V

  letI : Fintype ι := hι

  refine ⟨ι, S, inferInstance, hSimple, ?_⟩

  calc
    ClassFun.character V
        = ClassFun.character (Limits.biproduct S) :=
          ClassFun.char_eq_of_iso e
    _ = ∑ i : ι, ClassFun.character (S i) :=
          ClassFun.char_biproduct S

/--
The set of characters of simple finite-dimensional representations of `G`
over `k`.-/
def irreducibleCharacterSet
    (k : Type u) [Field k]
    (G : Type v) [Group G] :
    Set (ClassFun k G) :=
  { ψ : ClassFun k G |
    ∃ (S : FDRep k G)
      (_ : Simple S),
      ψ = ClassFun.character S }

/--
The character of a finite-dimensional representation belongs to the
`ℤ`-linear span of the characters of simple representations.
@isnad1 id=mem.0h3v.s7.02b836ddda9b from=translated src=- shape=0aa4f9b5 vocab=19b494e3
-/
theorem character_mem_span_irreducibles
    [Finite G] [NeZero (Nat.card G : k)]
    (V : FDRep k G) :
    ClassFun.character V ∈
      Submodule.span ℤ
        (irreducibleCharacterSet k G) := by
  obtain ⟨ι, S, hι, hSimple, hchar⟩ :=
    char_eq_sum_simples (k := k) (G := G) V
  letI : Fintype ι := hι
  rw [hchar]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.subset_span
      ⟨S i, hSimple i, rfl⟩

/--
@isnad1 id=mem.1h3v.s7.afc77d547ae0 from=translated src=- shape=c7d88fa0 vocab=19b494e3
-/
theorem character_mem_span_irreducibles_of_eq
    [Finite G] [NeZero (Nat.card G : k)]
    (φ : ClassFun k G)
    (h_rep : ∃ V : FDRep k G,
      φ = ClassFun.character V) :
    φ ∈
      Submodule.span ℤ
        (irreducibleCharacterSet k G) := by
  obtain ⟨V, rfl⟩ := h_rep
  exact character_mem_span_irreducibles V

/--
The virtual character group of `G`: the `ℤ`-span of irreducible characters
inside the group of `k`-valued class functions.-/
def virtualCharacterSubmodule
    (k : Type u) [Field k]
    (G : Type v) [Group G] :
    Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (ClassFun.irreducibleCharacterSet k G)

end Tengoku.Brauerinduction.ClassFun
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
