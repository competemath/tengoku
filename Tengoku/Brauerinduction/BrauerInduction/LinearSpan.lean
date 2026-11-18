import Tengoku.Brauerinduction.BrauerInduction.Span
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Span
import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.Clifford
import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.InducedCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linear-character Brauer span

This file defines the integral span of characters induced from linear
characters of Brauer-elementary subgroups and proves that the Brauer character
span is contained in it.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u

open BigOperators CategoryTheory

namespace BrauerInduction

section BrauerSpanLin

/--
A generator for the linear-character Brauer span: a Brauer-elementary subgroup
together with a linear character of it.-/
structure BrauerLinGen (k : Type u) [CommRing k] (G : Type u) [Group G] where
  protected H : Subgroup G
  protected hElem : IsBrauerElementary H
  protected ψ : H →* kˣ

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace BrauerLinGen

/--
The induced linear character attached to a generator of `BrauerSpanLin`.-/
noncomputable def inducedCharacter
  (i : BrauerLinGen k G) : ClassFun k G :=
    ClassFun.character (FDRep.indLin i.H i.ψ)

/--
@isnad1 id=eq.0h4v.s6.f9dcca25b428 from=translated src=- shape=9173c781 vocab=94e84ba7
-/
@[simp] lemma inducedCharacter_apply
    (i : BrauerLinGen k G) (g : G) :
    BrauerLinGen.inducedCharacter i g
      =
    (FDRep.indLin i.H i.ψ).character g := rfl

end BrauerLinGen

/--
The `ℤ`-span of characters induced from linear characters of Brauer-elementary
subgroups.-/
def BrauerSpanLin : Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (Set.range (BrauerLinGen.inducedCharacter))

/--
Membership in `BrauerSpanLin` gives an explicit finite `ℤ`-linear combination
of induced linear characters.
@isnad1 id=ex.1h3v.s9.104480c27d9e from=translated src=- shape=fd827e79 vocab=da84b9ea
-/
theorem BrauerSpanLin.exists_decomposition
    {χ : ClassFun k G}
    (hχ : χ ∈ BrauerSpanLin) :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ) (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsBrauerElementary (Hs i)) ∧
      χ = ∑ i, (ns i) • ClassFun.character (FDRep.indLin (Hs i) (ψs i)) := by
  let P : ClassFun k G → Prop :=
    fun φ =>
      ∃ (ι : Type) (_ : Fintype ι)
        (ns : ι → ℤ) (Hs : ι → Subgroup G)
        (ψs : ∀ i, Hs i →* kˣ),
        (∀ i,  IsBrauerElementary (Hs i)) ∧
        φ = ∑ i, (ns i) • ClassFun.character (FDRep.indLin (Hs i) (ψs i))
  have hP : P χ := by
    refine Submodule.span_induction (p := fun φ _ => P φ) ?gen ?zero ?add ?smul hχ
    · intro φ hφ
      rcases hφ with ⟨i, rfl⟩
      refine ⟨PUnit, inferInstance,
        (fun _ => (1 : ℤ)), (fun _ => i.H), (fun _ => i.ψ), (fun _ => i.hElem), ?_⟩
      ext g
      simp [BrauerLinGen.inducedCharacter]
    · refine
        ⟨Empty, inferInstance, isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, ?_⟩
      simp only [Finset.univ_eq_empty, zsmul_eq_mul, Finset.sum_empty]
    · intro x y _ _ hx hy
      rcases hx with ⟨ιx, _, nsx, Hsx, ψsx, hHx, rfl⟩
      rcases hy with ⟨ιy, _, nsy, Hsy, ψsy, hHy, rfl⟩
      refine
        ⟨Sum ιx ιy,
         inferInstance,
         Sum.elim nsx nsy,
         Sum.elim Hsx Hsy,
         (fun i => match i with | Sum.inl j => ψsx j | Sum.inr j => ψsy j),
         (fun i => match i with | Sum.inl j => hHx j | Sum.inr j => hHy j),
         ?_⟩
      simp only [zsmul_eq_mul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    · intro n x _ hx
      rcases hx with ⟨ιx, _, nsx, Hsx, ψsx, hHx, rfl⟩
      refine ⟨ιx, inferInstance, (fun i => n * nsx i), Hsx, ψsx, hHx, ?_⟩
      rw [Finset.smul_sum]
      simp_rw [mul_smul]
  exact hP

end BrauerSpanLin
end BrauerInduction
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
