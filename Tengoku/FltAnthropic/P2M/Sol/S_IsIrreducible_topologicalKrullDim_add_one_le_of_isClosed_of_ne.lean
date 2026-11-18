import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne

set_option autoImplicit false

open Set Order TopologicalSpace Topology

universe u

namespace P2mDim

variable {X : Type u} [TopologicalSpace X] {Y Z : Set X}

def topIC (hZ : IsIrreducible Z) : IrreducibleCloseds Z where
  carrier := univ
  isIrreducible' := by
    haveI : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
    exact IrreducibleSpace.isIrreducible_univ Z
  isClosed' := isClosed_univ

def push (hYZ : Y ⊆ Z) : IrreducibleCloseds Y → IrreducibleCloseds Z :=
  IrreducibleCloseds.map (inclusion hYZ) (continuous_inclusion hYZ)

/--
@isnad1 id=strictmo.1h3v.s7.f22d2f6925e6 from=translated src=- shape=73312a62 vocab=b17d6d4b
-/
theorem push_strictMono (hYZ : Y ⊆ Z) : StrictMono (push (X := X) hYZ) :=
  IrreducibleCloseds.map_strictMono_of_isInducing (IsEmbedding.inclusion hYZ).isInducing

/--
@isnad1 id=le.2h4v.s6.d2edbf20b5ef from=translated src=- shape=a7c5f9ee vocab=8e0a51bb
-/
theorem coe_push_subset (hYZ : Y ⊆ Z) (hY : IsClosed Y) (s : IrreducibleCloseds Y) :
    ((push hYZ s : IrreducibleCloseds Z) : Set Z) ⊆ (Subtype.val ⁻¹' Y : Set Z) := by
  show closure (inclusion hYZ '' (s : Set Y)) ⊆ _
  refine closure_minimal ?_ (hY.preimage continuous_subtype_val)
  rintro _ ⟨y, _, rfl⟩
  exact y.2

/--
@isnad1 id=lt.4h4v.s7.b66007f8b39c from=translated src=- shape=de5e1e28 vocab=fda24adc
-/
theorem push_lt_top (hZ : IsIrreducible Z) (hYZ : Y ⊆ Z) (hY : IsClosed Y) (hne : Y ≠ Z)
    (s : IrreducibleCloseds Y) : push hYZ s < topIC hZ := by
  refine lt_of_le_of_ne (fun _ _ => trivial) fun h => hne ?_
  refine subset_antisymm hYZ fun z hz => ?_
  have hmem : (⟨z, hz⟩ : Z) ∈ ((push hYZ s : IrreducibleCloseds Z) : Set Z) := by
    rw [h]; trivial
  exact coe_push_subset hYZ hY s hmem

/--
@isnad1 id=le.4h3v.s6.013f430b2084 from=translated src=- shape=17a64f4a vocab=0d01ba80
-/
theorem main (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z := by
  unfold topologicalKrullDim
  cases isEmpty_or_nonempty (IrreducibleCloseds Y) with
  | inl h =>
    rw [krullDim_eq_bot]
    exact bot_le
  | inr h =>
    rw [← krullDim_WithTop]

    let g : WithTop (IrreducibleCloseds Y) → IrreducibleCloseds Z :=
      fun a => WithTop.recTopCoe (topIC hZ) (fun s => push hYZ s) a
    refine krullDim_le_of_strictMono g fun a b hab => ?_
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe s =>
      induction b using WithTop.recTopCoe with
      | top => exact push_lt_top hZ hYZ hY hne s
      | coe t => exact push_strictMono hYZ (WithTop.coe_lt_coe.mp hab)

end P2mDim

/--
@isnad1 id=le.4h3v.s6.013f430b2084 from=translated src=- shape=17a64f4a vocab=0d01ba80
-/
theorem solution
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z :=
  P2mDim.main hZ hY hYZ hne
