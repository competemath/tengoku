import Tengoku.StringDiagramsLean.StringDiagrams.Biadjunction.Cyclic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Traces for biadjunctions

For a biadjunction `P : f ⊣⊢ g` with `f : a ⟶ b` and `α : f ⟶ f`, the right trace
`rightTrace P α : 𝟙 a ⟶ 𝟙 a` closes the strand of `α` on its right and the left trace
`leftTrace P α : 𝟙 b ⟶ 𝟙 b` closes it on its left (the conventions of Etingof–Gelaki–
Nikshych–Ostrik, *Tensor categories*, §4.7, with `f ≫ g` drawn as `f` to the left of `g`).
Traces of identities are the dimensions ("bubbles").

## Main results

* `rightTrace_comp`: for `α : f ⟶ f'` and `β : f' ⟶ f`,
  `rightTrace P (α ≫ β) = rightTrace P' (β ≫ doubleMate P P' α)`, with no hypothesis; hence
  `rightTrace P (α ≫ β) = rightTrace P' (β ≫ α)` as soon as *one* of `α`, `β` is cyclic
  (`rightTrace_comp_comm_of_isCyclic_left`, `rightTrace_comp_comm_of_isCyclic_right`).
  Similarly `leftTrace_comp` and its corollaries.
* Traces and mates: `rightTrace P α = leftTrace P.symm (rightMate P P α)
  = leftTrace P.symm (leftMate P P α)`, and
  `leftTrace P α = rightTrace P.symm (rightMate P P α) = rightTrace P.symm (leftMate P P α)`;
  no cyclicity is needed. Consequently, for cyclic `α` the right trace of `α` is the left trace
  of its (unique) mate.
* `rightTrace_comp_hcomp`, `leftTrace_comp_hcomp` (and the whiskered special cases): traces
  for composite biadjunctions are computed strand by strand, the inner closed strand becoming
  a trace (a bubble) in the region it encloses.

Without cyclicity, `rightTrace P (α ≫ β)` and `rightTrace P' (β ≫ α)` need not agree, and
the left and right traces of `α` need not agree (no sphericality is assumed or implied).
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

namespace Biadjunction

variable {a b c : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

/--
@isnad1 id=eq.0h6v.s7.f1c3f0fad881 from=translated src=- shape=f7f4d45f vocab=89038264
-/
theorem rightTrace_id (P : f ⊣⊢ g) : rightTrace P (𝟙 f) = P.left.unit ≫ P.right.counit := by
  simp [rightTrace]

/--
@isnad1 id=eq.0h6v.s7.8ed8c3b03738 from=translated src=- shape=6e06317a vocab=1744112e
-/
theorem leftTrace_id (P : f ⊣⊢ g) : leftTrace P (𝟙 f) = P.right.unit ≫ P.left.counit := by
  simp [leftTrace]

/--
@isnad1 id=eq.0h7v.s8.b8741b29ae42 from=translated src=- shape=061d989e vocab=8651f72c
-/
theorem leftTrace_symm (P : f ⊣⊢ g) (γ : g ⟶ g) :
    leftTrace P.symm γ = P.left.unit ≫ f ◁ γ ≫ P.right.counit := rfl

/--
@isnad1 id=eq.0h7v.s8.e5d3c5c0e484 from=translated src=- shape=efde378a vocab=847586a2
-/
theorem rightTrace_symm (P : f ⊣⊢ g) (γ : g ⟶ g) :
    rightTrace P.symm γ = P.right.unit ≫ γ ▷ f ≫ P.left.counit := rfl

/-- Cyclicity of the right trace up to a full rotation, with no hypothesis.
@isnad1 id=eq.0h11v.s8.755f8b85d252 from=translated src=- shape=1f36ff8e vocab=417e2b54
-/
theorem rightTrace_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') (β : f' ⟶ f) :
    rightTrace P (α ≫ β) = rightTrace P' (β ≫ doubleMate P P' α) := by
  have h₁ : P.left.unit ≫ α ▷ g = P'.left.unit ≫ f' ◁ rightMate P P' α :=
    unit_comp_whiskerRight_eq P'.left P.left α
  have h₂ : f ◁ rightMate P P' α ≫ P.right.counit =
      doubleMate P P' α ▷ g' ≫ P'.right.counit :=
    whiskerLeft_comp_counit_eq P.right P'.right (rightMate P P' α)
  simp only [rightTrace, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% h₁, whisker_exchange_assoc, h₂]

/-- Cyclicity of the left trace up to a full rotation, with no hypothesis.
@isnad1 id=eq.0h11v.s8.b6ad131bfab9 from=translated src=- shape=efcbb2f2 vocab=4897ae24
-/
theorem leftTrace_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') (β : f' ⟶ f) :
    leftTrace P (α ≫ β) = leftTrace P' (doubleMate P' P β ≫ α) := by
  have h₁ : g ◁ β ≫ P.left.counit = rightMate P' P β ▷ f' ≫ P'.left.counit :=
    whiskerLeft_comp_counit_eq P.left P'.left β
  have h₂ : P.right.unit ≫ rightMate P' P β ▷ f =
      P'.right.unit ≫ g' ◁ doubleMate P' P β :=
    unit_comp_whiskerRight_eq P'.right P.right (rightMate P' P β)
  simp only [leftTrace, Bicategory.whiskerLeft_comp, Category.assoc]
  rw [h₁, whisker_exchange_assoc, reassoc_of% h₂]

/--
@isnad1 id=eq.1h11v.s8.1c28cc5bd529 from=translated src=- shape=a26cd2a9 vocab=5de2fcd5
-/
theorem rightTrace_comp_comm_of_isCyclic_left {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) (β : f' ⟶ f) :
    rightTrace P (α ≫ β) = rightTrace P' (β ≫ α) := by
  rw [rightTrace_comp P P', hα.doubleMate_eq]

/--
@isnad1 id=eq.1h11v.s8.64a04bb492c3 from=translated src=- shape=74d00e31 vocab=5de2fcd5
-/
theorem rightTrace_comp_comm_of_isCyclic_right {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} (α : f ⟶ f')
    {β : f' ⟶ f} (hβ : IsCyclic P' P β) :
    rightTrace P (α ≫ β) = rightTrace P' (β ≫ α) := by
  rw [rightTrace_comp P' P, hβ.doubleMate_eq]

/--
@isnad1 id=eq.1h11v.s8.fbdef99b0bf8 from=translated src=- shape=e40e5d6d vocab=4ee06013
-/
theorem leftTrace_comp_comm_of_isCyclic_right {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} (α : f ⟶ f')
    {β : f' ⟶ f} (hβ : IsCyclic P' P β) :
    leftTrace P (α ≫ β) = leftTrace P' (β ≫ α) := by
  rw [leftTrace_comp P P', hβ.doubleMate_eq]

/--
@isnad1 id=eq.1h11v.s8.1846358f43a6 from=translated src=- shape=032f4ac9 vocab=4ee06013
-/
theorem leftTrace_comp_comm_of_isCyclic_left {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) (β : f' ⟶ f) :
    leftTrace P (α ≫ β) = leftTrace P' (β ≫ α) := by
  rw [leftTrace_comp P' P, hα.doubleMate_eq]

/-- The right trace of `α` is the left trace of its right mate.
@isnad1 id=eq.0h7v.s9.b3b7ecf5cb4c from=translated src=- shape=a50dae77 vocab=5dcd730c
-/
theorem rightTrace_eq_leftTrace_rightMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    rightTrace P α = leftTrace P.symm (rightMate P P α) := by
  rw [rightTrace, leftTrace_symm, reassoc_of% (unit_comp_whiskerRight_eq P.left P.left α)]
  rfl

/-- The right trace of `α` is the left trace of its left mate.
@isnad1 id=eq.0h7v.s9.8efd7f105b7c from=translated src=- shape=a50dae77 vocab=78c1de14
-/
theorem rightTrace_eq_leftTrace_leftMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    rightTrace P α = leftTrace P.symm (leftMate P P α) := by
  rw [rightTrace, leftTrace_symm, whiskerRight_comp_counit_eq P.right P.right α]
  rfl

/-- The left trace of `α` is the right trace of its right mate.
@isnad1 id=eq.0h7v.s9.cb05af98c33c from=translated src=- shape=34224927 vocab=5dcd730c
-/
theorem leftTrace_eq_rightTrace_rightMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    leftTrace P α = rightTrace P.symm (rightMate P P α) := by
  rw [leftTrace, rightTrace_symm, whiskerLeft_comp_counit_eq P.left P.left α]
  rfl

/-- The left trace of `α` is the right trace of its left mate.
@isnad1 id=eq.0h7v.s9.9f7a8ecf4a88 from=translated src=- shape=34224927 vocab=78c1de14
-/
theorem leftTrace_eq_rightTrace_leftMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    leftTrace P α = rightTrace P.symm (leftMate P P α) := by
  rw [leftTrace, rightTrace_symm, reassoc_of% (unit_comp_whiskerLeft_eq P.right P.right α)]
  rfl

/-- The right trace of a 2-morphism `γ : g ⟶ g` for the exchanged biadjunction is the left
trace of either of its inverse mates.
@isnad1 id=eq.0h7v.s9.0db22d38a5ee from=translated src=- shape=a7705dd6 vocab=5474cb7c
-/
theorem rightTrace_symm_eq_leftTrace (P : f ⊣⊢ g) (γ : g ⟶ g) :
    rightTrace P.symm γ = leftTrace P ((rightMate P P).symm γ) := by
  rw [leftTrace_eq_rightTrace_rightMate, Equiv.apply_symm_apply]

/--
@isnad1 id=eq.0h7v.s9.dbf404d57545 from=translated src=- shape=dfbded41 vocab=5474cb7c
-/
theorem leftTrace_symm_eq_rightTrace (P : f ⊣⊢ g) (γ : g ⟶ g) :
    leftTrace P.symm γ = rightTrace P ((rightMate P P).symm γ) := by
  rw [rightTrace_eq_leftTrace_rightMate, Equiv.apply_symm_apply]

/-! ## Partial traces -/

section Partial

variable {h : b ⟶ c} {k : c ⟶ b}

/-- The right trace for a composite biadjunction, of `γ ▷ h ≫ f ◁ β`: the inner `h`-strand
closes to the right trace of `β`, inside the `f`-strand.
@isnad1 id=eq.0h12v.s9.f54eb233c755 from=translated src=- shape=36a09ed8 vocab=29db928d
-/
theorem rightTrace_comp_hcomp (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) (β : h ⟶ h) :
    rightTrace (P.comp R) (γ ▷ h ≫ f ◁ β) =
      rightTrace P (γ ≫ (ρ_ f).inv ≫ f ◁ rightTrace R β ≫ (ρ_ f).hom) := by
  simp only [rightTrace, comp_left, comp_right, Adjunction.comp_unit, Adjunction.comp_counit,
    Adjunction.compUnit, Adjunction.compCounit]
  calc
    _ = P.left.unit ⊗≫ (f ◁ R.left.unit ≫ γ ▷ (h ≫ k)) ▷ g ⊗≫ f ◁ β ▷ k ▷ g ⊗≫
          f ◁ R.right.counit ▷ g ⊗≫ P.right.counit := by
      bicategory
    _ = P.left.unit ⊗≫ (γ ▷ 𝟙 b ≫ f ◁ R.left.unit) ▷ g ⊗≫ f ◁ β ▷ k ▷ g ⊗≫
          f ◁ R.right.counit ▷ g ⊗≫ P.right.counit := by
      rw [whisker_exchange]
    _ = _ := by
      bicategory

/-- The left trace for a composite biadjunction, of `γ ▷ h ≫ f ◁ β`: the inner `f`-strand
closes to the left trace of `γ`, inside the `h`-strand.
@isnad1 id=eq.0h12v.s9.2e10e52d92ad from=translated src=- shape=b59afcf2 vocab=7731cb66
-/
theorem leftTrace_comp_hcomp (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) (β : h ⟶ h) :
    leftTrace (P.comp R) (γ ▷ h ≫ f ◁ β) =
      leftTrace R ((λ_ h).inv ≫ leftTrace P γ ▷ h ≫ (λ_ h).hom ≫ β) := by
  simp only [leftTrace, comp_left, comp_right, Adjunction.comp_unit, Adjunction.comp_counit,
    Adjunction.compUnit, Adjunction.compCounit]
  calc
    _ = R.right.unit ⊗≫ k ◁ P.right.unit ▷ h ⊗≫ k ◁ g ◁ γ ▷ h ⊗≫
          k ◁ ((g ≫ f) ◁ β ≫ P.left.counit ▷ h) ⊗≫ R.left.counit := by
      bicategory
    _ = R.right.unit ⊗≫ k ◁ P.right.unit ▷ h ⊗≫ k ◁ g ◁ γ ▷ h ⊗≫
          k ◁ (P.left.counit ▷ h ≫ 𝟙 b ◁ β) ⊗≫ R.left.counit := by
      rw [whisker_exchange]
    _ = _ := by
      bicategory

/--
@isnad1 id=eq.0h11v.s8.efd64c5a8141 from=translated src=- shape=51ef4c8e vocab=29db928d
-/
theorem rightTrace_comp_whiskerRight (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) :
    rightTrace (P.comp R) (γ ▷ h) =
      rightTrace P (γ ≫ (ρ_ f).inv ≫ f ◁ rightTrace R (𝟙 h) ≫ (ρ_ f).hom) := by
  rw [← rightTrace_comp_hcomp, Bicategory.whiskerLeft_id, Category.comp_id]

/--
@isnad1 id=eq.0h11v.s8.fe318ad1a993 from=translated src=- shape=0b6dd003 vocab=5bb85c26
-/
theorem rightTrace_comp_whiskerLeft (P : f ⊣⊢ g) (R : h ⊣⊢ k) (β : h ⟶ h) :
    rightTrace (P.comp R) (f ◁ β) =
      rightTrace P ((ρ_ f).inv ≫ f ◁ rightTrace R β ≫ (ρ_ f).hom) := by
  have := rightTrace_comp_hcomp P R (𝟙 f) β
  rwa [id_whiskerRight, Category.id_comp, Category.id_comp] at this

/--
@isnad1 id=eq.0h11v.s8.4e5159b1a692 from=translated src=- shape=437d5e90 vocab=7731cb66
-/
theorem leftTrace_comp_whiskerLeft (P : f ⊣⊢ g) (R : h ⊣⊢ k) (β : h ⟶ h) :
    leftTrace (P.comp R) (f ◁ β) =
      leftTrace R ((λ_ h).inv ≫ leftTrace P (𝟙 f) ▷ h ≫ (λ_ h).hom ≫ β) := by
  rw [← leftTrace_comp_hcomp, id_whiskerRight, Category.id_comp]

/--
@isnad1 id=eq.0h11v.s8.06bb32c8cbcf from=translated src=- shape=3088d877 vocab=4636ac3f
-/
theorem leftTrace_comp_whiskerRight (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) :
    leftTrace (P.comp R) (γ ▷ h) =
      leftTrace R ((λ_ h).inv ≫ leftTrace P γ ▷ h ≫ (λ_ h).hom) := by
  have := leftTrace_comp_hcomp P R γ (𝟙 h)
  rwa [Bicategory.whiskerLeft_id, Category.comp_id, Category.comp_id] at this

end Partial

end Biadjunction

end StringDiagrams
