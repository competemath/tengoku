import Tengoku.Seed.Algebra.DirectSum.Decomposition
import Tengoku.Seed.RingTheory.GradedAlgebra.Basic
import Tengoku.DgLean.DG.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generic helpers for internally graded objects

This file collects generic constructions about objects graded by an additive monoid `ι` in
Mathlib's internal style: a type `M` with a family `ℳ : ι → σ` of subobjects (`σ` a `SetLike`
type with `AddSubmonoidClass σ M`) and a `DirectSum.Decomposition ℳ`. In the rest of the
library `ι = ℤ`.

## Main definitions

* `DG.summand β i`: the `i`-th summand of an external direct sum `⨁ i, β i`, as an
  additive subgroup, together with the `DirectSum.Decomposition` instance exhibiting the external
  direct sum as internally graded by its summands, and the `GradedRing` instance when `β` is a
  `DirectSum.GSemiring`.
* `DG.proj ℳ i : M →+ ℳ i`: the projection onto the degree-`i` homogeneous component.
* `DG.liftHomogeneous ℳ φ : M →+ N`: the extension of a family `φ i : ℳ i →+ N` of additive maps
  on the homogeneous components to all of `M`.
* `DG.decompose_addHom_ext`: two additive maps out of `M` agreeing on homogeneous elements are
  equal.
-/

namespace DG

open DirectSum

/-! ### External direct sums as internally graded objects -/

section Summand

variable {ι : Type*} [DecidableEq ι] (β : ι → Type*) [∀ i, AddCommGroup (β i)]

/-- The `i`-th summand of the external direct sum `⨁ i, β i`, as an additive subgroup: the range
of `DirectSum.of β i`.-/
def summand (i : ι) : AddSubgroup (⨁ i, β i) := (DirectSum.of β i).range

variable {β}

/--
@isnad1 id=iff.0h4v.s8.5d5a36a584c3 from=translated src=- shape=66cc3861 vocab=3afe00cb
-/
theorem mem_summand {i : ι} {x : ⨁ i, β i} : x ∈ summand β i ↔ ∃ b, DirectSum.of β i b = x :=
  AddMonoidHom.mem_range

/--
@isnad1 id=mem.0h4v.s8.a4b19756db0a from=translated src=- shape=769b4f77 vocab=3afe00cb
-/
theorem of_mem_summand (i : ι) (b : β i) : DirectSum.of β i b ∈ summand β i := ⟨b, rfl⟩

variable (β)

/-- The summand `β i` is isomorphic to its image in the external direct sum.-/
noncomputable def summandEquiv (i : ι) : β i ≃+ summand β i :=
  AddMonoidHom.ofInjective (DirectSum.of_injective i)

/--
@isnad1 id=eq.0h4v.s10.20a3037d93bc from=translated src=- shape=02c225f4 vocab=b576ed05
-/
@[simp]
theorem coe_summandEquiv_apply (i : ι) (b : β i) :
    (summandEquiv β i b : ⨁ i, β i) = DirectSum.of β i b := rfl

/-- The external direct sum `⨁ i, β i` is internally graded by its summands.-/
noncomputable instance instDecompositionSummand : Decomposition (summand β) :=
  Decomposition.ofAddHom (summand β)
    (DirectSum.toAddMonoid fun i =>
      (DirectSum.of (fun i => summand β i) i).comp (summandEquiv β i).toAddMonoidHom)
    (by ext i b; simp)
    (by
      ext i ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := hx
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        DirectSum.toAddMonoid_of, AddMonoidHom.id_comp]
      rfl)

/--
@isnad1 id=eq.0h4v.s13.bfb183ed3a0a from=translated src=- shape=d185455e vocab=e515c98c
-/
theorem decompose_summand_of (i : ι) (b : β i) :
    decompose (summand β) (DirectSum.of β i b) = DirectSum.of _ i (summandEquiv β i b) :=
  decompose_of_mem _ (of_mem_summand i b)

section GSemiring

variable [AddMonoid ι] [GSemiring β]

/--
@isnad1 id=gradedmo.0h2v.s7.e0d18e4f0252 from=translated src=- shape=8b1a09a6 vocab=e3ff85a2
-/
instance instGradedMonoidSummand : SetLike.GradedMonoid (summand β) where
  one_mem := ⟨GradedMonoid.GOne.one, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨GradedMonoid.GMul.mul a b, (DirectSum.of_mul_of a b).symm⟩

/-- The external direct sum of a graded semiring is a graded ring with respect to the grading
by its summands.-/
noncomputable instance instGradedRingSummand : GradedRing (summand β) := {}

end GSemiring

section GRing
variable [AddMonoid ι] [GRing β]
end GRing

end Summand

/-! ### Homogeneous components -/

section Decomposition

variable {ι M σ : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
variable (ℳ : ι → σ) [Decomposition ℳ]

/-- The projection of a graded object onto its degree-`i` homogeneous component.-/
def proj (i : ι) : M →+ ℳ i where
  toFun m := decompose ℳ m i
  map_zero' := by simp
  map_add' _ _ := by simp

/--
@isnad1 id=eq.0h6v.s9.cb08a594c5b1 from=translated src=- shape=d3afdf49 vocab=38e25812
-/
@[simp]
theorem proj_apply (i : ι) (m : M) : proj ℳ i m = decompose ℳ m i := rfl

/--
@isnad1 id=eq.0h6v.s8.c9668f492e69 from=translated src=- shape=935e0378 vocab=bd405164
-/
@[simp]
theorem proj_coe {i : ι} (m : ℳ i) : proj ℳ i m = m := by
  simp [proj_apply]

/--
@isnad1 id=eq.1h6v.s8.6b813eb3833b from=translated src=- shape=b6bfbd68 vocab=fdfbf909
-/
theorem proj_of_mem_same {i : ι} {m : M} (h : m ∈ ℳ i) : proj ℳ i m = ⟨m, h⟩ :=
  proj_coe ℳ ⟨m, h⟩

/--
@isnad1 id=eq.1h6v.s8.5da9970bfd82 from=translated src=- shape=aee1909a vocab=bd405164
-/
theorem coe_proj_of_mem_same {i : ι} {m : M} (h : m ∈ ℳ i) : (proj ℳ i m : M) = m :=
  decompose_of_mem_same ℳ h

/--
@isnad1 id=eq.2h7v.s8.1e00ffbd9762 from=translated src=- shape=58f01da5 vocab=bd405164
-/
theorem coe_proj_of_mem_ne {i j : ι} {m : M} (h : m ∈ ℳ i) (hij : i ≠ j) :
    (proj ℳ j m : M) = 0 :=
  decompose_of_mem_ne ℳ h hij

/--
@isnad1 id=eq.2h7v.s8.6bc4c6e63862 from=translated src=- shape=01083da8 vocab=0bc4618b
-/
theorem proj_of_mem_ne {i j : ι} {m : M} (h : m ∈ ℳ i) (hij : i ≠ j) : proj ℳ j m = 0 :=
  Subtype.ext (coe_proj_of_mem_ne ℳ h hij)

/--
@isnad1 id=eq.1h7v.s8.e5f91a6d01cb from=translated src=- shape=4f43920b vocab=bd405164
-/
theorem proj_coe_of_ne {i j : ι} (m : ℳ i) (hij : i ≠ j) : proj ℳ j m = 0 :=
  proj_of_mem_ne ℳ m.2 hij

variable {N : Type*} [AddCommMonoid N]

/-- Two additive maps out of a graded object which agree on homogeneous elements are equal.
@isnad1 id=eq.1h7v.s7.1ed776ace24b from=translated src=- shape=eb3d5003 vocab=e5475a04
-/
theorem decompose_addHom_ext ⦃f g : M →+ N⦄ (h : ∀ (i : ι) (m : ℳ i), f m = g m) : f = g :=
  AddMonoidHom.ext fun m =>
    Decomposition.inductionOn ℳ (by simp) (fun m => h _ m)
      (fun a b ha hb => by simp [ha, hb]) m

/-- The additive map `M →+ N` obtained by extending a family of additive maps `ℳ i →+ N` on the
homogeneous components.-/
def liftHomogeneous (φ : ∀ i, ℳ i →+ N) : M →+ N :=
  (DirectSum.toAddMonoid φ).comp (decomposeAddEquiv ℳ).toAddMonoidHom

/--
@isnad1 id=eq.0h8v.s8.4020fc9e9940 from=translated src=- shape=d20b3bba vocab=56daa6ea
-/
@[simp]
theorem liftHomogeneous_coe (φ : ∀ i, ℳ i →+ N) {i : ι} (m : ℳ i) :
    liftHomogeneous ℳ φ m = φ i m := by
  simp [liftHomogeneous]

/--
@isnad1 id=eq.1h8v.s8.06a92a8a6d45 from=translated src=- shape=87fe28a2 vocab=e10e9fb5
-/
theorem liftHomogeneous_of_mem (φ : ∀ i, ℳ i →+ N) {i : ι} {m : M} (h : m ∈ ℳ i) :
    liftHomogeneous ℳ φ m = φ i ⟨m, h⟩ :=
  liftHomogeneous_coe ℳ φ ⟨m, h⟩

/--
@isnad1 id=eq.0h7v.s9.4c3a6450372d from=translated src=- shape=300226c9 vocab=2d26d854
-/
theorem liftHomogeneous_apply (φ : ∀ i, ℳ i →+ N) (m : M) :
    liftHomogeneous ℳ φ m = DirectSum.toAddMonoid φ (decompose ℳ m) := rfl

/-- Extending the restrictions of an additive map to the homogeneous components recovers it.
@isnad1 id=eq.0h6v.s7.60b710fa1384 from=translated src=- shape=e4528d34 vocab=dbd8b463
-/
@[simp]
theorem liftHomogeneous_comp_subtype (f : M →+ N) :
    liftHomogeneous ℳ (fun i => f.comp (AddSubmonoidClass.subtype (ℳ i))) = f :=
  decompose_addHom_ext ℳ fun _ _ => by simp

/--
@isnad1 id=eq.0h7v.s8.927893eac29c from=translated src=- shape=97923b7e vocab=dbd8b463
-/
theorem liftHomogeneous_comp_subtype' (φ : ∀ i, ℳ i →+ N) (i : ι) :
    (liftHomogeneous ℳ φ).comp (AddSubmonoidClass.subtype (ℳ i)) = φ i :=
  AddMonoidHom.ext fun _ => by simp

/-- Additive maps out of a graded object are the same as families of additive maps on its
homogeneous components.-/
def liftHomogeneousEquiv : (∀ i, ℳ i →+ N) ≃+ (M →+ N) where
  toFun := liftHomogeneous ℳ
  invFun f i := f.comp (AddSubmonoidClass.subtype (ℳ i))
  left_inv φ := funext fun i => liftHomogeneous_comp_subtype' ℳ φ i
  right_inv := liftHomogeneous_comp_subtype ℳ
  map_add' φ ψ := decompose_addHom_ext ℳ fun _ _ => by simp

end Decomposition

end DG
