import Tengoku.DgLean.DG.Algebra.Decompose
import Tengoku.DgLean.DG.Module.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# dg submodules

A dg submodule of a dg `A`-module `M` is an `A`-submodule which is stable under the
differential and homogeneous (it contains the homogeneous components of each of its elements).
Such a submodule is itself a dg `A`-module, graded by `Sⁿ = S ∩ Mⁿ`, and the inclusion
`S →ᵈᵍ[A] M` is a morphism of dg modules.

* `DG.DGSubmodule A M`: the structure, extending `Submodule A M`.
* `DG.DGSubmodule.subtype`, `DG.DGSubmodule.codRestrict`: the inclusion and corestriction.
* `DG.DGModuleHom.ker`, `DG.DGModuleHom.range`: kernel and image of a morphism.

The decomposition of `S` into homogeneous components is obtained noncomputably from
`DirectSum.IsInternal`, which is proved using that the inclusion is injective of degree `0`
(`DG.coeAddMonoidHom_injective_of_injective`).
-/

open scoped DG

open DirectSum

namespace DG

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]

/-- A dg submodule of a dg module: an `A`-submodule stable under `d` and containing the
homogeneous components of its elements.-/
structure DGSubmodule (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [AddCommGroup M]
    [DGAddCommGroup M] [Module A M] extends Submodule A M where
  d_mem' : ∀ {m : M}, m ∈ carrier → d m ∈ carrier
  decompose_mem' : ∀ (n : ℤ) {m : M}, m ∈ carrier →
    (decompose (grading (M := M)) m n : M) ∈ carrier

namespace DGSubmodule

instance : SetLike (DGSubmodule A M) M where
  coe S := S.carrier
  coe_injective S T h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := S
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := T
    congr

instance : PartialOrder (DGSubmodule A M) := .ofSetLike (DGSubmodule A M) M

/--
@isnad1 id=iff.0h4v.s6.3196109c62fd from=translated src=- shape=f67bb2e2 vocab=87a906c0
-/
@[simp]
theorem mem_toSubmodule {S : DGSubmodule A M} {m : M} : m ∈ S.toSubmodule ↔ m ∈ S :=
  Iff.rfl

/--
@isnad1 id=iff.2h4v.s10.52712aeac793 from=translated src=- shape=ec171fb8 vocab=595e7945
-/
@[simp]
theorem mem_mk {p : Submodule A M} {h₁ h₂} {m : M} : m ∈ mk p h₁ h₂ ↔ m ∈ p :=
  Iff.rfl

/--
@isnad1 id=eq.1h4v.s6.c9268bbe6598 from=translated src=- shape=f667638b vocab=ce219961
-/
@[ext]
theorem ext {S T : DGSubmodule A M} (h : ∀ m, m ∈ S ↔ m ∈ T) : S = T :=
  SetLike.ext h

/--
@isnad1 id=injectiv.0h2v.s5.2af76b107b8a from=translated src=- shape=c69e4dc3 vocab=8d50e3c5
-/
theorem toSubmodule_injective :
    Function.Injective (DGSubmodule.toSubmodule : DGSubmodule A M → Submodule A M) :=
  fun _ _ h => ext fun m => by rw [← mem_toSubmodule, h, mem_toSubmodule]

variable (S : DGSubmodule A M)

/--
@isnad1 id=mem.1h4v.s7.3917544733fc from=translated src=- shape=ed8ba181 vocab=0ea24f45
-/
theorem d_mem {m : M} (hm : m ∈ S) : d m ∈ S :=
  S.d_mem' hm

/--
@isnad1 id=mem.1h5v.s9.ff43e71ed108 from=translated src=- shape=7bfb0558 vocab=8d288f84
-/
theorem decompose_mem (n : ℤ) {m : M} (hm : m ∈ S) :
    (decompose (grading (M := M)) m n : M) ∈ S :=
  S.decompose_mem' n hm

instance : AddSubgroupClass (DGSubmodule A M) M where
  add_mem := fun {S} => S.toSubmodule.add_mem
  zero_mem S := S.toSubmodule.zero_mem
  neg_mem := fun {S} => S.toSubmodule.neg_mem

instance : SMulMemClass (DGSubmodule A M) A M where
  smul_mem := fun {S} a => S.toSubmodule.smul_mem a

/--
@isnad1 id=eq.0h5v.s8.fe86785d1943 from=translated src=- shape=41b8104c vocab=98eef84d
-/
@[simp, norm_cast]
theorem coe_add (x y : S) : ((x + y : S) : M) = x + y := rfl

/--
@isnad1 id=eq.0h3v.s7.2eb095c83b0e from=translated src=- shape=7a7e01c9 vocab=11e8c435
-/
@[simp, norm_cast]
theorem coe_zero : ((0 : S) : M) = 0 := rfl

/--
@isnad1 id=eq.0h5v.s10.10d22a5d1a4c from=translated src=- shape=944e5f57 vocab=2d9dd41d
-/
@[simp, norm_cast]
theorem coe_smul (a : A) (x : S) : ((a • x : S) : M) = a • (x : M) := rfl

/-- The homogeneous components `Sⁿ = S ∩ Mⁿ` of a dg submodule.-/
def grading (n : ℤ) : AddSubgroup S :=
  (DGAddCommGroup.grading n).comap (AddSubgroupClass.subtype S)

/--
@isnad1 id=iff.0h5v.s8.f8f0466c7bdc from=translated src=- shape=8da6a284 vocab=7be2ed04
-/
theorem mem_grading_iff {n : ℤ} {x : S} : x ∈ S.grading n ↔ (x : M) ∈ DGAddCommGroup.grading n :=
  Iff.rfl

/--
@isnad1 id=isintern.0h3v.s8.652db49015e8 from=translated src=- shape=95591b26 vocab=78dd9f59
-/
theorem isInternal_grading : DirectSum.IsInternal S.grading := by
  classical
  refine ⟨coeAddMonoidHom_injective_of_injective S.grading (AddSubgroupClass.subtype S)
    (fun _ _ hx => hx) Subtype.val_injective, fun x => ?_⟩
  refine ⟨∑ n ∈ (decompose (DGAddCommGroup.grading (M := M)) (x : M)).support,
    DirectSum.of (fun n => S.grading n) n
      ⟨⟨decompose (DGAddCommGroup.grading (M := M)) (x : M) n, S.decompose_mem n x.2⟩,
        (decompose (DGAddCommGroup.grading (M := M)) (x : M) n).2⟩, ?_⟩
  apply Subtype.ext
  rw [map_sum]
  simp only [DirectSum.coeAddMonoidHom_of]
  rw [AddSubmonoidClass.coe_finsetSum]
  exact DirectSum.sum_support_decompose (DGAddCommGroup.grading (M := M)) (x : M)

/-- The differential of a dg submodule.-/
def d : S →+ S :=
  AddMonoidHom.codRestrict ((DGAddCommGroup.d : M →+ M).comp (AddSubgroupClass.subtype S)) S
    fun x => S.d_mem x.2

/--
@isnad1 id=eq.0h4v.s10.faeaa9a75eb0 from=translated src=- shape=4621a822 vocab=76d53fd1
-/
@[simp]
theorem coe_d_apply (x : S) : (S.d x : M) = DGAddCommGroup.d (x : M) := rfl

noncomputable instance instDGAddCommGroup : DGAddCommGroup S where
  grading := S.grading
  decomposition := S.isInternal_grading.chooseDecomposition
  d := S.d
  d_mem' hx := DG.d_mem hx
  d_d' x := Subtype.ext (by simp)

/--
@isnad1 id=eq.0h4v.s10.fa02572fc77a from=translated src=- shape=ec4d0a5f vocab=267be56e
-/
@[simp]
theorem coe_d (x : S) : ((DGAddCommGroup.d x : S) : M) = DGAddCommGroup.d (x : M) := rfl

/--
@isnad1 id=iff.0h5v.s9.3f5abc0601ad from=translated src=- shape=4d279259 vocab=3ee7b1cb
-/
@[simp]
theorem mem_grading {n : ℤ} {x : S} :
    x ∈ DGAddCommGroup.grading n ↔ (x : M) ∈ DGAddCommGroup.grading n :=
  Iff.rfl

variable [DGModule A M]

/--
@isnad1 id=dgmodule.0h3v.s7.937484676306 from=translated src=- shape=fde272f8 vocab=5d9ab92b
-/
instance instDGModule : DGModule A S where
  smul_mem _ _ _ _ ha hx := smul_mem_grading (M := M) ha hx
  d_smul' ha x := Subtype.ext (by
    rw [coe_d, coe_smul, d_smul ha (x : M)]
    simp only [coe_add, coe_smul]
    rfl)

/-- The inclusion of a dg submodule as a morphism of dg modules.-/
def subtype : S →ᵈᵍ[A] M where
  __ := S.toSubmodule.subtype
  map_mem' hx := hx
  map_d' _ := rfl

omit [DGModule A M] in
/--
@isnad1 id=eq.0h4v.s8.e56d38a72c47 from=translated src=- shape=bcd3c116 vocab=fc3ca433
-/
@[simp]
theorem subtype_apply (x : S) : S.subtype x = x := rfl

omit [DGModule A M] in
/--
@isnad1 id=injectiv.0h3v.s8.86b6b0e435c2 from=translated src=- shape=33917638 vocab=4843b5fe
-/
theorem subtype_injective : Function.Injective S.subtype :=
  Subtype.val_injective

variable {S} {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]

omit [DGModule A M]

/-- Corestriction of a morphism of dg modules to a dg submodule containing its image.-/
def codRestrict (f : N →ᵈᵍ[A] M) (h : ∀ x, f x ∈ S) : N →ᵈᵍ[A] S where
  __ := LinearMap.codRestrict S.toSubmodule f.toLinearMap h
  map_mem' hx := f.map_mem hx
  map_d' x := Subtype.ext (f.map_d x)

/--
@isnad1 id=eq.1h6v.s8.0c62fa3a5694 from=translated src=- shape=ec9bd4be vocab=b017fe30
-/
@[simp]
theorem coe_codRestrict_apply (f : N →ᵈᵍ[A] M) (h : ∀ x, f x ∈ S) (x : N) :
    (codRestrict f h x : M) = f x := rfl

/--
@isnad1 id=eq.1h5v.s8.15094ceb7a29 from=translated src=- shape=ee3562fe vocab=baafd257
-/
@[simp]
theorem subtype_comp_codRestrict (f : N →ᵈᵍ[A] M) (h : ∀ x, f x ∈ S) :
    S.subtype.comp (codRestrict f h) = f := rfl

/-- The decomposition of `S` is the restriction of that of `M`.
@isnad1 id=eq.0h5v.s13.d05c28d4f230 from=translated src=- shape=0557b251 vocab=8d288f84
-/
theorem coe_decompose_apply (x : S) (n : ℤ) :
    ((decompose (DGAddCommGroup.grading (M := S)) x n : S) : M) =
      decompose (DGAddCommGroup.grading (M := M)) (x : M) n :=
  (coe_decompose_map_of_map_mem S.subtype.toLinearMap.toAddMonoidHom
    (fun hx => S.subtype.map_mem hx) x n).symm

end DGSubmodule

namespace DGModuleHom

variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] (f : M →ᵈᵍ[A] N)

/-- The kernel of a morphism of dg modules, as a dg submodule.-/
def ker : DGSubmodule A M where
  __ := LinearMap.ker f.toLinearMap
  d_mem' := fun {m} hm => by
    have hm' : f m = 0 := hm
    show f (d m) = 0
    rw [map_d, hm', d_zero]
  decompose_mem' := fun n {m} hm => by
    have hm' : f m = 0 := hm
    show f _ = 0
    refine (coe_decompose_map_of_map_mem f.toLinearMap.toAddMonoidHom
      (fun hx => f.map_mem hx) m n).symm.trans ?_
    change (decompose (grading (M := N)) (f m) n : N) = 0
    rw [hm', decompose_zero,
      DirectSum.zero_apply, ZeroMemClass.coe_zero]

/--
@isnad1 id=iff.0h5v.s7.90c077985f0e from=translated src=- shape=d0eb6eda vocab=a4f5f24a
-/
@[simp]
theorem mem_ker {m : M} : m ∈ f.ker ↔ f m = 0 :=
  Iff.rfl

/-- The image of a morphism of dg modules, as a dg submodule.-/
def range : DGSubmodule A N where
  __ := LinearMap.range f.toLinearMap
  d_mem' := fun {x} hx => by
    obtain ⟨m, rfl⟩ : ∃ m, f m = x := hx
    exact ⟨d m, by simp⟩
  decompose_mem' := fun n {x} hx => by
    obtain ⟨m, rfl⟩ : ∃ m, f m = x := hx
    exact ⟨decompose (grading (M := M)) m n,
      (coe_decompose_map_of_map_mem f.toLinearMap.toAddMonoidHom (fun hx => f.map_mem hx) m n).symm⟩

/--
@isnad1 id=iff.0h5v.s7.31ea7fb888d6 from=translated src=- shape=5529b259 vocab=567a177b
-/
@[simp]
theorem mem_range {n : N} : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl

/--
@isnad1 id=mem.0h5v.s7.9d19eefa80ec from=translated src=- shape=503a00c6 vocab=567a177b
-/
theorem apply_mem_range (m : M) : f m ∈ f.range :=
  ⟨m, rfl⟩

/-- A morphism of dg modules corestricted to its image.-/
def rangeRestrict : M →ᵈᵍ[A] f.range :=
  DGSubmodule.codRestrict f f.apply_mem_range

/--
@isnad1 id=eq.0h5v.s8.209f26f27740 from=translated src=- shape=89820f6d vocab=acc610ed
-/
@[simp]
theorem coe_rangeRestrict_apply (m : M) : (f.rangeRestrict m : N) = f m := rfl

end DGModuleHom

end DG
