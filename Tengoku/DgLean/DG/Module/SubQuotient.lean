import Tengoku.DgLean.DG.Module.Sub
import Tengoku.DgLean.DG.Module.Quotient
import Tengoku.Seed.LinearAlgebra.Quotient.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quotients of dg modules by dg submodules

For a dg submodule `S` of a dg `A`-module `M`, the quotient module `M ⧸ S.toSubmodule` is a dg
`A`-module: its homogeneous components are the images of those of `M` and its differential is
induced by `d` (`DG.DGAddCommGroup.quotient`, since `S` is a dg subgroup). The quotient map
`DG.DGSubmodule.mkQ S : M →ᵈᵍ[A] M ⧸ S.toSubmodule` is a morphism of dg modules, and a morphism
of dg modules vanishing on `S` factors through it (`DG.DGSubmodule.liftQ`).
-/

open scoped DG

namespace DG

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]

namespace DGSubmodule

variable (S : DGSubmodule A M)

/-- A dg submodule is a dg subgroup.
@isnad1 id=isdgadds.0h3v.s5.a128d393013f from=translated src=- shape=70d866e7 vocab=7b819067
-/
instance isDGAddSubgroup : IsDGAddSubgroup S.toSubmodule.toAddSubgroup where
  decompose_mem hx n := S.decompose_mem n hx
  d_mem hx := S.d_mem hx

/-- The quotient of a dg module by a dg submodule is a dg abelian group, with
`(M ⧸ S)ⁿ` the image of `Mⁿ` and the induced differential.-/
noncomputable instance quotientDGAddCommGroup : DGAddCommGroup (M ⧸ S.toSubmodule) :=
  DGAddCommGroup.quotient S.toSubmodule.toAddSubgroup

/--
@isnad1 id=iff.0h5v.s8.1a41f1492ecf from=translated src=- shape=cfb85f08 vocab=bcfa693a
-/
theorem mem_grading_quotient_iff {n : ℤ} {y : M ⧸ S.toSubmodule} :
    y ∈ DGAddCommGroup.grading n ↔
      ∃ x ∈ DGAddCommGroup.grading (M := M) n, Submodule.Quotient.mk x = y :=
  Iff.rfl

/--
@isnad1 id=mem.1h5v.s8.4304ba7f30c7 from=translated src=- shape=7ed1e192 vocab=bcfa693a
-/
theorem mk_mem_grading {n : ℤ} {x : M} (hx : x ∈ DGAddCommGroup.grading n) :
    (Submodule.Quotient.mk x : M ⧸ S.toSubmodule) ∈ DGAddCommGroup.grading n :=
  ⟨x, hx, rfl⟩

/--
@isnad1 id=eq.0h4v.s10.e4e2a434bb8a from=translated src=- shape=68ac4f75 vocab=3129eedb
-/
@[simp]
theorem d_mk (x : M) :
    DGAddCommGroup.d (Submodule.Quotient.mk x : M ⧸ S.toSubmodule) =
      Submodule.Quotient.mk (DGAddCommGroup.d x) :=
  rfl

variable [DGModule A M]

/-- The quotient of a dg module by a dg submodule is a dg module.
@isnad1 id=dgmodule.0h3v.s6.27e8f6ffd308 from=translated src=- shape=bb2a4736 vocab=04e63024
-/
instance quotientDGModule : DGModule A (M ⧸ S.toSubmodule) where
  smul_mem _ _ a _ ha hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨a • x, smul_mem_grading ha hx, rfl⟩
  d_smul' {n a} ha y := by
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, d_mk, d_smul ha, d_mk, Submodule.Quotient.mk_add,
        Units.smul_def, Units.smul_def, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_smul]

omit [DGModule A M]

/-- The quotient map `M → M ⧸ S` as a morphism of dg modules.-/
def mkQ : M →ᵈᵍ[A] M ⧸ S.toSubmodule where
  __ := S.toSubmodule.mkQ
  map_mem' hx := S.mk_mem_grading hx
  map_d' _ := rfl

/--
@isnad1 id=eq.0h4v.s8.6e2e5e30a3b4 from=translated src=- shape=e7c8afd3 vocab=3fff0212
-/
@[simp]
theorem mkQ_apply (x : M) : S.mkQ x = Submodule.Quotient.mk x := rfl

/--
@isnad1 id=surjecti.0h3v.s8.f8877eaf0d5e from=translated src=- shape=1571d968 vocab=e846d7bc
-/
theorem mkQ_surjective : Function.Surjective S.mkQ :=
  Submodule.mkQ_surjective _

/--
@isnad1 id=iff.0h4v.s8.0bc15857eda1 from=translated src=- shape=931fb705 vocab=5ff0e204
-/
theorem mkQ_eq_zero_iff {x : M} : S.mkQ x = 0 ↔ x ∈ S :=
  Submodule.Quotient.mk_eq_zero _

/--
@isnad1 id=eq.0h3v.s7.88bfabf435d5 from=translated src=- shape=aa83b67b vocab=33dc09f9
-/
@[simp]
theorem ker_mkQ : S.mkQ.ker = S :=
  ext fun _ => S.mkQ_eq_zero_iff

variable {S} {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- A morphism of dg modules vanishing on `S` factors through the quotient `M ⧸ S`.-/
def liftQ (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) : (M ⧸ S.toSubmodule) →ᵈᵍ[A] N where
  __ := S.toSubmodule.liftQ f.toLinearMap fun x hx => h x hx
  map_mem' := by
    rintro n _ ⟨x, hx, rfl⟩
    exact f.map_mem hx
  map_d' y := by
    induction y using Submodule.Quotient.induction_on with
    | H x => exact f.map_d x

/--
@isnad1 id=eq.1h6v.s8.9e8a426aa204 from=translated src=- shape=06b9bf31 vocab=45e06415
-/
@[simp]
theorem liftQ_mk (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) (x : M) :
    liftQ f h (Submodule.Quotient.mk x) = f x := rfl

/--
@isnad1 id=eq.1h6v.s9.32cd1d275420 from=translated src=- shape=17fcb958 vocab=50a46606
-/
@[simp]
theorem liftQ_mkQ (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) (x : M) :
    liftQ f h (S.mkQ x) = f x := rfl

/--
@isnad1 id=eq.1h5v.s8.e659b249ee53 from=translated src=- shape=709ef224 vocab=98c7a45c
-/
@[simp]
theorem liftQ_comp_mkQ (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) : (liftQ f h).comp S.mkQ = f :=
  rfl

/-- Two morphisms out of `M ⧸ S` agreeing after composition with the quotient map are equal.
@isnad1 id=eq.1h6v.s8.de2db81fd8db from=translated src=- shape=33f7abce vocab=a03c4f4d
-/
theorem quotient_ext {f g : (M ⧸ S.toSubmodule) →ᵈᵍ[A] N} (h : f.comp S.mkQ = g.comp S.mkQ) :
    f = g :=
  DGModuleHom.ext fun y => by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    exact congrArg (fun φ : M →ᵈᵍ[A] N => φ x) h

end DGSubmodule

end DG
