import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfOrderData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_mem_of_forall_mem_dual_apply_mem_range.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfOrder_mem_of_forall_mem_dual_apply_mem_range

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace S17Dual

section DualOrder

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

/--
@isnad1 id=eq.0h5v.s9.22837abf8735 from=translated src=- shape=03625dd4 vocab=27dde2ac
-/
theorem add_apply' (φ ψ : CartierDual K A) (a : A) : (φ + ψ) a = φ a + ψ a := rfl
/--
@isnad1 id=eq.0h3v.s9.0d98a6ecd3f0 from=translated src=- shape=c286e80d vocab=74453711
-/
theorem zero_apply' (a : A) : (0 : CartierDual K A) a = 0 := rfl

/--
@isnad1 id=mem.2h7v.s14.30d88ad4996c from=translated src=- shape=540b4a23 vocab=f0084419
-/
theorem dualDistrib_tensorSqHom_mem (S : Subalgebra R A) (φ ψ : CartierDual K A)
    (hφ : ∀ b ∈ S, φ b ∈ (algebraMap R K).range) (hψ : ∀ b ∈ S, ψ b ∈ (algebraMap R K).range)
    (z : ↥S ⊗[R] ↥S) :
    TensorProduct.dualDistrib K A A (CartierDual.toDual K A φ ⊗ₜ[K] CartierDual.toDual K A ψ)
      (HopfOrder.tensorSqHom (K := K) S z) ∈ (algebraMap R K).range := by
  induction z with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul s t =>
      rw [HopfOrder.tensorSqHom_tmul, TensorProduct.dualDistrib_apply, CartierDual.toDual_apply,
        CartierDual.toDual_apply]
      exact mul_mem (hφ s s.2) (hψ t t.2)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

def dualOrder (S : Subalgebra R A)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Subalgebra R (CartierDual K A) where
  carrier := {φ | ∀ b ∈ S, φ b ∈ (algebraMap R K).range}
  mul_mem' {φ ψ} hφ hψ := by
    intro b hb
    rw [CartierDual.mul_apply]
    obtain ⟨z, hz⟩ := (AlgHom.mem_range _).mp (hcomul b hb)
    rw [← hz]
    exact dualDistrib_tensorSqHom_mem S φ ψ hφ hψ z
  one_mem' := by
    intro b hb
    rw [CartierDual.one_apply]
    exact hcounit b hb
  add_mem' {φ ψ} hφ hψ := by
    intro b hb
    rw [add_apply']
    exact add_mem (hφ b hb) (hψ b hb)
  zero_mem' := by
    intro b _
    rw [zero_apply']
    exact zero_mem _
  algebraMap_mem' r := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R K (CartierDual K A), CartierDual.algebraMap_apply]
    exact mul_mem (hcounit b hb) ⟨r, rfl⟩

end DualOrder

section Bases

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]

noncomputable def basisA (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} (b : Module.Basis ι R ↥S) : Module.Basis ι K A :=
  haveI := HopfOrder.moduleFlat_of_finite (K := K) S
  (Algebra.TensorProduct.basis K b).map (HopfOrder.baseChangeEquiv S hspan).toLinearEquiv

/--
@isnad1 id=eq.1h7v.s10.110df3c39f3b from=translated src=- shape=3401a8f1 vocab=a04678e5
-/
theorem basisA_apply (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} (b : Module.Basis ι R ↥S) (i : ι) :
    basisA S hspan b i = (b i : A) := by
  haveI := HopfOrder.moduleFlat_of_finite (K := K) S
  rw [basisA, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  show HopfOrder.baseChangeEquiv S hspan ((1 : K) ⊗ₜ[R] b i) = _
  rw [HopfOrder.baseChangeEquiv_tmul, one_smul]

/--
@isnad1 id=eq.1h8v.s11.c30931e85940 from=translated src=- shape=9044686b vocab=6b49d99d
-/
theorem basisA_repr_coe (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] (b : Module.Basis ι R ↥S) (s : ↥S) (i : ι) :
    (basisA S hspan b).repr (s : A) i = algebraMap R K (b.repr s i) := by
  classical

  let f : ↥S →ₗ[R] K := ((basisA S hspan b).coord i).restrictScalars R ∘ₗ (S.val.toLinearMap)
  let g : ↥S →ₗ[R] K := (Algebra.linearMap R K) ∘ₗ (b.coord i)
  have hfg : f = g := by
    apply b.ext
    intro j
    show (basisA S hspan b).repr (S.val (b j)) i = algebraMap R K (b.repr (b j) i)
    rw [Module.Basis.repr_self]
    have : S.val (b j) = basisA S hspan b j := by rw [basisA_apply]; rfl
    rw [this, Module.Basis.repr_self]
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  have := LinearMap.congr_fun hfg s
  simpa [f, g] using this

/--
@isnad1 id=mem.2h7v.s10.77e0f0570e72 from=translated src=- shape=d528e84f vocab=a52dbdb2
-/
theorem mem_of_forall_repr_mem (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Fintype ι] (b : Module.Basis ι R ↥S) (a : A)
    (h : ∀ i, (basisA S hspan b).repr a i ∈ (algebraMap R K).range) : a ∈ S := by
  choose r hr using h
  have ha : a = ∑ i, (basisA S hspan b).repr a i • basisA S hspan b i :=
    ((basisA S hspan b).sum_repr a).symm
  rw [ha]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [← hr i, algebraMap_smul, basisA_apply]
  exact Subalgebra.smul_mem _ (b i).2 _

variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

noncomputable def basisD (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) :
    Module.Basis ι K (CartierDual K A) :=
  ((basisA S hspan b).dualBasis).map (CartierDual.ofDual K A)

/--
@isnad1 id=eq.1h8v.s11.5ea6b760bfe8 from=translated src=- shape=bfdf68be vocab=a6a59d4b
-/
theorem basisD_apply_apply (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) (i : ι) (a : A) :
    basisD S hspan b i a = (basisA S hspan b).repr a i := by
  rw [basisD, Module.Basis.map_apply, CartierDual.ofDual_apply, Module.Basis.dualBasis_apply]

/--
@isnad1 id=mem.2h8v.s11.1db79d6cb06d from=translated src=- shape=2bb4f2e7 vocab=2bd318e9
-/
theorem basisD_mem (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) (i : ι) :
    ∀ s ∈ S, basisD S hspan b i s ∈ (algebraMap R K).range := by
  intro s hs
  rw [basisD_apply_apply]
  have := basisA_repr_coe S hspan b ⟨s, hs⟩ i
  exact ⟨_, this.symm⟩

end Bases

section DualIsOrder

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

variable (S : Subalgebra R A) (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)

end DualIsOrder

end S17Dual

namespace S17Dual

section Packaging

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

/--
@isnad1 id=mem.4h6v.s11.9dd2f263e7f1 from=translated src=- shape=5279e94e vocab=4dbc104b
-/
theorem childIII (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (S' : Subalgebra R (CartierDual K A))
    (hS' : ∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range)
    (a : A) (ha : ∀ φ ∈ S', φ a ∈ (algebraMap R K).range) : a ∈ S := by
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  let b := Module.Free.chooseBasis R ↥S
  apply mem_of_forall_repr_mem S hspan b a
  intro i
  rw [← basisD_apply_apply S hspan b i a]
  exact ha _ ((hS' _).mpr (basisD_mem S hspan b i))

end Packaging

end S17Dual

/--
@isnad1 id=mem.4h6v.s11.9dd2f263e7f1 from=translated src=- shape=5279e94e vocab=4dbc104b
-/
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (S' : Subalgebra R (CartierDual K A))
    (hS' : ∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range)
    (a : A) (ha : ∀ φ ∈ S', φ a ∈ (algebraMap R K).range) : a ∈ S :=
  S17Dual.childIII S hfin hspan S' hS' a ha
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
