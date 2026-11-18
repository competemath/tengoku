import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfOrderData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_exists_dual_hopfOrder.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfOrder_exists_dual_hopfOrder

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

/--
@isnad1 id=iff.2h5v.s13.64c12ce8f878 from=translated src=- shape=44d0efa2 vocab=fe2183eb
-/
theorem mem_dualOrder_iff (S : Subalgebra R A)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (φ : CartierDual K A) :
    φ ∈ dualOrder S hcomul hcounit ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range := Iff.rfl

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
@isnad1 id=eq.1h7v.s10.050452906545 from=translated src=- shape=3401a8f1 vocab=f15d8e9b
-/
theorem basisA_apply (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} (b : Module.Basis ι R ↥S) (i : ι) :
    basisA S hspan b i = (b i : A) := by
  haveI := HopfOrder.moduleFlat_of_finite (K := K) S
  rw [basisA, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  show HopfOrder.baseChangeEquiv S hspan ((1 : K) ⊗ₜ[R] b i) = _
  rw [HopfOrder.baseChangeEquiv_tmul, one_smul]

/--
@isnad1 id=eq.1h8v.s11.33679d7aec2e from=translated src=- shape=9044686b vocab=5e030444
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

variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

noncomputable def basisD (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) :
    Module.Basis ι K (CartierDual K A) :=
  ((basisA S hspan b).dualBasis).map (CartierDual.ofDual K A)

/--
@isnad1 id=eq.1h8v.s11.27ed2428be25 from=translated src=- shape=bfdf68be vocab=bed25492
-/
theorem basisD_apply_apply (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) (i : ι) (a : A) :
    basisD S hspan b i a = (basisA S hspan b).repr a i := by
  rw [basisD, Module.Basis.map_apply, CartierDual.ofDual_apply, Module.Basis.dualBasis_apply]

/--
@isnad1 id=eq.1h8v.s11.83c96dc9b9b3 from=translated src=- shape=b7205b63 vocab=c8f78f16
-/
theorem basisD_repr (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S)
    (φ : CartierDual K A) (i : ι) :
    (basisD S hspan b).repr φ i = φ (b i : A) := by
  rw [basisD, Module.Basis.map_repr, LinearEquiv.trans_apply, Module.Basis.dualBasis_repr, basisA_apply]
  rfl

/--
@isnad1 id=mem.2h8v.s11.476464e41888 from=translated src=- shape=2bb4f2e7 vocab=a8da10db
-/
theorem basisD_mem (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) (i : ι) :
    ∀ s ∈ S, basisD S hspan b i s ∈ (algebraMap R K).range := by
  intro s hs
  rw [basisD_apply_apply]
  have := basisA_repr_coe S hspan b ⟨s, hs⟩ i
  exact ⟨_, this.symm⟩

/--
@isnad1 id=mem.2h7v.s11.3e920f69bd2f from=translated src=- shape=582271c9 vocab=2f6bc814
-/
theorem mem_span_basisD (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R ↥S)
    (φ : CartierDual K A) (hφ : ∀ s ∈ S, φ s ∈ (algebraMap R K).range) :
    φ ∈ Submodule.span R (Set.range (basisD S hspan b)) := by
  have hφ' : φ = ∑ i, (basisD S hspan b).repr φ i • basisD S hspan b i := ((basisD S hspan b).sum_repr φ).symm
  rw [hφ']
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨r, hr⟩ := hφ (b i : A) (b i).2
  rw [basisD_repr, ← hr, algebraMap_smul]
  exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)

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

/--
@isnad1 id=eq.3h6v.s13.5ae44c925a48 from=translated src=- shape=6ce61476 vocab=a289a86d
-/
theorem toSubmodule_dualOrder_eq [Module.Finite R ↥S] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) :
    Subalgebra.toSubmodule (dualOrder S hcomul hcounit) = Submodule.span R (Set.range (basisD S hspan b)) := by
  apply le_antisymm
  · intro φ hφ
    exact mem_span_basisD S hspan _ φ hφ
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact basisD_mem S hspan _ i

include hfin hspan in
/--
@isnad1 id=finite.4h4v.s13.7624856994e4 from=translated src=- shape=8e1c2b1d vocab=8124b127
-/
theorem finite_dualOrder : Module.Finite R ↥(dualOrder S hcomul hcounit) := by
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  have hfg : (Subalgebra.toSubmodule (dualOrder S hcomul hcounit)).FG := by
    rw [toSubmodule_dualOrder_eq S hspan hcomul hcounit (Module.Free.chooseBasis R ↥S)]
    exact Submodule.fg_span (Set.finite_range _)
  exact Module.Finite.iff_fg.mpr hfg

include hfin hspan in
/--
@isnad1 id=eq.4h4v.s13.f7319418371a from=translated src=- shape=dc9c0eac vocab=8124b127
-/
theorem span_dualOrder : Submodule.span K ((dualOrder S hcomul hcounit : Subalgebra R (CartierDual K A)) :
    Set (CartierDual K A)) = ⊤ := by
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  apply eq_top_iff.mpr
  exact (basisD S hspan (Module.Free.chooseBasis R ↥S)).span_eq.ge.trans
    (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact basisD_mem S hspan _ i))

/--
@isnad1 id=mem.3h5v.s13.311bb103f521 from=translated src=- shape=b9b849da vocab=72e13557
-/
theorem counit_dualOrder : ∀ φ ∈ dualOrder S hcomul hcounit,
    Coalgebra.counit (R := K) (A := CartierDual K A) φ ∈ (algebraMap R K).range := by
  intro φ hφ
  rw [CartierDual.counit_apply]
  exact hφ 1 S.one_mem

include hanti in
/--
@isnad1 id=mem.4h5v.s13.e4ee2904ff1c from=translated src=- shape=a0e3279c vocab=5e49d1d1
-/
theorem antipode_dualOrder : ∀ φ ∈ dualOrder S hcomul hcounit,
    HopfAlgebra.antipode K (A := CartierDual K A) φ ∈ dualOrder S hcomul hcounit := by
  intro φ hφ b hb
  rw [CartierDual.antipode_apply]
  exact hφ _ (hanti b hb)

/--
@isnad1 id=eq.1h9v.s14.eff696498dce from=translated src=- shape=4851a5cb vocab=6cd2460a
-/
theorem tensor_repr_eq_pairing {ι : Type*} [Fintype ι] [DecidableEq ι] [Module.Finite R ↥S] (b : Module.Basis ι R ↥S)
    (w : CartierDual K A ⊗[K] CartierDual K A) (i j : ι) :
    ((basisD S hspan b).tensorProduct (basisD S hspan b)).repr w (i, j) =
      TensorProduct.dualDistrib K A A
        (TensorProduct.map (CartierDual.toDual K A).toLinearMap (CartierDual.toDual K A).toLinearMap w)
        (basisA S hspan b i ⊗ₜ[K] basisA S hspan b j) := by
  induction w with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, LinearMap.add_apply]
  | tmul φ ψ =>
      rw [Module.Basis.tensorProduct_repr_tmul_apply, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
      simp only [LinearEquiv.coe_coe, CartierDual.toDual_apply, basisD_repr, basisA_apply, smul_eq_mul]
      exact mul_comm _ _

include hfin hspan in
/--
@isnad1 id=mem.5h5v.s15.9b2e5af3f5d0 from=translated src=- shape=7feed181 vocab=8124b127
-/
theorem comul_dualOrder : ∀ φ ∈ dualOrder S hcomul hcounit, Coalgebra.comul (R := K) φ ∈
    (Algebra.TensorProduct.productMap
      (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp
        (dualOrder S hcomul hcounit).val)
      (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp
        (dualOrder S hcomul hcounit).val)).range := by
  intro φ hφ
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  let b := Module.Free.chooseBasis R ↥S
  let β := (basisD S hspan b).tensorProduct (basisD S hspan b)
  set w := Coalgebra.comul (R := K) φ with hw

  have hcoord : ∀ ij : _ × _, β.repr w ij ∈ (algebraMap R K).range := by
    rintro ⟨i, j⟩
    have h1 : β.repr w (i, j) = φ ((b i : A) * (b j : A)) := by
      refine (tensor_repr_eq_pairing S hspan b w i j).trans ?_
      rw [hw]
      refine (CartierDual.comul_pairing φ _ _).trans ?_
      rw [basisA_apply, basisA_apply]
    rw [h1]
    exact hφ _ (S.mul_mem (b i).2 (b j).2)
  choose r hr using hcoord
  have hw' : w = ∑ ij, β.repr w ij • β ij := (β.sum_repr w).symm
  rw [hw']
  refine Subalgebra.sum_mem _ fun ij _ => ?_
  obtain ⟨i, j⟩ := ij
  rw [← hr, algebraMap_smul, Module.Basis.tensorProduct_apply]
  refine Subalgebra.smul_mem _ ?_ _
  exact (AlgHom.mem_range _).mpr
    ⟨(⟨basisD S hspan b i, basisD_mem S hspan b i⟩ : ↥(dualOrder S hcomul hcounit)) ⊗ₜ[R]
      (⟨basisD S hspan b j, basisD_mem S hspan b j⟩ : ↥(dualOrder S hcomul hcounit)),
     HopfOrder.tensorSqHom_tmul (K := K) (dualOrder S hcomul hcounit) _ _⟩

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
@isnad1 id=ex.5h4v.s15.3fdbbacd11e9 from=translated src=- shape=11be0b23 vocab=f539cb74
-/
theorem childI (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ S' : Subalgebra R (CartierDual K A),
      (∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range) ∧
      Module.Finite R ↥S' ∧ Submodule.span K (S' : Set (CartierDual K A)) = ⊤ ∧
      (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)).range) ∧
      (∀ x ∈ S', HopfAlgebra.antipode K (A := CartierDual K A) x ∈ S') ∧
      (∀ x ∈ S', Coalgebra.counit (R := K) (A := CartierDual K A) x ∈ (algebraMap R K).range) :=
  ⟨dualOrder S hcomul hcounit, mem_dualOrder_iff S hcomul hcounit, finite_dualOrder S hfin hspan hcomul hcounit,
    span_dualOrder S hfin hspan hcomul hcounit, comul_dualOrder S hfin hspan hcomul hcounit,
    antipode_dualOrder S hcomul hanti hcounit, counit_dualOrder S hcomul hcounit⟩

end Packaging

end S17Dual

/--
@isnad1 id=ex.5h4v.s15.3fdbbacd11e9 from=translated src=- shape=11be0b23 vocab=f539cb74
-/
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ S' : Subalgebra R (CartierDual K A),
      (∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range) ∧
      Module.Finite R ↥S' ∧ Submodule.span K (S' : Set (CartierDual K A)) = ⊤ ∧
      (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)).range) ∧
      (∀ x ∈ S', HopfAlgebra.antipode K (A := CartierDual K A) x ∈ S') ∧
      (∀ x ∈ S', Coalgebra.counit (R := K) (A := CartierDual K A) x ∈ (algebraMap R K).range) :=
  S17Dual.childI S hfin hspan hcomul hanti hcounit
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
