import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace GaloisRep

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev inertiaField (A : ValuationSubring ℚ̄) : IntermediateField ℚ ℚ̄ :=
  IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)

/--
@isnad1 id=iff.0h2v.s9.c6250c591eaa from=translated src=- shape=cdfd2fe7 vocab=436d6d6b
-/
theorem mem_inertiaField_iff {A : ValuationSubring ℚ̄} {x : ℚ̄} :
    x ∈ inertiaField A ↔ ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x := by
  rw [inertiaField, IntermediateField.mem_fixedField_iff]

def inertiaRing (A : ValuationSubring ℚ̄) : Subring ℚ̄ := A.toSubring ⊓ (inertiaField A).toSubring

/--
@isnad1 id=iff.0h2v.s7.03acf6ced1e1 from=translated src=- shape=cfd1f3e5 vocab=22defca4
-/
theorem mem_inertiaRing_iff {A : ValuationSubring ℚ̄} {x : ℚ̄} :
    x ∈ inertiaRing A ↔ x ∈ A ∧ x ∈ inertiaField A := by
  rw [inertiaRing, Subring.mem_inf]
  exact Iff.rfl

namespace InertiaRing

variable (A : ValuationSubring ℚ̄)

variable {A} in

def mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x) : inertiaRing A :=
  ⟨x, GaloisRep.mem_inertiaRing_iff.mpr ⟨hxA, GaloisRep.mem_inertiaField_iff.mpr hfix⟩⟩

/--
@isnad1 id=eq.2h2v.s9.cb708926723d from=translated src=- shape=d5f95798 vocab=2dfa97be
-/
@[simp] theorem coe_mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x) :
    ((mkO x hxA hfix : inertiaRing A) : ℚ̄) = x := rfl

/--
@isnad1 id=mem.0h2v.s7.a38f9abb225c from=translated src=- shape=7201c105 vocab=e02d084d
-/
theorem coe_memA (x : inertiaRing A) : (x : ℚ̄) ∈ A := (GaloisRep.mem_inertiaRing_iff.mp x.2).1

/--
@isnad1 id=mem.0h2v.s7.26314b349626 from=translated src=- shape=ff52366e vocab=08e8cf35
-/
theorem coe_mem_inertiaField (x : inertiaRing A) : (x : ℚ̄) ∈ inertiaField A := (GaloisRep.mem_inertiaRing_iff.mp x.2).2

/--
@isnad1 id=eq.1h3v.s9.873d872c2e54 from=translated src=- shape=f6351f75 vocab=82ce4de4
-/
theorem coe_fixed (x : inertiaRing A) (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : σ (x : ℚ̄) = x :=
  GaloisRep.mem_inertiaField_iff.mp (coe_mem_inertiaField A x) σ hσ

/--
@isnad1 id=or.1h2v.s7.0f8359e79765 from=translated src=- shape=f98e30f3 vocab=d7d5b1dc
-/
theorem mem_or_inv_mem {x : ℚ̄} (hx : x ∈ inertiaField A) : x ∈ inertiaRing A ∨ x⁻¹ ∈ inertiaRing A := by
  rcases A.mem_or_inv_mem x with h | h
  · exact Or.inl (GaloisRep.mem_inertiaRing_iff.mpr ⟨h, hx⟩)
  · exact Or.inr (GaloisRep.mem_inertiaRing_iff.mpr ⟨h, IntermediateField.inv_mem _ hx⟩)

/--
@isnad1 id=not.1h2v.s9.84ee2cc271bd from=translated src=- shape=7e518638 vocab=c12bf773
-/
theorem not_isUnit_of_valuation_lt_one (x : inertiaRing A) (hx : A.valuation (x : ℚ̄) < 1) : ¬ IsUnit x := by
  rintro ⟨u, rfl⟩
  have h1 : ((u : inertiaRing A) : ℚ̄) * ((↑u⁻¹ : inertiaRing A) : ℚ̄) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  have hle : A.valuation ((↑u⁻¹ : inertiaRing A) : ℚ̄) ≤ 1 := (A.valuation_le_one_iff _).mpr (coe_memA A _)
  have hlt : A.valuation (((u : inertiaRing A) : ℚ̄) * ((↑u⁻¹ : inertiaRing A) : ℚ̄)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hx hle
  rw [h1, map_one] at hlt
  exact lt_irrefl _ hlt

instance instAlgebraField : Algebra (inertiaRing A) (inertiaField A) :=
  (({ toFun := fun x => ⟨(x : ℚ̄), coe_mem_inertiaField A x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl } : inertiaRing A →+* inertiaField A)).toAlgebra

/--
@isnad1 id=eq.0h2v.s11.f0579aba117e from=translated src=- shape=e1ec7d07 vocab=7e753f66
-/
theorem algebraMap_field_coe (x : inertiaRing A) : ((algebraMap (inertiaRing A) (inertiaField A) x : inertiaField A) : ℚ̄) = x := rfl

/--
@isnad1 id=isscalar.0h1v.s9.a3469323aec0 from=translated src=- shape=3cd05c7a vocab=b8f9762f
-/
instance instTowerField : IsScalarTower (inertiaRing A) (inertiaField A) ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end InertiaRing

end GaloisRep

end

section PointTransportSection

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
open WithConv

namespace GaloisRep.PointTransport

section LiftPt

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Algebra R H]

noncomputable def liftPt (φ : WithConv (H →ₐ[R] L)) : WithConv (S ⊗[R] H →ₐ[S] L) :=
  toConv (Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv fun _ _ => .all _ _)

/--
@isnad1 id=eq.0h7v.s9.3c97e1b647b1 from=translated src=- shape=87d4b6f9 vocab=e5a50c99
-/
theorem liftPt_tmul (φ : WithConv (H →ₐ[R] L)) (s : S) (h : H) :
    liftPt (S := S) φ (s ⊗ₜ[R] h) = algebraMap S L s * φ h := by
  show Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv (fun _ _ => .all _ _) (s ⊗ₜ[R] h) = _
  rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

/--
@isnad1 id=eq.0h6v.s9.1605b61fce10 from=translated src=- shape=775b730d vocab=b4568230
-/
theorem liftPt_one_tmul (φ : WithConv (H →ₐ[R] L)) (h : H) : liftPt (S := S) φ ((1 : S) ⊗ₜ[R] h) = φ h := by
  rw [liftPt_tmul, map_one, one_mul]

/--
@isnad1 id=injectiv.0h4v.s7.b8b8a5920a2a from=translated src=- shape=54287d96 vocab=457895cd
-/
theorem liftPt_injective : Function.Injective (liftPt (R := R) (S := S) (L := L) (H := H)) := by
  intro φ ψ h
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  have := congrArg (fun χ : WithConv (S ⊗[R] H →ₐ[S] L) => χ ((1 : S) ⊗ₜ[R] x)) h
  simpa only [liftPt_one_tmul] using this

/--
@isnad1 id=eq.0h6v.s9.2227cf3a6653 from=translated src=- shape=2e9f71f2 vocab=022227fe
-/
theorem comp_liftPt (σ : L →ₐ[S] L) (φ : WithConv (H →ₐ[R] L)) :
    σ.comp (liftPt (S := S) φ).ofConv = (liftPt (S := S) (toConv ((σ.restrictScalars R).comp φ.ofConv))).ofConv := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [AlgHom.comp_apply]
    show σ (liftPt (S := S) φ (s ⊗ₜ[R] h)) = liftPt (S := S) (toConv ((σ.restrictScalars R).comp φ.ofConv)) (s ⊗ₜ[R] h)
    rw [liftPt_tmul, liftPt_tmul, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end LiftPt

section LiftPtConv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

/--
@isnad1 id=eq.0h6v.s10.f85dceb9075e from=translated src=- shape=7b6060f0 vocab=ba4905bf
-/
theorem liftPt_mul (φ ψ : WithConv (H →ₐ[R] L)) :
    liftPt (S := S) (φ * ψ) = liftPt (S := S) φ * liftPt (S := S) ψ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (φ * ψ) x = (liftPt (S := S) φ * liftPt (S := S) ψ) x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    let rr := Coalgebra.Repr.arbitrary R h
    have hco : Coalgebra.comul (R := S) (s ⊗ₜ[R] h)
        = ∑ i ∈ rr.index, ((1 : S) ⊗ₜ[R] rr.left i) ⊗ₜ[S] (s ⊗ₜ[R] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rw [liftPt_tmul, AlgHom.convMul_apply, AlgHom.convMul_apply, ← rr.eq, map_sum, Finset.mul_sum, hco, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    show algebraMap S L s * (φ.ofConv (rr.left i) * ψ.ofConv (rr.right i))
      = liftPt (S := S) φ ((1 : S) ⊗ₜ[R] rr.left i) * liftPt (S := S) ψ (s ⊗ₜ[R] rr.right i)
    rw [liftPt_one_tmul, liftPt_tmul]
    show _ = φ.ofConv (rr.left i) * (algebraMap S L s * ψ.ofConv (rr.right i))
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/--
@isnad1 id=eq.0h4v.s9.2ebfadc42eb2 from=translated src=- shape=e72b0f89 vocab=a4138a0f
-/
theorem liftPt_one : liftPt (S := S) (1 : WithConv (H →ₐ[R] L)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (1 : WithConv (H →ₐ[R] L)) x = (1 : WithConv (S ⊗[R] H →ₐ[S] L)) x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [liftPt_tmul, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/--
@isnad1 id=eq.0h6v.s9.000a5ceafeab from=translated src=- shape=aaa67c12 vocab=f5fe56ea
-/
theorem liftPt_pow (φ : WithConv (H →ₐ[R] L)) (n : ℕ) : liftPt (S := S) (φ ^ n) = liftPt (S := S) φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, liftPt_one]
  | succ n ih => rw [pow_succ, pow_succ, liftPt_mul, ih]

end LiftPtConv

section EvGen

variable (K : Type*) (L : Type*) (B : Type*) [CommRing K] [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]

variable {K L B}
variable {S : Type*} [CommRing S] [Algebra K S] [Algebra S L] [IsScalarTower K S L]

/--
@isnad1 id=surjecti.0h4v.s7.af2e6d917a71 from=translated src=- shape=715e8e99 vocab=4466f687
-/
theorem liftPt_surjective : Function.Surjective (liftPt (R := K) (S := S) (L := L) (H := B)) := by
  intro ψ
  refine ⟨toConv (((ψ.ofConv).restrictScalars K).comp Algebra.TensorProduct.includeRight), ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (toConv (((ψ.ofConv).restrictScalars K).comp Algebra.TensorProduct.includeRight)) x = ψ.ofConv x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s b =>
    rw [liftPt_tmul]
    show algebraMap S L s * ψ.ofConv ((1 : S) ⊗ₜ[K] b) = ψ.ofConv (s ⊗ₜ[K] b)
    rw [← ψ.ofConv.commutes s, ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

noncomputable def liftPtEquiv : WithConv (B →ₐ[K] L) ≃ WithConv (S ⊗[K] B →ₐ[S] L) :=
  Equiv.ofBijective (liftPt (S := S)) ⟨liftPt_injective, liftPt_surjective⟩

/--
@isnad1 id=eq.0h5v.s9.fc3e55c63c5c from=translated src=- shape=505f8514 vocab=d80c3b3c
-/
@[simp] theorem liftPtEquiv_apply (φ : WithConv (B →ₐ[K] L)) : liftPtEquiv (S := S) φ = liftPt (S := S) φ := rfl

/--
@isnad1 id=finite.0h4v.s7.288830d2f4a4 from=translated src=- shape=6ea7219c vocab=644f9c74
-/
theorem finite_pts_baseChange [Finite (WithConv (B →ₐ[K] L))] : Finite (WithConv (S ⊗[K] B →ₐ[S] L)) :=
  Finite.of_surjective _ liftPt_surjective

end EvGen

section LiftPtMulEquiv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

noncomputable def liftPtMulEquiv : WithConv (H →ₐ[R] L) ≃* WithConv (S ⊗[R] H →ₐ[S] L) :=
  { liftPtEquiv (K := R) (L := L) (B := H) (S := S) with map_mul' := liftPt_mul }

/--
@isnad1 id=eq.0h5v.s10.c54d97e50089 from=translated src=- shape=0084ae21 vocab=d4808ad6
-/
@[simp] theorem liftPtMulEquiv_apply (φ : WithConv (H →ₐ[R] L)) :
    liftPtMulEquiv (S := S) φ = liftPt (S := S) φ := rfl

/--
@isnad1 id=eq.0h5v.s11.2d1b8db5a245 from=translated src=- shape=7f62474c vocab=86e5fbb0
-/
theorem liftPtMulEquiv_symm_apply (ψ : WithConv (S ⊗[R] H →ₐ[S] L)) :
    (liftPtMulEquiv (S := S)).symm ψ = (liftPtEquiv (S := S)).symm ψ := rfl

end LiftPtMulEquiv

section Valuative

variable {R S L H : Type*} [CommRing R] [CommRing S] [Field L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

/--
@isnad1 id=lt.2h8v.s11.1983b66186a6 from=translated src=- shape=8931e91b vocab=5a5e587c
-/
theorem valuation_liftPt_sub_lt_one (hS : ∀ s : S, v (algebraMap S L s) ≤ 1)
    (φ : WithConv (H →ₐ[R] L)) (hφ : ∀ h : H, v (φ h - algebraMap R L (Coalgebra.counit (R := R) h)) < 1)
    (x : S ⊗[R] H) :
    v (liftPt (S := S) φ x - algebraMap S L (Coalgebra.counit (R := S) x)) < 1 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, sub_zero, map_zero]; exact zero_lt_one
  | tmul s h =>
    rw [liftPt_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_comm (algebraMap R L _), ← mul_sub, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hS s) zero_le (hφ h)
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    have : liftPt (S := S) φ x + liftPt (S := S) φ y - (algebraMap S L (Coalgebra.counit (R := S) x)
        + algebraMap S L (Coalgebra.counit (R := S) y))
        = (liftPt (S := S) φ x - algebraMap S L (Coalgebra.counit (R := S) x))
          + (liftPt (S := S) φ y - algebraMap S L (Coalgebra.counit (R := S) y)) := by ring
    rw [this]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt hx hy)

end Valuative

end GaloisRep.PointTransport

noncomputable section

namespace GaloisRep.InertiaRing

section Dec

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)

/--
@isnad1 id=eq.0h2v.s9.02e5c7b91e66 from=translated src=- shape=c4c8a914 vocab=a586b98f
-/
theorem algebraMap_O_apply (z : GaloisRep.inertiaRing A) : algebraMap (GaloisRep.inertiaRing A) ℚ̄ z = (z : ℚ̄) := rfl

/--
@isnad1 id=injectiv.0h1v.s9.27e9e728d9e5 from=translated src=- shape=47a2c244 vocab=e42a193d
-/
theorem algebraMap_O_injective : Function.Injective (algebraMap (GaloisRep.inertiaRing A) ℚ̄) := Subtype.val_injective

/--
@isnad1 id=le.0h2v.s10.7efd27df8dfe from=translated src=- shape=b747fa40 vocab=22d3dfbf
-/
theorem valuation_algebraMap_O_le_one (z : GaloisRep.inertiaRing A) : A.valuation (algebraMap (GaloisRep.inertiaRing A) ℚ̄ z) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (GaloisRep.InertiaRing.coe_memA A z)

noncomputable def galF {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : ℚ̄ ≃ₐ[GaloisRep.inertiaField A] ℚ̄ :=
  { σ with commutes' := fun x => GaloisRep.mem_inertiaField_iff.mp x.2 σ hσ }

/--
@isnad1 id=eq.1h3v.s10.165655b230fd from=translated src=- shape=0f0b7f39 vocab=02ba30a2
-/
@[simp] theorem galF_apply {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : ℚ̄) : galF A hσ x = σ x := rfl

noncomputable def rhoI (σ : A.inertiaSubgroupIn ℚ) : ℚ̄ ≃ₐ[GaloisRep.inertiaField A] ℚ̄ := galF A σ.2

/--
@isnad1 id=eq.0h3v.s10.383633148c21 from=translated src=- shape=c0889c06 vocab=bc966155
-/
@[simp] theorem rhoI_apply (σ : A.inertiaSubgroupIn ℚ) (x : ℚ̄) : rhoI A σ x = (σ : Gal) x := rfl

/--
@isnad1 id=mem.1h2v.s11.318c8098de94 from=translated src=- shape=3c762b5e vocab=5a85b306
-/
theorem hfix_I (c : ℚ̄) (hc : ∀ σ : A.inertiaSubgroupIn ℚ, rhoI A σ c = c) :
    c ∈ Set.range (algebraMap (GaloisRep.inertiaField A) ℚ̄) :=
  ⟨⟨c, GaloisRep.mem_inertiaField_iff.mpr fun σ hσ => hc ⟨σ, hσ⟩⟩, rfl⟩

noncomputable def galO {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : ℚ̄ →ₐ[GaloisRep.inertiaRing A] ℚ̄ :=
  { (σ : ℚ̄ →+* ℚ̄) with commutes' := fun z => GaloisRep.InertiaRing.coe_fixed A z σ hσ }

/--
@isnad1 id=eq.1h3v.s10.d686bfcefbdf from=translated src=- shape=07987078 vocab=c4f64552
-/
@[simp] theorem galO_apply {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : ℚ̄) : galO A hσ x = σ x := rfl

/--
@isnad1 id=eq.3h5v.s10.f783989b1ee2 from=translated src=- shape=cb57d7f6 vocab=64fc08e1
-/
theorem galF_hn {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {N n : ℕ}
    (hn : ∀ ζ : ℚ̄, ζ ^ N = 1 → σ ζ = ζ ^ n) : ∀ ζ : ℚ̄, ζ ^ N = 1 → galF A hσ ζ = ζ ^ n := hn

/--
@isnad1 id=iff.1h4v.s10.92b9c60d51fb from=translated src=- shape=b01126e6 vocab=02ba30a2
-/
theorem galF_fix_iff {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {X : Type*} (f : X → ℚ̄) :
    (∀ x, galF A hσ (f x) = f x) ↔ ∀ x, σ (f x) = f x := Iff.rfl

/--
@isnad1 id=iff.1h5v.s10.bca60f42d9c0 from=translated src=- shape=f00c0817 vocab=02ba30a2
-/
theorem galF_comp_iff {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {X : Type*} (f g : X → ℚ̄) :
    (∀ x, g x = galF A hσ (f x)) ↔ ∀ x, g x = σ (f x) := Iff.rfl

/--
@isnad1 id=eq.1h2v.s10.692cb3d1319e from=translated src=- shape=51ffacd0 vocab=db21d45c
-/
theorem galF_restrictScalars {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    ((galF A hσ : ℚ̄ →ₐ[GaloisRep.inertiaField A] ℚ̄).restrictScalars (GaloisRep.inertiaRing A)) = galO A hσ :=
  AlgHom.ext fun _ => rfl

variable (q : ℕ) [Fact q.Prime]

/--
@isnad1 id=mem.2h3v.s7.55ebaebbc765 from=translated src=- shape=e6407e36 vocab=c346e65e
-/
theorem ratCast_mem_of_coprime (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) {r : ℚ} (hr : r.den.Coprime q) : (r : ℚ̄) ∈ A := by
  have hq : q.Prime := Fact.out
  have hden : A.valuation ((r.den : ℚ̄)) = 1 := by
    have hle : A.valuation ((r.den : ℚ̄)) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A r.den)
    refine le_antisymm hle (not_lt.mp fun hlt => ?_)
    have hq1 : A.valuation ((q : ℚ̄)) < 1 := (A.mem_nonunits_iff).mp hA
    have hg := Nat.gcd_eq_gcd_ab r.den q
    rw [Nat.Coprime.gcd_eq_one hr, Nat.cast_one] at hg
    have h1 : (1 : ℚ̄) = (r.den : ℚ̄) * (Nat.gcdA r.den q : ℚ̄) + (q : ℚ̄) * (Nat.gcdB r.den q : ℚ̄) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ̄)) hg
    have hlt' : A.valuation 1 < 1 := by
      rw [h1]
      refine lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hq1 ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
    rw [map_one] at hlt'
    exact lt_irrefl _ hlt'
  have hden0 : (r.den : ℚ̄) ≠ 0 := by exact_mod_cast r.den_nz
  rw [← A.valuation_le_one_iff, Rat.cast_def, map_div₀, hden, div_one]
  exact (A.valuation_le_one_iff _).mpr (intCast_mem A r.num)

@[reducible] noncomputable def algebraRO (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) :
    Algebra (GaloisRep.ratLocalizedAt q) (GaloisRep.inertiaRing A) :=
  RingHom.toAlgebra
    { toFun := fun r => GaloisRep.InertiaRing.mkO (((r : ℚ) : ℚ̄)) (ratCast_mem_of_coprime A q hA r.2)
        (fun σ _ => by rw [← eq_ratCast (algebraMap ℚ ℚ̄), AlgEquiv.commutes])
      map_one' := Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_one]; push_cast; try rfl)
      map_mul' := fun a b => Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_mul]; push_cast; try rfl)
      map_zero' := Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_zero]; push_cast; try rfl)
      map_add' := fun a b => Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_add]; push_cast; try rfl) }

/--
@isnad1 id=eq.1h3v.s10.441d49f324dc from=translated src=- shape=c9bad313 vocab=e59ed468
-/
theorem algebraMap_RO_coe (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) (r : GaloisRep.ratLocalizedAt q) :
    letI := algebraRO A q hA
    ((algebraMap (GaloisRep.ratLocalizedAt q) (GaloisRep.inertiaRing A) r : GaloisRep.inertiaRing A) : ℚ̄) = ((r : ℚ) : ℚ̄) := rfl

/--
@isnad1 id=isscalar.1h2v.s9.5c5d53fcd048 from=translated src=- shape=8adf9e1e vocab=938b97bc
-/
theorem towerROQbar (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) :
    letI := algebraRO A q hA
    IsScalarTower (GaloisRep.ratLocalizedAt q) (GaloisRep.inertiaRing A) ℚ̄ := by
  letI := algebraRO A q hA
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [algebraMap_O_apply, algebraMap_RO_coe]
  show algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ r = ((r : ℚ) : ℚ̄)
  rw [IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt q) ℚ ℚ̄, eq_ratCast]
  rfl

end Dec

section T1

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)
variable {S : Type*} [CommRing S] [Bialgebra (GaloisRep.inertiaRing A) S] [Module.Finite (GaloisRep.inertiaRing A) S]

/--
@isnad1 id=mem.0h4v.s10.fd63e8298bd1 from=translated src=- shape=47b77b01 vocab=524bfd76
-/
theorem apply_mem_A (ψ : S →ₐ[GaloisRep.inertiaRing A] ℚ̄) (s : S) : ψ s ∈ A := by
  have h1 : IsIntegral (GaloisRep.inertiaRing A) (ψ s) := (Algebra.IsIntegral.isIntegral s).map ψ
  obtain ⟨p, hpm, hpe⟩ := h1
  let j : GaloisRep.inertiaRing A →+* A :=
    { toFun := fun z => ⟨(z : ℚ̄), GaloisRep.InertiaRing.coe_memA A z⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hj : (algebraMap A ℚ̄).comp j = algebraMap (GaloisRep.inertiaRing A) ℚ̄ := RingHom.ext fun _ => rfl
  have h2 : IsIntegral A (ψ s) := by
    refine ⟨p.map j, hpm.map j, ?_⟩
    rw [Polynomial.eval₂_map, hj]
    exact hpe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

noncomputable def toQbarPt (x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) :
    WithConv (S →ₐ[GaloisRep.inertiaRing A] ℚ̄) :=
  toConv ((Algebra.ofId (GaloisRep.inertiaRing A) ℚ̄).comp x.ofConv)

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
/--
@isnad1 id=eq.0h4v.s12.d7918ea0b26b from=translated src=- shape=fe33b72d vocab=51e01c3e
-/
theorem toQbarPt_apply (x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) (s : S) :
    toQbarPt A x s = algebraMap (GaloisRep.inertiaRing A) ℚ̄ (x s) := rfl

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
/--
@isnad1 id=eq.0h4v.s12.2b8f02eaffe2 from=translated src=- shape=3b601d72 vocab=693df456
-/
theorem toQbarPt_mul (x y : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) :
    toQbarPt A (x * y) = toQbarPt A x * toQbarPt A y := by
  unfold toQbarPt
  rw [AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv]

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
/--
@isnad1 id=eq.0h2v.s11.3d9085b27ca7 from=translated src=- shape=6788532b vocab=300c87b1
-/
theorem toQbarPt_one : toQbarPt A (1 : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro s
  show algebraMap (GaloisRep.inertiaRing A) ℚ̄ ((1 : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) s)
    = (1 : WithConv (S →ₐ[GaloisRep.inertiaRing A] ℚ̄)) s
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  rfl

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
/--
@isnad1 id=eq.0h4v.s12.b52ce85b852a from=translated src=- shape=63e35400 vocab=ef6215dc
-/
theorem toQbarPt_pow (x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) (n : ℕ) :
    toQbarPt A (x ^ n) = toQbarPt A x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toQbarPt_one]
  | succ n ih => rw [pow_succ, pow_succ, toQbarPt_mul, ih]

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
/--
@isnad1 id=injectiv.0h2v.s9.ad4b9be12746 from=translated src=- shape=dcb0409d vocab=8f91a27f
-/
theorem toQbarPt_injective : Function.Injective (toQbarPt A (S := S)) := by
  intro x y h
  apply WithConv.ext
  apply AlgHom.ext
  intro s
  apply algebraMap_O_injective A
  rw [← toQbarPt_apply, ← toQbarPt_apply, h]

/--
@isnad1 id=ex.1h3v.s14.2675477a38c0 from=translated src=- shape=6583b8a4 vocab=d534f47e
-/
theorem exists_OPt_of_fixed [IsLocalRing (GaloisRep.inertiaRing A)] (ψ : WithConv (S →ₐ[GaloisRep.inertiaRing A] ℚ̄))
    (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → ∀ s : S, σ (ψ s) = ψ s) :
    ∃ x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A),
      toQbarPt A x = ψ ∧
      (∀ s, algebraMap (GaloisRep.inertiaRing A) ℚ̄ (x s) = ψ s) ∧
      (∀ k : ℕ, ψ ^ k = 1 ↔ x ^ k = 1) ∧
      ((∀ s, A.valuation (ψ s - algebraMap (GaloisRep.inertiaRing A) ℚ̄ (Coalgebra.counit (R := GaloisRep.inertiaRing A) s)) < 1) →
        ∀ s, x s - algebraMap (GaloisRep.inertiaRing A) (GaloisRep.inertiaRing A) (Coalgebra.counit (R := GaloisRep.inertiaRing A) s)
          ∈ IsLocalRing.maximalIdeal (GaloisRep.inertiaRing A)) := by
  let x₀ : S → GaloisRep.inertiaRing A := fun s => GaloisRep.InertiaRing.mkO (ψ s) (apply_mem_A A ψ.ofConv s) (fun σ hσ => hfix σ hσ s)
  have hx₀ : ∀ s, ((x₀ s : GaloisRep.inertiaRing A) : ℚ̄) = ψ s := fun s => rfl
  let xa : S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A :=
    { toFun := x₀
      map_one' := Subtype.ext (by rw [hx₀]; exact map_one ψ.ofConv)
      map_mul' := fun a b => Subtype.ext (by rw [hx₀, Subring.coe_mul, hx₀, hx₀]; exact map_mul ψ.ofConv a b)
      map_zero' := Subtype.ext (by rw [hx₀]; exact map_zero ψ.ofConv)
      map_add' := fun a b => Subtype.ext (by rw [hx₀, Subring.coe_add, hx₀, hx₀]; exact map_add ψ.ofConv a b)
      commutes' := fun z => Subtype.ext (by rw [hx₀]; exact ψ.ofConv.commutes z) }
  refine ⟨toConv xa, ?_, fun s => rfl, fun k => ?_, fun hred s => ?_⟩
  · exact WithConv.ext (AlgHom.ext fun s => rfl)
  · have hψ : toQbarPt A (toConv xa) = ψ := WithConv.ext (AlgHom.ext fun s => rfl)
    constructor
    · intro h
      apply toQbarPt_injective A
      rw [toQbarPt_pow, hψ, h, toQbarPt_one]
    · intro h
      rw [← hψ, ← toQbarPt_pow, h, toQbarPt_one]
  · apply (IsLocalRing.mem_maximalIdeal _).mpr
    apply GaloisRep.InertiaRing.not_isUnit_of_valuation_lt_one
    have hid : ∀ y : GaloisRep.inertiaRing A, algebraMap (GaloisRep.inertiaRing A) (GaloisRep.inertiaRing A) y = y := fun _ => rfl
    rw [hid, AddSubgroupClass.coe_sub]
    exact hred s

end T1

end GaloisRep.InertiaRing

end

end PointTransportSection
