import Tengoku.Seed.RingTheory.AdicCompletion.Completeness
import Tengoku.Seed.RingTheory.AdicCompletion.LocalRing
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.Noetherian.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AdicCompletion.ker_evalₐ_eq_map_pow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AdicCompletion.isUnit_one_add_of_mem_map` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AdicCompletion.instIsLocalRingMaximalIdeal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AdicCompletion.maximalIdeal_eq_map` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AdicCompletion.quotientMaximalIdealPowAlgEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AdicCompletion.maximalIdeal_eq_map_algEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AdicCompletion.quotientMaximalIdealPowAlgEquivOfAlgEquiv` (it only prints; the queue checks the axioms of every declaration). -/

set_option autoImplicit false

open IsLocalRing

namespace AdicCompletion

variable {A : Type*} [CommRing A]

section Kernel

variable (I : Ideal A)

/--
@isnad1 id=iff.0h4v.s11.5580d0770a61 from=translated src=- shape=1c5b0d41 vocab=ac06bf84
-/
theorem mem_ker_evalₐ_iff (n : ℕ) (x : AdicCompletion I A) :
    x ∈ RingHom.ker (evalₐ I n) ↔ x ∈ LinearMap.ker (eval I A n) := by
  have h : (I ^ n • ⊤ : Ideal A) = I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx; rw [← factor_evalₐ_eq_eval I x h.ge, hx]; exact RingHom.map_zero _
  · intro hx; rw [← factor_eval_eq_evalₐ I x h.le, hx]; exact LinearMap.map_zero _

/--
@isnad1 id=eq.1h3v.s10.17143d0bd23a from=translated src=- shape=4c8b1532 vocab=f6c8831a
-/
theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem]

/--
@isnad1 id=isunit.2h3v.s9.bc61d4417857 from=translated src=- shape=68e233ab vocab=f274d3cb
-/
theorem isUnit_one_add_of_mem_map (hI : I.FG) {x : AdicCompletion I A}
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (1 + x) := by
  haveI : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I A)).mpr (isAdicComplete hI)
  have h := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _ hx) 1
  rwa [mul_one, add_comm] at h

end Kernel

section Local

variable [IsLocalRing A]

variable [IsNoetherianRing A]

/--
@isnad1 id=fg.0h1v.s5.23e7f0a3508c from=translated src=- shape=456cb356 vocab=0bb98ca8
-/
theorem maximalIdeal_fg : (maximalIdeal A).FG := IsNoetherian.noetherian _

/--
@isnad1 id=islocalr.0h1v.s6.2a7a3d0dbba6 from=translated src=- shape=368cb636 vocab=fae34159
-/
instance instIsLocalRingMaximalIdeal : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
  isLocalRing_of_fg maximalIdeal_fg

/--
@isnad1 id=eq.0h2v.s10.364782b4538b from=translated src=- shape=a28e570e vocab=34cc96ef
-/
theorem maximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n = RingHom.ker (evalₐ (maximalIdeal A) n) := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow, ker_evalₐ_eq_map_pow _ maximalIdeal_fg]

/--
@isnad1 id=eq.0h1v.s9.e4e24fed8350 from=translated src=- shape=008947e9 vocab=34cc96ef
-/
theorem maximalIdeal_eq_ker_evalₐ_one :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) = RingHom.ker (evalₐ (maximalIdeal A) 1) := by
  rw [← maximalIdeal_pow_eq_ker_evalₐ, pow_one]

/--
@isnad1 id=iff.0h2v.s10.c3795976de21 from=translated src=- shape=59402647 vocab=e8c0f777
-/
theorem mem_maximalIdeal_iff (x : AdicCompletion (maximalIdeal A) A) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ↔ evalₐ (maximalIdeal A) 1 x = 0 := by
  rw [maximalIdeal_eq_ker_evalₐ_one, RingHom.mem_ker]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k A]

noncomputable def quotientMaximalIdealPowAlgHom (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      →ₐ[k] A ⧸ maximalIdeal A ^ n :=
  Ideal.Quotient.liftₐ _ ((evalₐ (maximalIdeal A) n).restrictScalars k) fun x hx => by
    rwa [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker] at hx

/--
@isnad1 id=eq.0h4v.s13.2b307ff10230 from=translated src=- shape=4eab9302 vocab=08a138e0
-/
theorem quotientMaximalIdealPowAlgHom_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgHom k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

/--
@isnad1 id=bijectiv.0h3v.s12.c953bf4b466a from=translated src=- shape=b47cc33c vocab=c656dbd5
-/
theorem quotientMaximalIdealPowAlgHom_bijective (n : ℕ) :
    Function.Bijective (quotientMaximalIdealPowAlgHom (A := A) k n) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotientMaximalIdealPowAlgHom_mk, quotientMaximalIdealPowAlgHom_mk] at hxy
    refine Ideal.Quotient.eq.mpr ?_
    rw [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker, map_sub, hxy, sub_self]
  · intro z
    obtain ⟨x, rfl⟩ := surjective_evalₐ (maximalIdeal A) n z
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩

noncomputable def quotientMaximalIdealPowAlgEquiv (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  AlgEquiv.ofBijective _ (quotientMaximalIdealPowAlgHom_bijective k n)

end Scalars

end Local

section Transport

variable [IsLocalRing A] [IsNoetherianRing A]
variable {k : Type*} [CommRing k] [Algebra k A] {B : Type*} [CommRing B] [IsLocalRing B] [Algebra k B]
variable (Φ : AdicCompletion (maximalIdeal A) A ≃ₐ[k] B)

omit [IsNoetherianRing A] [IsLocalRing B] in
/--
@isnad1 id=iff.0h5v.s9.54d3b1501186 from=translated src=- shape=9ba865a9 vocab=1d733083
-/
theorem isUnit_algEquiv_iff (x : AdicCompletion (maximalIdeal A) A) : IsUnit (Φ x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map Φ.symm, fun h => h.map Φ⟩

/--
@isnad1 id=eq.0h4v.s9.69ffd389b31c from=translated src=- shape=8249d32e vocab=08a6d1ab
-/
theorem comap_maximalIdeal_algEquiv :
    (maximalIdeal B).comap (Φ : AdicCompletion (maximalIdeal A) A →+* B)
      = maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  ext x
  show Φ x ∈ maximalIdeal B ↔ x ∈ maximalIdeal _
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_algEquiv_iff]

/--
@isnad1 id=eq.0h4v.s9.383217cfbb6b from=translated src=- shape=9eace9db vocab=a030a175
-/
theorem map_maximalIdeal_algEquiv :
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map
        (Φ : AdicCompletion (maximalIdeal A) A →+* B) = maximalIdeal B := by
  rw [← comap_maximalIdeal_algEquiv Φ]
  exact Ideal.map_comap_of_surjective _ Φ.surjective _

/--
@isnad1 id=eq.0h4v.s9.a42c848769a9 from=translated src=- shape=0ceca426 vocab=76c87bd5
-/
theorem maximalIdeal_eq_map_algEquiv :
    maximalIdeal B = (maximalIdeal A).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [← Ideal.map_map, ← maximalIdeal_eq_map, map_maximalIdeal_algEquiv]

noncomputable def quotientMaximalIdealPowAlgEquivOfAlgEquiv (n : ℕ) :
    (B ⧸ maximalIdeal B ^ n) ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  (Ideal.quotientEquivAlg (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) (maximalIdeal B ^ n)
    Φ (by rw [Ideal.map_pow, map_maximalIdeal_algEquiv])).symm.trans
    (quotientMaximalIdealPowAlgEquiv k n)

end Transport

end AdicCompletion

