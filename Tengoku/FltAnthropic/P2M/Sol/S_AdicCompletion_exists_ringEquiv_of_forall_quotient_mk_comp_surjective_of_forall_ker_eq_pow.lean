import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow

set_option autoImplicit false

namespace AdicCompletion
export _root_.AdicCompletion (evalₐ map mk liftRingHom of mk_surjective ext evalₐ_liftRingHom ext_evalₐ lift evalₐ_mk congr)
namespace AssemblyProof
open _root_.AdicCompletion

open _root_.AdicCompletion open _root_.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion

variable {R S : Type*} [CommRing R] [CommRing S]

/--
@isnad1 id=eq.1h5v.s11.b28f3d5ba92d from=translated src=- shape=576c93d7 vocab=a954745f
-/
theorem factorPow_evalₐ (I : Ideal R) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  have h : c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := c.2 hle
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
  have h' : c n - c m ∈ I ^ m := by
    have := Submodule.neg_mem _ h
    rwa [neg_sub] at this
  exact Ideal.Quotient.eq.mpr h'

section Levelwise

variable (I : Ideal R) (J : Ideal S) (f : R →+* S)
  (hker : ∀ k : ℕ, RingHom.ker ((Ideal.Quotient.mk (J ^ k)).comp f) = I ^ k)
  (hsurj : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (J ^ k)).comp f))

def ψ (k : ℕ) : R ⧸ I ^ k →+* S ⧸ J ^ k :=
  Ideal.Quotient.lift (I ^ k) ((Ideal.Quotient.mk (J ^ k)).comp f)
    (fun r hr => by rw [← RingHom.mem_ker, hker]; exact hr)

/--
@isnad1 id=eq.1h7v.s11.23b9701b0cbd from=translated src=- shape=6fc107e7 vocab=4406a54d
-/
theorem ψ_mk (k : ℕ) (r : R) : ψ I J f hker k (Ideal.Quotient.mk (I ^ k) r) = Ideal.Quotient.mk (J ^ k) (f r) :=
  Ideal.Quotient.lift_mk _ _ _

/--
@isnad1 id=injectiv.1h6v.s10.913ec7e2555d from=translated src=- shape=ce9e68ee vocab=b4e078b9
-/
theorem ψ_injective (k : ℕ) : Function.Injective (ψ I J f hker k) :=
  RingHom.lift_injective_of_ker_le_ideal (I ^ k) _ (le_of_eq (hker k))

/--
@isnad1 id=eq.2h7v.s11.ce230bf43a88 from=translated src=- shape=4fd78a1e vocab=c1fea856
-/
theorem factorPow_comp_ψ {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (ψ I J f hker n) = (ψ I J f hker m).comp (Ideal.Quotient.factorPow I hle) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply, ψ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

include hsurj in
/--
@isnad1 id=surjecti.2h6v.s11.d6b4ad2e8012 from=translated src=- shape=dd14c2c1 vocab=96c034fb
-/
theorem ψ_surjective (k : ℕ) : Function.Surjective (ψ I J f hker k) :=
  Ideal.Quotient.lift_surjective_of_surjective (I ^ k) _ (hsurj k)

noncomputable def e (k : ℕ) : R ⧸ I ^ k ≃+* S ⧸ J ^ k :=
  RingEquiv.ofBijective (ψ I J f hker k) ⟨ψ_injective I J f hker k, ψ_surjective I J f hker hsurj k⟩

/--
@isnad1 id=eq.2h7v.s12.dc2b66f4f3ef from=translated src=- shape=e181a334 vocab=59d0b352
-/
theorem e_apply (k : ℕ) (q : R ⧸ I ^ k) : e I J f hker hsurj k q = ψ I J f hker k q := rfl

/--
@isnad1 id=eq.2h7v.s11.06438f07c4b0 from=translated src=- shape=ede4385a vocab=2e6d1d01
-/
theorem compatF {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp ((ψ I J f hker n).comp (evalₐ I n).toRingHom) =
      (ψ I J f hker m).comp (evalₐ I m).toRingHom := by
  rw [← RingHom.comp_assoc, factorPow_comp_ψ, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun x => factorPow_evalₐ I hle x

noncomputable def F : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (fun n => (ψ I J f hker n).comp (evalₐ I n).toRingHom)
    (fun hle => compatF I J f hker hle)

/--
@isnad1 id=eq.1h7v.s11.667c2adc080e from=translated src=- shape=607959c8 vocab=aa3e04fb
-/
theorem evalₐ_F (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (F I J f hker x) = ψ I J f hker n (evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (fun hle => compatF I J f hker hle) n x

/--
@isnad1 id=eq.3h7v.s12.515ccdd36d4e from=translated src=- shape=6ff0e634 vocab=8ebbe130
-/
theorem compatG {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp ((e I J f hker hsurj n).symm.toRingHom.comp (evalₐ J n).toRingHom) =
      (e I J f hker hsurj m).symm.toRingHom.comp (evalₐ J m).toRingHom := by
  refine RingHom.ext fun y => ?_
  apply (e I J f hker hsurj m).injective
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [e_apply, ← RingHom.comp_apply (ψ I J f hker m), ← factorPow_comp_ψ I J f hker hle, RingHom.comp_apply,
    ← e_apply I J f hker hsurj n, RingEquiv.apply_symm_apply, factorPow_evalₐ]

noncomputable def G : AdicCompletion J S →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (fun n => (e I J f hker hsurj n).symm.toRingHom.comp (evalₐ J n).toRingHom)
    (fun hle => compatG I J f hker hsurj hle)

/--
@isnad1 id=eq.2h7v.s12.37ec320fd954 from=translated src=- shape=5a4acd99 vocab=e1d40490
-/
theorem evalₐ_G (n : ℕ) (y : AdicCompletion J S) :
    evalₐ I n (G I J f hker hsurj y) = (e I J f hker hsurj n).symm (evalₐ J n y) :=
  AdicCompletion.evalₐ_liftRingHom I _ (fun hle => compatG I J f hker hsurj hle) n y

/--
@isnad1 id=eq.2h5v.s11.4c73db20115d from=translated src=- shape=abd7d56a vocab=cc9d41a3
-/
theorem F_comp_G : (F I J f hker).comp (G I J f hker hsurj) = RingHom.id _ := by
  refine RingHom.ext fun y => AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, evalₐ_F, evalₐ_G, ← e_apply I J f hker hsurj n, RingEquiv.apply_symm_apply, RingHom.id_apply]

/--
@isnad1 id=eq.2h5v.s11.e4c9617b8c3f from=translated src=- shape=bad95bc9 vocab=cc9d41a3
-/
theorem G_comp_F : (G I J f hker hsurj).comp (F I J f hker) = RingHom.id _ := by
  refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, evalₐ_G, evalₐ_F, ← e_apply I J f hker hsurj n, RingEquiv.symm_apply_apply, RingHom.id_apply]

end Levelwise

end AdicCompletion.AssemblyProof

open _root_.AdicCompletion _root_.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion AdicCompletion.AssemblyProof in
/--
@isnad1 id=ex.2h5v.s11.2224eb3cb05e from=translated src=- shape=138abb23 vocab=25591dc2
-/
theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hsurj : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (J ^ k)).comp f))
    (hker : ∀ k : ℕ, RingHom.ker ((Ideal.Quotient.mk (J ^ k)).comp f) = I ^ k) :
    ∃ e : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r : R, e (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r) := by
  refine ⟨RingEquiv.ofRingHom (F I J f hker) (G I J f hker hsurj) (F_comp_G I J f hker hsurj) (G_comp_F I J f hker hsurj),
    fun r => ?_⟩
  show F I J f hker (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r)
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_F, AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, ψ_mk]
