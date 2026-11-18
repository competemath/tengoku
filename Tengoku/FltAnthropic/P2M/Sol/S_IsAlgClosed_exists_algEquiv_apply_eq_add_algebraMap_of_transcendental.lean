import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental

open MvPolynomial

namespace TranslateTranscendental

variable {K : Type*} [Field K] {ι : Type*}

noncomputable def shift (c : ι → K) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval fun i => X i + C (c i)

/--
@isnad1 id=eq.0h4v.s8.db4d828ab392 from=translated src=- shape=34478692 vocab=88ff66cf
-/
@[scoped simp] theorem shift_X (c : ι → K) (i : ι) : shift c (X i) = X i + C (c i) := by
  simp [shift]

/--
@isnad1 id=eq.0h3v.s8.41d55c192a46 from=translated src=- shape=0bfa6885 vocab=4aa8a9dd
-/
theorem shift_comp_shift_neg (c : ι → K) : (shift c).comp (shift (-c)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [shift, add_assoc]

/--
@isnad1 id=eq.0h3v.s8.13acf434a7b3 from=translated src=- shape=ca2ef191 vocab=4aa8a9dd
-/
theorem shift_neg_comp_shift (c : ι → K) : (shift (-c)).comp (shift c) = AlgHom.id K _ := by
  simpa using shift_comp_shift_neg (-c)

noncomputable def shiftEquiv (c : ι → K) : MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (shift c) (shift (-c)) (shift_comp_shift_neg c) (shift_neg_comp_shift c)

/--
@isnad1 id=eq.0h4v.s8.0c67f8b1bb5d from=translated src=- shape=34478692 vocab=f1bb3fc4
-/
@[scoped simp] theorem shiftEquiv_X (c : ι → K) (i : ι) : shiftEquiv c (X i) = X i + C (c i) := by
  simp [shiftEquiv]

/--
@isnad1 id=eq.0h4v.s8.9b5bfefe2c56 from=translated src=- shape=fcd5842f vocab=b99fb19b
-/
@[scoped simp] theorem shiftEquiv_C (c : ι → K) (k : K) : shiftEquiv c (C k) = C k := by
  simp [shiftEquiv, shift]

end TranslateTranscendental
open scoped _root_.P2MW.S_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental.TranslateTranscendental

open TranslateTranscendental in
/--
@isnad1 id=ex.1h4v.s7.286162ed084c from=translated src=- shape=e49f9aad vocab=3c28ce15
-/
theorem solution
    (K K' : Type*) [Field K] [Field K'] [Algebra K K'] [IsAlgClosed K']
    (t : K') (ht : Transcendental K t) (a : K) :
    ∃ τ : K' ≃ₐ[K] K', τ t = t + algebraMap K K' a := by
  classical

  have hind : AlgebraicIndepOn K id ({t} : Set K') :=
    (algebraicIndependent_singleton_iff (R := K) (x := fun i : ({t} : Set K') => (id (i : K')))
      ⟨t, Set.mem_singleton t⟩).mpr ht
  obtain ⟨B, htB, hB⟩ := exists_isTranscendenceBasis_superset hind
  set L : IntermediateField K K' := IntermediateField.adjoin K (Set.range ((↑) : B → K')) with hL
  haveI : Algebra.IsAlgebraic L K' := hB.isAlgebraic_field
  haveI : IsAlgClosure L K' := ⟨inferInstance, inferInstance⟩
  let t₀ : B := ⟨t, htB (Set.mem_singleton t)⟩

  let c : B → K := fun i => if i = t₀ then a else 0
  let φ : MvPolynomial B K ≃ₐ[K] MvPolynomial B K := shiftEquiv c
  let φF : FractionRing (MvPolynomial B K) ≃+* FractionRing (MvPolynomial B K) :=
    IsFractionRing.ringEquivOfRingEquiv φ.toRingEquiv
  let e := hB.1.aevalEquivField
  let ψ : L ≃+* L := (e.symm.toRingEquiv.trans φF).trans e.toRingEquiv

  have hφF_alg : ∀ p : MvPolynomial B K,
      φF (algebraMap (MvPolynomial B K) (FractionRing (MvPolynomial B K)) p) =
        algebraMap _ _ (φ p) := fun p =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap φ.toRingEquiv p
  have hψK : ∀ k : K, ψ (algebraMap K L k) = algebraMap K L k := by
    intro k
    simp only [ψ, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial B K) (FractionRing (MvPolynomial B K)),
      hφF_alg, MvPolynomial.algebraMap_eq, show φ (C k) = C k from shiftEquiv_C c k,
      ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (MvPolynomial B K) (FractionRing (MvPolynomial B K)),
      AlgEquiv.commutes]

  have het : (e (algebraMap (MvPolynomial B K) _ (X t₀)) : K') = t := by
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe, aeval_X]
  have hψt : (ψ (e (algebraMap (MvPolynomial B K) _ (X t₀))) : K') = t + algebraMap K K' a := by
    simp only [ψ, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply]
    rw [hφF_alg, AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe,
      show φ (X t₀) = X t₀ + C (c t₀) from shiftEquiv_X c t₀]
    simp [c, t₀]

  let E : K' ≃+* K' := IsAlgClosure.equivOfEquiv K' K' ψ
  have hE : ∀ s : L, E (algebraMap L K' s) = algebraMap L K' (ψ s) :=
    fun s => IsAlgClosure.equivOfEquiv_algebraMap K' K' ψ s
  have hEK : ∀ k : K, E (algebraMap K K' k) = algebraMap K K' k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K L K', hE, hψK]
  refine ⟨{ E with commutes' := hEK }, ?_⟩
  change E t = t + algebraMap K K' a
  conv_lhs => rw [← het]
  rw [show ((e (algebraMap (MvPolynomial B K) _ (X t₀)) : L) : K') =
      algebraMap L K' (e (algebraMap (MvPolynomial B K) _ (X t₀))) from rfl, hE]
  exact hψt
