import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective

set_option autoImplicit false

open scoped TensorProduct

namespace ConormalPresentation

open KaehlerDifferential

section Generic

variable (R : Type*) [CommRing R] (m : ℕ) (S : Type*) [CommRing S]
variable [Algebra R S] [Algebra (MvPolynomial (Fin m) R) S] [IsScalarTower R (MvPolynomial (Fin m) R) S]

local notation "P" => MvPolynomial (Fin m) R

noncomputable def bS : Module.Basis (Fin m) S (S ⊗[P] Ω[P⁄R]) := (mvPolynomialBasis R (Fin m)).baseChange S

noncomputable def coords : (Fin m → S) ≃ₗ[S] S ⊗[P] Ω[P⁄R] :=
  (Finsupp.linearEquivFunOnFinite S S (Fin m)).symm ≪≫ₗ (bS R m S).repr.symm

/--
@isnad1 id=eq.0h4v.s12.f97fd3cc4deb from=translated src=- shape=72540ed5 vocab=5513e341
-/
theorem coords_single (j : Fin m) : coords R m S (Pi.single j 1) = (1 : S) ⊗ₜ[P] D R P (MvPolynomial.X j) := by
  have h1 : (Finsupp.linearEquivFunOnFinite S S (Fin m)).symm (Pi.single j 1) = Finsupp.single j 1 := by
    ext i; simp [Finsupp.linearEquivFunOnFinite, Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [coords, LinearEquiv.trans_apply, h1, Module.Basis.repr_symm_single_one, bS, Module.Basis.baseChange_apply,
    mvPolynomialBasis_apply]

/--
@isnad1 id=eq.0h5v.s13.7491339c2467 from=translated src=- shape=5833f5d1 vocab=04df5e07
-/
theorem coords_symm_tmul (w : Ω[P⁄R]) (j : Fin m) :
    (coords R m S).symm ((1 : S) ⊗ₜ[P] w) j = algebraMap P S ((mvPolynomialBasis R (Fin m)).repr w j) := by
  rw [coords, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.symm_symm,
    Finsupp.linearEquivFunOnFinite_apply, bS, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

/--
@isnad1 id=eq.0h5v.s12.a0c31fcb6678 from=translated src=- shape=ef7bc0f1 vocab=d989eb74
-/
theorem coords_symm_tmul_D (g : P) (j : Fin m) :
    (coords R m S).symm ((1 : S) ⊗ₜ[P] D R P g) j = algebraMap P S (MvPolynomial.pderiv j g) := by
  rw [coords_symm_tmul, mvPolynomialBasis_repr_apply]

noncomputable def Φ : (Fin m → S) →ₗ[S] Ω[S⁄R] := (mapBaseChange R P S) ∘ₗ (coords R m S).toLinearMap

/--
@isnad1 id=eq.0h4v.s9.d15ca4dc469f from=translated src=- shape=261f6e9d vocab=6a645117
-/
theorem Φ_single (j : Fin m) : Φ R m S (Pi.single j 1) = D R S (algebraMap P S (MvPolynomial.X j)) := by
  rw [Φ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, coords_single, mapBaseChange_tmul, one_smul, map_D]

/--
@isnad1 id=surjecti.1h3v.s9.9624d423d31a from=translated src=- shape=55a8d496 vocab=1ef3bf72
-/
theorem Φ_surjective (hφ : Function.Surjective (algebraMap P S)) : Function.Surjective (Φ R m S) :=
  (mapBaseChange_surjective R P S hφ).comp (coords R m S).surjective

/--
@isnad1 id=eq.2h5v.s12.4dcb37cd9420 from=translated src=- shape=c6dc8299 vocab=5d05cd9a
-/
theorem ker_mapBaseChange_eq {r : ℕ} (f : Fin r → P) (hφ : Function.Surjective (algebraMap P S))
    (hker : RingHom.ker (algebraMap P S) = Ideal.span (Set.range f)) :
    LinearMap.ker (mapBaseChange R P S) =
      Submodule.span S (Set.range fun i : Fin r => (1 : S) ⊗ₜ[P] D R P (f i)) := by
  classical
  have hex := exact_kerCotangentToTensor_mapBaseChange R P S hφ
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨c, hc⟩ := (hex w).mp hw
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ c
    rw [kerCotangentToTensor_toCotangent] at hc
    rw [← hc]
    have hx : (x : P) ∈ Ideal.span (Set.range f) := hker ▸ x.2
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
    rw [← ha, map_sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz, TensorProduct.tmul_add]
    have hfi : algebraMap P S (f i) = 0 := by
      have : f i ∈ RingHom.ker (algebraMap P S) := hker ▸ Ideal.subset_span (Set.mem_range_self i)
      exact this
    have h1 : (1 : S) ⊗ₜ[P] (f i • D R P (a i)) = 0 := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, hfi, TensorProduct.zero_tmul]
    have h2 : (1 : S) ⊗ₜ[P] (a i • D R P (f i)) = algebraMap P S (a i) • ((1 : S) ⊗ₜ[P] D R P (f i)) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        smul_eq_mul, mul_one]
    rw [h2, h1, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    apply (hex _).mpr
    have hfi : f i ∈ RingHom.ker (algebraMap P S) := hker ▸ Ideal.subset_span (Set.mem_range_self i)
    exact ⟨(RingHom.ker (algebraMap P S)).toCotangent ⟨f i, hfi⟩, kerCotangentToTensor_toCotangent R P S _⟩

/--
@isnad1 id=eq.2h5v.s10.8065d999d3b8 from=translated src=- shape=fe248a3f vocab=fc610291
-/
theorem ker_Φ {r : ℕ} (f : Fin r → P) (hφ : Function.Surjective (algebraMap P S))
    (hker : RingHom.ker (algebraMap P S) = Ideal.span (Set.range f)) :
    LinearMap.ker (Φ R m S) =
      Submodule.span S (Set.range fun i : Fin r => fun j : Fin m => algebraMap P S (MvPolynomial.pderiv j (f i))) := by
  rw [Φ, LinearMap.ker_comp, ker_mapBaseChange_eq R m S f hφ hker, Submodule.comap_equiv_eq_map_symm,
    Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, funext fun j => (coords_symm_tmul_D R m S (f i) j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, funext fun j => coords_symm_tmul_D R m S (f i) j⟩

end Generic

end ConormalPresentation

/--
@isnad1 id=ex.2h6v.s11.f1e7ada7b4d8 from=translated src=- shape=066f8150 vocab=90cc0816
-/
theorem solution
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {m r : ℕ}
    (f : Fin r → MvPolynomial (Fin m) R) (φ : MvPolynomial (Fin m) R →ₐ[R] S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span (Set.range f)) :
    ∃ Φ : (Fin m → S) →ₗ[S] Ω[S⁄R],
      Function.Surjective Φ ∧
      (∀ j : Fin m, Φ (Pi.single j 1) = KaehlerDifferential.D R S (φ (MvPolynomial.X j))) ∧
      LinearMap.ker Φ = Submodule.span S (Set.range fun i : Fin r => fun j : Fin m => φ (MvPolynomial.pderiv j (f i))) := by
  letI : Algebra (MvPolynomial (Fin m) R) S := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin m) R) S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap R S x = φ (algebraMap R (MvPolynomial (Fin m) R) x)
      rw [AlgHom.commutes]
  have hmap : (algebraMap (MvPolynomial (Fin m) R) S : MvPolynomial (Fin m) R → S) = φ := rfl
  refine ⟨ConormalPresentation.Φ R m S, ConormalPresentation.Φ_surjective R m S (by rw [hmap]; exact hφ),
    fun j => ?_, ?_⟩
  · rw [ConormalPresentation.Φ_single]; rfl
  · rw [ConormalPresentation.ker_Φ R m S f (by rw [hmap]; exact hφ) (by ext x; exact Iff.of_eq (congrArg (x ∈ ·) hker))]
    rfl
