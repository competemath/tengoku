/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.ProjectiveDimension
import Tengoku.Seed.Algebra.Polynomial.Module.TensorProduct
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hilbert's syzygy theorem

We prove that every module over `k[X₁, …, Xₙ]`, `k` a field, has projective dimension at most
`n` (`ModuleCat.hasGlobalDimensionLE_mvPolynomial`).

The proof is the classical one via the exact sequence of `A[X]`-modules
`0 → A[X] ⊗[A] M → A[X] ⊗[A] M → M → 0`, with maps
`Xⁱ ⊗ m ↦ Xⁱ⁺¹ ⊗ m - Xⁱ ⊗ X m` and `Xⁱ ⊗ m ↦ Xⁱ m`, for any `A[X]`-module `M` (written
with `PolynomialModule A M`), together with the fact that flat base change does not increase
projective dimension (`ModuleCat.hasProjectiveDimensionLE_baseChange`). This gives
`gldim A[X] ≤ gldim A + 1` (`ModuleCat.hasGlobalDimensionLE_polynomial`).

## Main definitions and results

* `ModuleCat.HasGlobalDimensionLE R d`: every `R`-module has projective dimension `≤ d`.
* `ModuleCat.hasProjectiveDimensionLE_baseChange`: for a flat `A`-algebra `B`,
  `pd_B (B ⊗[A] N) ≤ pd_A N`.
* `PolynomialModule.exact_diff_augment`, `PolynomialModule.diff_injective`,
  `PolynomialModule.augment_surjective`: the exact sequence above.
* `ModuleCat.hasGlobalDimensionLE_polynomial`, `ModuleCat.hasGlobalDimensionLE_mvPolynomial`.
-/

universe u

open CategoryTheory TensorProduct Polynomial

noncomputable section

namespace PolynomialModule

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

/-- The `A[X]`-linear isomorphism `A[X] ⊗[A] M ≃ PolynomialModule A M`. -/
noncomputable abbrev tensorEquiv : A[X] ⊗[A] M ≃ₗ[A[X]] PolynomialModule A M :=
  polynomialTensorProductLEquivPolynomialModule A M

/--
@isnad1 id=eq.0h3v.s10.f26f68fd7d98 from=translated src=- shape=61d32617 vocab=3da8cde6
-/
lemma tensorEquiv_symm_single_zero (m : M) :
    (tensorEquiv (A := A) (M := M)).symm (single A 0 m) = 1 ⊗ₜ m := by
  rw [LinearEquiv.symm_apply_eq]
  simp [polynomialTensorProductLEquivPolynomialModule, lsingle]

/--
@isnad1 id=eq.0h4v.s8.d005c7e4a670 from=translated src=- shape=fcb064bf vocab=b098ccc3
-/
lemma single_eq_X_pow_smul (i : ℕ) (m : M) :
    single A i m = (X ^ i : A[X]) • single A 0 m := by
  rw [← monomial_one_right_eq_X_pow, monomial_smul_single, one_smul, add_zero]

variable [Module A[X] M] [IsScalarTower A A[X] M]

/-- The `A`-linear endomorphism `m ↦ X • m`. -/
noncomputable def mulX : M →ₗ[A] M :=
  ((X : A[X]) • LinearMap.id : M →ₗ[A[X]] M).restrictScalars A

/-- The augmentation `Σ Xⁱ mᵢ ↦ Σ Xⁱ • mᵢ`. -/
noncomputable def augment : PolynomialModule A M →ₗ[A[X]] M :=
  LinearMap.liftBaseChange A[X] (LinearMap.id : M →ₗ[A] M) ∘ₗ
    (tensorEquiv (A := A) (M := M)).symm.toLinearMap

/--
@isnad1 id=eq.0h4v.s9.6dda47e6f0b6 from=translated src=- shape=b493c492 vocab=b84d50e0
-/
lemma augment_single (i : ℕ) (m : M) : augment (single A i m) = (X ^ i : A[X]) • m := by
  rw [single_eq_X_pow_smul, LinearMap.map_smul]
  simp [augment, tensorEquiv_symm_single_zero]

/-- The `A`-linear map `m ↦ X m - (X • m)`. -/
noncomputable def diffAux : M →ₗ[A] PolynomialModule A M :=
  lsingle A 1 - lsingle A 0 ∘ₗ mulX

/-- The differential `Xⁱ m ↦ Xⁱ⁺¹ m - Xⁱ (X • m)`. -/
noncomputable def diff : PolynomialModule A M →ₗ[A[X]] PolynomialModule A M :=
  LinearMap.liftBaseChange A[X] diffAux ∘ₗ (tensorEquiv (A := A) (M := M)).symm.toLinearMap

/--
@isnad1 id=eq.0h4v.s9.507859b2ec98 from=translated src=- shape=70ccbd8e vocab=fc5541ef
-/
lemma diff_single (i : ℕ) (m : M) :
    diff (single A i m) = single A (i + 1) m - single A i ((X : A[X]) • m) := by
  rw [single_eq_X_pow_smul, LinearMap.map_smul]
  simp only [diff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    tensorEquiv_symm_single_zero, LinearMap.liftBaseChange_tmul, one_smul]
  simp only [diffAux, lsingle, mulX, LinearMap.restrictScalars_smul,
    LinearMap.restrictScalars_id, LinearMap.sub_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lsingle_apply, coeffLinearEquiv_symm_apply, ofCoeff_single,
    LinearMap.coe_smul, LinearMap.id_coe, Pi.smul_apply, id_eq, smul_sub,
    ← single_eq_X_pow_smul, sub_left_inj]
  rw [← monomial_one_right_eq_X_pow, monomial_smul_single, one_smul]

/--
@isnad1 id=eq.0h3v.s9.83df2a5ef48d from=translated src=- shape=529f1873 vocab=fadc99ae
-/
lemma augment_diff (q : PolynomialModule A M) : augment (diff q) = 0 := by
  induction q using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i m => simp [diff_single, augment_single, pow_succ, mul_smul]

omit [Module A[X] M] [IsScalarTower A A[X] M] in
/--
@isnad1 id=eq.0h4v.s8.f185894e77be from=translated src=- shape=6b1e93b5 vocab=b66551a4
-/
lemma X_smul_coeff (q : PolynomialModule A M) (n : ℕ) :
    ((X : A[X]) • q).coeff (n + 1) = q.coeff n := by
  rw [← monomial_one_one_eq_X, monomial_smul_apply]
  simp

omit [Module A[X] M] [IsScalarTower A A[X] M] in
/--
@isnad1 id=eq.0h5v.s8.1a75f5cdb4c9 from=translated src=- shape=1fe94a41 vocab=d167dafd
-/
lemma map_coeff (f : M →ₗ[A] M) (q : PolynomialModule A M) (n : ℕ) :
    (map A f q).coeff n = f (q.coeff n) := by
  simp [map]

/--
@isnad1 id=eq.0h3v.s9.b46487cd8b54 from=translated src=- shape=b101d86d vocab=01df9406
-/
lemma diff_eq (q : PolynomialModule A M) : diff q = (X : A[X]) • q - map A mulX q := by
  induction q using induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | single i m =>
    rw [diff_single, map_single, ← monomial_one_one_eq_X, monomial_smul_single, one_smul,
      add_comm 1 i]
    rfl

/--
@isnad1 id=injectiv.0h2v.s8.129a281df105 from=translated src=- shape=4e8f56bc vocab=ba74538f
-/
lemma diff_injective : Function.Injective (diff (A := A) (M := M)) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra hq0
  have hs : q.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun h ↦ hq0 (coeff_eq_zero.mp h)
  set N := q.coeff.support.max' hs
  have hN : q.coeff N ≠ 0 := Finsupp.mem_support_iff.mp (q.coeff.support.max'_mem hs)
  have hN1 : q.coeff (N + 1) = 0 := by
    by_contra h
    have := q.coeff.support.le_max' _ (Finsupp.mem_support_iff.mpr h)
    omega
  have := congr_arg (fun r ↦ r.coeff (N + 1)) hq
  have hsub : ∀ x y : PolynomialModule A M, (x - y).coeff = x.coeff - y.coeff :=
    map_sub (coeffAddEquiv (R := A) (M := M))
  simp only [diff_eq, hsub, Finsupp.coe_sub, Pi.sub_apply, X_smul_coeff, map_coeff, hN1,
    map_zero, sub_zero, coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact hN this

/--
@isnad1 id=mem.0h3v.s9.5f3a8394dc62 from=translated src=- shape=61f9565a vocab=1d23aab9
-/
lemma sub_single_augment_mem_range (q : PolynomialModule A M) :
    q - single A 0 (augment q) ∈ LinearMap.range (diff (A := A) (M := M)) := by
  induction q using induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, single_add, add_sub_add_comm]
    exact add_mem hx hy
  | single i m =>
    induction i generalizing m with
    | zero => simp [augment_single]
    | succ i ih =>
      have h := ih ((X : A[X]) • m)
      rw [augment_single] at h ⊢
      have e : single A (i + 1) m - single A 0 ((X ^ (i + 1) : A[X]) • m) =
          diff (single A i m) + (single A i ((X : A[X]) • m) -
            single A 0 ((X ^ i : A[X]) • (X : A[X]) • m)) := by
        rw [diff_single, pow_succ, mul_smul]
        abel
      rw [e]
      exact add_mem (LinearMap.mem_range_self _ _) h

/--
@isnad1 id=exact.0h2v.s9.3926100ab089 from=translated src=- shape=2026662c vocab=e52c7d19
-/
lemma exact_diff_augment : Function.Exact (diff (A := A) (M := M)) augment := by
  intro q
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa [h] using sub_single_augment_mem_range q
  · rintro ⟨q, rfl⟩
    exact augment_diff q

/--
@isnad1 id=surjecti.0h2v.s8.ac0dc51c03c5 from=translated src=- shape=32624c29 vocab=cd8eaffe
-/
lemma augment_surjective : Function.Surjective (augment (A := A) (M := M)) :=
  fun m ↦ ⟨single A 0 m, by simp [augment_single]⟩

end PolynomialModule

namespace ModuleCat

variable {A : Type u} [CommRing A]

/--
@isnad1 id=hasproje.3h7v.s8.981a72da1116 from=translated src=- shape=3b8f2da2 vocab=95b29c4b
-/
lemma hasProjectiveDimensionLE_succ_of_exact {K P N : Type u} [AddCommGroup K] [Module A K]
    [AddCommGroup P] [Module A P] [AddCommGroup N] [Module A N]
    (f : K →ₗ[A] P) (g : P →ₗ[A] N) (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) (d : ℕ) [Module.Projective A P]
    [HasProjectiveDimensionLE (ModuleCat.of A K) d] :
    HasProjectiveDimensionLE (ModuleCat.of A N) (d + 1) := by
  let S : ShortComplex (ModuleCat.{u} A) :=
    ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
  have : Projective S.X₂ := (IsProjective.iff_projective P).mp inferInstance
  exact (hS.hasProjectiveDimensionLT_X₃_iff d this).mpr ‹_›

/--
@isnad1 id=hasproje.3h7v.s8.ba1ab4f272c3 from=translated src=- shape=546a7fd4 vocab=95b29c4b
-/
lemma hasProjectiveDimensionLE_of_exact {K P N : Type u} [AddCommGroup K] [Module A K]
    [AddCommGroup P] [Module A P] [AddCommGroup N] [Module A N]
    (f : K →ₗ[A] P) (g : P →ₗ[A] N) (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) (d : ℕ) [Module.Projective A P]
    [HasProjectiveDimensionLE (ModuleCat.of A N) (d + 1)] :
    HasProjectiveDimensionLE (ModuleCat.of A K) d := by
  let S : ShortComplex (ModuleCat.{u} A) :=
    ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
  have : Projective S.X₂ := (IsProjective.iff_projective P).mp inferInstance
  exact (hS.hasProjectiveDimensionLT_X₃_iff d this).mp ‹_›

variable {B : Type u} [CommRing B] [Algebra A B] [Module.Flat A B]

/--
@isnad1 id=hasproje.0h4v.s7.50e1c22d5058 from=translated src=- shape=1c0f1a26 vocab=409b4c38
-/
lemma hasProjectiveDimensionLE_baseChange (d : ℕ) (N : Type u) [AddCommGroup N] [Module A N]
    [HasProjectiveDimensionLE (ModuleCat.of A N) d] :
    HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] N)) d := by
  induction d generalizing N with
  | zero =>
    have h : HasProjectiveDimensionLE (ModuleCat.of A N) 0 := ‹_›
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
      ← IsProjective.iff_projective] at h ⊢
    infer_instance
  | succ d ih =>
    let g : (N →₀ A) →ₗ[A] N := Finsupp.linearCombination A id
    have hg : Function.Surjective g := fun x ↦ ⟨Finsupp.single x 1, by simp [g]⟩
    have hK := hasProjectiveDimensionLE_of_exact (K := LinearMap.ker g) (LinearMap.ker g).subtype g
      (LinearMap.exact_subtype_ker_map g) (Submodule.injective_subtype _) hg d
    have := ih (LinearMap.ker g)
    refine hasProjectiveDimensionLE_succ_of_exact
      ((LinearMap.ker g).subtype.baseChange B) (g.baseChange B) ?_ ?_ ?_ d
    · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_exact (R := A) B (N := LinearMap.ker g) (N' := N →₀ A)
        (N'' := N) (LinearMap.exact_subtype_ker_map g)
    · rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _
        (LinearMap.ker g).injective_subtype
    · rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective B hg

/-- Every `R`-module (in the universe of `R`) has projective dimension at most `d`, i.e. the
global dimension of `R` is at most `d`. -/
def HasGlobalDimensionLE (R : Type u) [CommRing R] (d : ℕ) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M], HasProjectiveDimensionLE (ModuleCat.of R M) d

/--
@isnad1 id=hasgloba.2h3v.s4.6e1242f26865 from=translated src=- shape=6dcaf7d6 vocab=a9994a21
-/
lemma HasGlobalDimensionLE.mono {R : Type u} [CommRing R] {d e : ℕ}
    (h : HasGlobalDimensionLE R d) (hde : d ≤ e) : HasGlobalDimensionLE R e := fun M _ _ ↦
  have := h M
  hasProjectiveDimensionLT_of_ge _ (d + 1) (e + 1) (by omega)

/-- Over a field every module is free, hence projective.
@isnad1 id=hasgloba.0h1v.s3.f3456581ca9e from=translated src=- shape=89d4eb60 vocab=c413b78e
-/
lemma hasGlobalDimensionLE_zero_of_field (k : Type u) [Field k] : HasGlobalDimensionLE k 0 := by
  intro M _ _
  simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective]
  infer_instance

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Global dimension bounds are invariant under ring isomorphisms.
@isnad1 id=hasgloba.1h4v.s5.a19cce87ae9d from=translated src=- shape=ff3f24c4 vocab=e365c423
-/
lemma HasGlobalDimensionLE.of_ringEquiv {R R' : Type u} [CommRing R] [CommRing R'] (e : R ≃+* R')
    {d : ℕ} (h : HasGlobalDimensionLE R d) : HasGlobalDimensionLE R' d := by
  intro M _ _
  letI : Module R M := Module.compHom M (e : R →+* R')
  let e' : ModuleCat.of R M ≃ₛₗ[RingHomClass.toRingHom e] ModuleCat.of R' M :=
    { AddEquiv.refl M with map_smul' := fun _ _ ↦ rfl }
  have := h M
  exact hasProjectiveDimensionLE_of_semiLinearEquiv e e' d

/-- **Hilbert's syzygy theorem, inductive step**: if every `A`-module has projective dimension
at most `d`, then every `A[X]`-module has projective dimension at most `d + 1`.
@isnad1 id=hasgloba.1h2v.s5.90e5d9cc3836 from=translated src=- shape=92a75d9e vocab=b1f7f65e
-/
theorem hasGlobalDimensionLE_polynomial {A : Type u} [CommRing A] {d : ℕ}
    (h : HasGlobalDimensionLE A d) : HasGlobalDimensionLE A[X] (d + 1) := by
  intro M _ _
  letI : Module A M := Module.compHom M (algebraMap A A[X])
  haveI : IsScalarTower A A[X] M := ⟨fun a p m ↦ by
    change (a • p) • m = (algebraMap A A[X] a) • (p • m)
    rw [Algebra.smul_def, mul_smul]⟩
  have := h M
  have hT := hasProjectiveDimensionLE_baseChange (A := A) (B := A[X]) d M
  have hP : HasProjectiveDimensionLE (ModuleCat.of A[X] (PolynomialModule A M)) d :=
    hasProjectiveDimensionLE_of_linearEquiv.{u, u}
      (M := ModuleCat.of A[X] (A[X] ⊗[A] M)) (N := ModuleCat.of A[X] (PolynomialModule A M))
      (PolynomialModule.polynomialTensorProductLEquivPolynomialModule A M) d
  let S : ShortComplex (ModuleCat.{u} A[X]) :=
    ModuleCat.shortComplexOfCompEqZero (PolynomialModule.diff (A := A) (M := M))
      PolynomialModule.augment PolynomialModule.exact_diff_augment.linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    PolynomialModule.exact_diff_augment PolynomialModule.diff_injective
    PolynomialModule.augment_surjective
  exact hS.hasProjectiveDimensionLT_X₃ (d + 1) hP
    (hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 1 + 1) (by omega))

/-- **Hilbert's syzygy theorem**: every module over `k[X₁, …, Xₙ]` has projective dimension at
most `n`.
@isnad1 id=hasgloba.0h2v.s5.3e529e7f9159 from=translated src=- shape=8912f54d vocab=fcda3be5
-/
theorem hasGlobalDimensionLE_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    HasGlobalDimensionLE (MvPolynomial (Fin n) k) n := by
  induction n with
  | zero =>
    exact (hasGlobalDimensionLE_zero_of_field k).of_ringEquiv
      (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toRingEquiv
  | succ n ih =>
    exact (hasGlobalDimensionLE_polynomial ih).of_ringEquiv
      (MvPolynomial.finSuccEquiv k n).symm.toRingEquiv

end ModuleCat
