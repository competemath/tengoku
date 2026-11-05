/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import Tengoku.SplittingDensityRationality.SurfaceBlowup.Unramified.PolynomialTypes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Frobenius descent for unramified extensions

Let `O` be a complete discrete valuation ring with finite residue field and let `Φ` be an
unramified lift (a monic polynomial over `O` with irreducible residue polynomial). This file
first computes the Haar mass of projective cells, then develops the ring `O_δ = O[X]/(Φ)`: it is a
complete discrete valuation ring, unramified over `O`, carrying a Frobenius automorphism of order
`δ = deg Φ` with fixed ring `O`. Finally it proves Frobenius descent for blocks: monic residue
cells of `residuePoly Φ ^ r` over `O` correspond bijectively, and congruence-preservingly, to block
cells over `O_δ`.

## Main results

* `SurfaceBlowup.projective_cell_mass`, `SurfaceBlowup.projective_cell_conditional_density`:
  the mass of a projective cell and its density inside the primitive locus.
* `SurfaceBlowup.unramified_is_dvr`: `O_δ` is a complete DVR with uniformizer any uniformizer of
  `O` and residue field of cardinality `q ^ δ`.
* `SurfaceBlowup.frobenius_pow_degree_eq_id`, `SurfaceBlowup.frobenius_fixed_ring`: the Frobenius
  has order dividing `δ` and its fixed points are exactly `O`.
* `SurfaceBlowup.block_descent_bijection`, `SurfaceBlowup.block_descent_congruence_iff`: the
  descent bijection between residue cells and block cells, and its compatibility with congruences.

Provenance: `Thm_SurfaceBlowupV2_{projective_cell_mass, projective_cell_mass_mul_normalizer,
projective_cell_conditional_density, unramified_base_invariants, inertiaDeg_unramified_tower,
ramificationIdx_unramified_tower, unramified_fraction_field_lift, unramified_free_module,
unramified_adic_complete, base_ideal_maximal_local, simple_root_derivative_unit,
frobenius_root_exists, frobenius_root_spec, frobenius_residue_action, frobenius_fixed_mod_pow,
frobenius_fixed_ring, root_unique_of_congruent, frobenius_pow_degree_eq_id, unramified_is_domain,
conjugate_product_invariant, descend_block_mem_cell, unramified_is_dvr, block_conjugates,
block_conjugates_coprime, block_splitting, block_descent_bijection, block_descent_congruence_iff}`.
-/

namespace SurfaceBlowup

open scoped BigOperators ENNReal

/-! ### Projective cells -/

/-! ### Unramified extensions of discrete valuation rings -/

/-- A finite free extension of DVRs of rank `δ` in which a uniformizer stays irreducible has
ramification index `1` and inertia degree `δ`.-/
private theorem unramified_base_invariants (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ)
    (hrank : Module.finrank O Oδ = δ) (pi : O) (hpi : Irreducible pi)
    (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    (IsLocalRing.maximalIdeal Oδ).ramificationIdx O = 1 ∧
      (IsLocalRing.maximalIdeal Oδ).inertiaDeg O = δ := by
  have hinj : Function.Injective (algebraMap O Oδ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hpi
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact (Units.map (algebraMap O Oδ : O →* Oδ) u).ne_zero h
    · exact hpiδ.ne_zero (pow_eq_zero_iff'.mp h).1
  have : Algebra.IsIntegral O Oδ := Algebra.IsIntegral.of_finite O Oδ
  have h512 := dvr_extension_maximalIdeal_map_eq_pow O Oδ hinj
  have h1 : (IsLocalRing.maximalIdeal O).map (algebraMap O Oδ) =
      (IsLocalRing.maximalIdeal Oδ) ^ 1 := by
    rw [pow_one, hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      ← hpiδ.maximalIdeal_eq]
  have he : (IsLocalRing.maximalIdeal Oδ).ramificationIdx O = 1 :=
    dvr_maximalIdeal_pow_injective Oδ _ _ (h512.symm.trans h1)
  have : Module.Flat O Oδ := Module.Flat.of_free
  have h251 := finite_flat_local_ramification_degree O Oδ
  rw [he, hrank, one_mul] at h251
  exact ⟨he, h251⟩

/-- In a tower `O → O_δ → B` with `O_δ` unramified of rank `δ` over `O`, inertia degrees over `O`
are `δ` times inertia degrees over `O_δ`.
@isnad1 id=eq.3h5v.s8.9a26a4e37a00 from=translated src=- shape=71a3287c vocab=0a144cf1
-/
theorem inertiaDeg_unramified_tower (O Oδ B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O Oδ] [Algebra O B]
    [Algebra Oδ B] [IsScalarTower O Oδ B] [Module.Finite O Oδ] [Module.Free O Oδ]
    [Module.Finite Oδ B] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O)
    (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    (IsLocalRing.maximalIdeal B).inertiaDeg O =
      δ * (IsLocalRing.maximalIdeal B).inertiaDeg Oδ := by
  have : Algebra.IsIntegral Oδ B := Algebra.IsIntegral.of_finite Oδ B
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal Oδ) :=
    ⟨(integral_local_extension_unique_prime Oδ B).1.symm⟩
  rw [Ideal.inertiaDeg_tower (R := O) (S := Oδ) (IsLocalRing.maximalIdeal Oδ)
    (IsLocalRing.maximalIdeal B), (unramified_base_invariants O Oδ δ hrank pi hpi hpiδ).2]

/-- In a tower `O → O_δ → B` with `O_δ` unramified over `O`, ramification indices over `O` and
over `O_δ` agree.
@isnad1 id=eq.3h5v.s8.25d556424e39 from=translated src=- shape=8e47795c vocab=57a1cb4d
-/
theorem ramificationIdx_unramified_tower (O Oδ B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O Oδ] [Algebra O B]
    [Algebra Oδ B] [IsScalarTower O Oδ B] [Module.Finite O Oδ] [Module.Free O Oδ]
    [Module.Finite Oδ B] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O)
    (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) [Module.Free Oδ B] :
    (IsLocalRing.maximalIdeal B).ramificationIdx O =
      (IsLocalRing.maximalIdeal B).ramificationIdx Oδ := by
  have : Algebra.IsIntegral Oδ B := Algebra.IsIntegral.of_finite Oδ B
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal Oδ) :=
    ⟨(integral_local_extension_unique_prime Oδ B).1.symm⟩
  rw [Ideal.ramificationIdx_tower (R := O) (S := Oδ) (T := B) (IsLocalRing.maximalIdeal Oδ)
    (IsLocalRing.maximalIdeal B), (unramified_base_invariants O Oδ δ hrank pi hpi hpiδ).1,
    one_mul]

/-- For an unramified lift `Φ` with `O[X]/(Φ)` a domain, there is a unique ring map of fraction
fields extending `O → O[X]/(Φ)`; it is injective and makes the target a field extension of degree
`deg Φ`.
@isnad1 id=ex.1h2v.s11.4f875496aae9 from=translated src=- shape=dae954f5 vocab=41535b25
-/
theorem unramified_fraction_field_lift (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] :
    ∃ ι : BaseField O →+* BaseField (AdjoinRoot Φ),
      (∀ c : O, ι (algebraMap O (BaseField O) c) =
        algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) ∧
      Function.Injective ι ∧
      (∀ ι' : BaseField O →+* BaseField (AdjoinRoot Φ),
        (∀ c : O, ι' (algebraMap O (BaseField O) c) =
          algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) →
        ι' = ι) ∧
      (letI := ι.toAlgebra; Module.Finite (BaseField O) (BaseField (AdjoinRoot Φ)) ∧
        Module.finrank (BaseField O) (BaseField (AdjoinRoot Φ)) = Φ.natDegree) := by
  have hmon : Φ.Monic := hΦ.1
  let pb := AdjoinRoot.powerBasis' hmon
  have : Module.Free O (AdjoinRoot Φ) := Module.Free.of_basis pb.basis
  have : Module.Finite O (AdjoinRoot Φ) := pb.finite
  let j : O →+* BaseField (AdjoinRoot Φ) :=
    (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))).comp (algebraMap O (AdjoinRoot Φ))
  have hj : Function.Injective j :=
    (IsFractionRing.injective (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))).comp
      (FaithfulSMul.algebraMap_injective O (AdjoinRoot Φ))
  refine ⟨IsFractionRing.lift hj, fun c => IsFractionRing.lift_algebraMap hj c,
    RingHom.injective (IsFractionRing.lift hj : BaseField O →+* BaseField (AdjoinRoot Φ)),
    fun ι' h => ?_, ?_⟩
  · exact IsFractionRing.ringHom_ext (A := O) (K := BaseField O) fun c => by
      rw [h, IsFractionRing.lift_algebraMap hj c]; rfl
  · let _ : Algebra (BaseField O) (BaseField (AdjoinRoot Φ)) := (IsFractionRing.lift hj).toAlgebra
    have : IsScalarTower O (BaseField O) (BaseField (AdjoinRoot Φ)) :=
      IsScalarTower.of_algebraMap_eq fun c => by
        change _ = IsFractionRing.lift hj _
        rw [IsFractionRing.lift_algebraMap hj c]
        exact IsScalarTower.algebraMap_apply O (AdjoinRoot Φ) _ c
    have hrank : Module.finrank (BaseField O) (BaseField (AdjoinRoot Φ)) = Φ.natDegree := by
      rw [IsFractionRing.finrank_eq O (BaseField O) (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)),
        pb.finrank]
      exact AdjoinRoot.powerBasis'_dim hmon
    refine ⟨?_, hrank⟩
    apply Module.finite_of_finrank_pos
    rw [hrank, ← hmon.natDegree_map (IsLocalRing.residue O)]
    exact Irreducible.natDegree_pos hΦ.2

/-- For monic `Φ`, `O[X]/(Φ)` is a free `O`-module of finite rank `deg Φ`.
@isnad1 id=and.1h2v.s7.81c314024b20 from=translated src=- shape=871c0dd9 vocab=590174de
-/
theorem unramified_free_module (O : Type) [CommRing O] [Nontrivial O] (Φ : Polynomial O)
    (hΦ : Φ.Monic) :
    Module.Free O (AdjoinRoot Φ) ∧ Module.Finite O (AdjoinRoot Φ) ∧
      Module.finrank O (AdjoinRoot Φ) = Φ.natDegree :=
  ⟨hΦ.free_adjoinRoot, hΦ.finite_adjoinRoot, by simp [(AdjoinRoot.powerBasis' hΦ).finrank]⟩

/-- For monic `Φ` over a complete local ring, `O[X]/(Φ)` is complete and separated for the
extended ideal `𝔪 O[X]/(Φ)`, and regular elements of `O` stay regular in it.-/
private theorem unramified_adic_complete (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Φ : Polynomial O) (hΦ : Φ.Monic) :
    IsAdicComplete (baseIdeal O Φ) (AdjoinRoot Φ) ∧
      (∀ x : AdjoinRoot Φ, (∀ L, x ∈ (baseIdeal O Φ)^L) → x = 0) ∧
      (∀ c : O, (∀ y : O, c * y = 0 → y = 0) →
        ∀ x : AdjoinRoot Φ, algebraMap O (AdjoinRoot Φ) c * x = 0 → x = 0) := by
  obtain ⟨hfree, hfin, -⟩ := unramified_free_module O Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · exact (IsAdicComplete.map_algebraMap_iff (S := AdjoinRoot Φ) (M := AdjoinRoot Φ)
      (I := IsLocalRing.maximalIdeal O)).2 (finite_free_adic_complete O (AdjoinRoot Φ) _)
  · intro x hx
    apply (AdjoinRoot.powerBasis' hΦ).basis.repr.injective
    ext i
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    have hi : ∀ L, (AdjoinRoot.powerBasis' hΦ).basis.repr x i ∈ (IsLocalRing.maximalIdeal O)^L :=
      fun L => (base_ideal_coordinates O Φ hΦ L x).1 (hx L) i
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal O))
    intro n
    simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hi n
  · intro c hc x hx
    rw [← Algebra.smul_def] at hx
    apply (AdjoinRoot.powerBasis' hΦ).basis.repr.injective
    ext i
    have := congrArg (fun y => (AdjoinRoot.powerBasis' hΦ).basis.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    exact hc _ this

/-- For an unramified lift `Φ`, the extended ideal `𝔪 O[X]/(Φ)` is maximal, units can be detected
modulo it, and `O[X]/(Φ)` is local with that maximal ideal.
@isnad1 id=and.1h2v.s8.22bae6149a44 from=translated src=- shape=e13f6747 vocab=5467da02
-/
theorem base_ideal_maximal_local (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (baseIdeal O Φ).IsMaximal ∧ (∀ x : AdjoinRoot Φ, IsUnit (baseReduce O Φ x) → IsUnit x) ∧
      ∃ _ : IsLocalRing (AdjoinRoot Φ),
        IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ := by
  have hF := (residue_extension_field O Φ hΦ).1
  have hmax : (baseIdeal O Φ).IsMaximal := Ideal.Quotient.maximal_of_isField _ hF
  have hC := (unramified_adic_complete O Φ hΦ.1).1
  have hloc : IsLocalHom (baseReduce O Φ) :=
    isLocalHom_of_le_jacobson_bot _ (IsAdicComplete.le_jacobson_bot _)
  have hunit : ∀ x : AdjoinRoot Φ, IsUnit (baseReduce O Φ x) → IsUnit x :=
    fun x hx => IsUnit.of_map (baseReduce O Φ) x hx
  let _ : Field (residueExtension O Φ) := hF.toField
  have : Nontrivial (AdjoinRoot Φ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hmax.ne_top (Subsingleton.elim _ _)
  have : IsLocalRing (AdjoinRoot Φ) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    by_cases ha : baseReduce O Φ a = 0
    · right; apply hunit; simp [map_sub, ha]
    · left; exact hunit a (Ne.isUnit ha)
  exact ⟨hmax, hunit, inferInstance, (IsLocalRing.eq_maximalIdeal hmax).symm⟩

/-- An approximate root of `Φ` in `O[X]/(Φ)` (a root modulo `𝔪`) is a simple root: the derivative
of `Φ` there is a unit, already modulo `𝔪`.
@isnad1 id=and.2h3v.s10.bd1eb5a2e8fa from=translated src=- shape=b7d1ee90 vocab=98acce73
-/
theorem simple_root_derivative_unit (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a : AdjoinRoot Φ)
    (ha : baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).eval a) = 0) :
    IsUnit (baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a)) ∧
      IsUnit ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a) := by
  have hle : IsLocalRing.maximalIdeal O ≤ (baseIdeal O Φ).comap (AdjoinRoot.of Φ) :=
    Ideal.map_le_iff_le_comap.1 le_rfl
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.quotientMap (baseIdeal O Φ) (AdjoinRoot.of Φ) hle
  have hcomp : (baseReduce O Φ).comp (AdjoinRoot.of Φ) = ρ.comp (IsLocalRing.residue O) :=
    (Ideal.quotientMap_comp_mk hle).symm
  have key : ∀ p : Polynomial O, baseReduce O Φ ((p.map (AdjoinRoot.of Φ)).eval a)
      = (p.map (IsLocalRing.residue O)).eval₂ ρ (baseReduce O Φ a) := fun p => by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
  let _ : Field (residueExtension O Φ) := (residue_extension_field O Φ hΦ).1.toField
  have hsep : (residuePoly O Φ).Separable := PerfectField.separable_of_irreducible hΦ.2
  have h1 : IsUnit (baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a)) := by
    rw [Polynomial.derivative_map, key, ← Polynomial.derivative_map]
    rw [key] at ha
    exact isUnit_iff_ne_zero.mpr (hsep.eval₂_derivative_ne_zero ρ ha)
  exact ⟨h1, (base_ideal_maximal_local O Φ hΦ).2.1 _ h1⟩

/-! ### The Frobenius automorphism -/

/-- Hensel's lemma produces a root of `Φ` in `O[X]/(Φ)` congruent to `X ^ q` modulo `𝔪`.-/
private theorem frobenius_root_exists (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    ∃ a : AdjoinRoot Φ, (Φ.map (AdjoinRoot.of Φ)).IsRoot a ∧
      a - (AdjoinRoot.root Φ) ^ residueCard O ∈ baseIdeal O Φ := by
  have : IsAdicComplete (baseIdeal O Φ) (AdjoinRoot Φ) := (unramified_adic_complete O Φ hΦ.1).1
  have : HenselianRing (AdjoinRoot Φ) (baseIdeal O Φ) := IsAdicComplete.henselianRing _ _
  have hker : ∀ c ∈ IsLocalRing.maximalIdeal O,
      ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) c = 0 := fun c hc => by
    simp only [RingHom.comp_apply, baseReduce, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hc
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.Quotient.lift _ ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) hker
  have key : ∀ x : AdjoinRoot Φ, baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).eval x)
      = (residuePoly O Φ).eval₂ ρ (baseReduce O Φ x) := fun x => by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, residuePoly, Polynomial.eval₂_map]
    congr 1
  have h0 : baseReduce O Φ
      ((Φ.map (AdjoinRoot.of Φ)).eval (AdjoinRoot.root Φ ^ residueCard O)) = 0 := by
    rw [key, map_pow, residueCard, eval_at_pow_card (IsLocalRing.ResidueField O) _ ρ
      (residuePoly O Φ) (baseReduce O Φ (AdjoinRoot.root Φ)), ← key,
      show (Φ.map (AdjoinRoot.of Φ)).eval (AdjoinRoot.root Φ) = 0 from AdjoinRoot.isRoot_root Φ,
      map_zero, zero_pow Nat.card_pos.ne']
  exact HenselianRing.is_henselian (Φ.map (AdjoinRoot.of Φ)) (hΦ.1.map _)
    (AdjoinRoot.root Φ ^ residueCard O) (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    (simple_root_derivative_unit O Φ hΦ _ h0).1

/-- The Frobenius root is a root of `Φ` congruent to `X ^ q`, and the Frobenius is the
`O`-algebra endomorphism sending `X` to it.-/
private theorem frobenius_root_spec (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (Φ.map (AdjoinRoot.of Φ)).IsRoot (frobeniusRoot O Φ) ∧
      frobeniusRoot O Φ - (AdjoinRoot.root Φ) ^ residueCard O ∈ baseIdeal O Φ ∧
      unramifiedFrobenius O Φ (AdjoinRoot.root Φ) = frobeniusRoot O Φ ∧
      ∀ c : O, unramifiedFrobenius O Φ (algebraMap O (AdjoinRoot Φ) c) =
        algebraMap O (AdjoinRoot Φ) c := by
  have h := frobenius_root_exists O Φ hΦ
  have hr : frobeniusRoot O Φ = Classical.choose h := dite_eq_left h
  exact ⟨hr ▸ (Classical.choose_spec h).1, hr ▸ (Classical.choose_spec h).2,
    AdjoinRoot.liftAlgHom_root _ _ _ _, (unramifiedFrobenius O Φ).commutes⟩

/-- Modulo `𝔪`, the Frobenius acts as `x ↦ x ^ q`, and its `i`-th iterate as `x ↦ x ^ (q ^ i)`.-/
private theorem frobenius_residue_action (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (∀ x : AdjoinRoot Φ,
      baseReduce O Φ (unramifiedFrobenius O Φ x) = (baseReduce O Φ x) ^ residueCard O) ∧
    (∀ (i : ℕ) (x : AdjoinRoot Φ),
      baseReduce O Φ (frobeniusIter O Φ i x) = (baseReduce O Φ x) ^ (residueCard O ^ i)) := by
  obtain ⟨-, hcong, hroot, -⟩ := frobenius_root_spec O Φ hΦ
  have hle : IsLocalRing.maximalIdeal O ≤
      RingHom.ker ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) := fun c hc => by
    rw [RingHom.mem_ker, RingHom.comp_apply, baseReduce, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hc
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.Quotient.lift _ ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) hle
  have hρ : ρ.comp (IsLocalRing.residue O) = (baseReduce O Φ).comp (AdjoinRoot.of Φ) := by
    ext c; rfl
  have key : ∀ (p : Polynomial O) (a : AdjoinRoot Φ),
      baseReduce O Φ (Polynomial.aeval a p) =
        (p.map (IsLocalRing.residue O)).eval₂ ρ (baseReduce O Φ a) := fun p a => by
    rw [Polynomial.eval₂_map, hρ, Polynomial.aeval_def, Polynomial.hom_eval₂]
    rfl
  have h1 : ∀ x : AdjoinRoot Φ, baseReduce O Φ (unramifiedFrobenius O Φ x) =
      (baseReduce O Φ x) ^ residueCard O := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, hroot, key, key]
    have : baseReduce O Φ (frobeniusRoot O Φ) =
        (baseReduce O Φ (AdjoinRoot.root Φ)) ^ residueCard O := by
      rw [← map_pow, baseReduce, Ideal.Quotient.eq]; exact hcong
    rw [this]
    exact eval_at_pow_card _ _ ρ _ _
  refine ⟨h1, fun i => ?_⟩
  induction i with
  | zero => intro x; simp [frobeniusIter]
  | succ i ih =>
    intro x
    change baseReduce O Φ (unramifiedFrobenius O Φ (frobeniusIter O Φ i x)) = _
    rw [h1, ih, ← pow_mul, pow_succ]

private theorem natDegree_pos_of_isUnramifiedLift {O : Type} [CommRing O] [IsLocalRing O]
    {Φ : Polynomial O} (hΦ : IsUnramifiedLift O Φ) : 0 < Φ.natDegree := by
  have := hΦ.2.natDegree_pos
  rwa [residuePoly, hΦ.1.natDegree_map] at this

/-- An element of `O[X]/(Φ)` fixed by the Frobenius modulo `𝔪 ^ L` is congruent to an element of
`O` modulo `𝔪 ^ L`.-/
private theorem frobenius_fixed_mod_pow (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (L : ℕ) (a : AdjoinRoot Φ)
    (ha : unramifiedFrobenius O Φ a - a ∈ (baseIdeal O Φ) ^ L) :
    ∃ c : O, a - algebraMap O (AdjoinRoot Φ) c ∈ (baseIdeal O Φ)^L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set σ := unramifiedFrobenius O Φ
  have hpow : ∀ j : ℕ, (baseIdeal O Φ) ^ j = Ideal.span {algebraMap O (AdjoinRoot Φ) ϖ ^ j} :=
    fun j => by
      rw [baseIdeal, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_pow]
      rfl
  have hmem1 : ∀ x, x ∈ baseIdeal O Φ ↔ ∃ e, x = e * algebraMap O (AdjoinRoot Φ) ϖ := fun x => by
    rw [← pow_one (baseIdeal O Φ), hpow, pow_one, Ideal.mem_span_singleton']
    exact ⟨fun ⟨e, he⟩ => ⟨e, he.symm⟩, fun ⟨e, he⟩ => ⟨e, he.symm⟩⟩
  have htf := (unramified_adic_complete O Φ hΦ.1).2.2
  obtain ⟨hfield, -, -⟩ := residue_extension_field O Φ hΦ
  let _ : Field (residueExtension O Φ) := hfield.toField
  have hres := (frobenius_residue_action O Φ hΦ).1
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.quotientMap (baseIdeal O Φ) (AdjoinRoot.of Φ) Ideal.le_comap_map
  induction L generalizing a with
  | zero => exact ⟨0, by simp⟩
  | succ L ih =>
    obtain ⟨c, hc⟩ := ih a (Ideal.pow_le_pow_right (Nat.le_succ L) ha)
    rw [hpow, Ideal.mem_span_singleton'] at hc ha
    obtain ⟨b, hb⟩ := hc
    obtain ⟨d, hd⟩ := ha
    have ha' : a = algebraMap O (AdjoinRoot Φ) c + b * algebraMap O (AdjoinRoot Φ) ϖ ^ L := by
      rw [hb]; ring
    have hσa : σ a - a = algebraMap O (AdjoinRoot Φ) (ϖ ^ L) * (σ b - b) := by
      rw [ha', map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_pow]; ring
    have hkey : σ b - b = algebraMap O (AdjoinRoot Φ) ϖ * d := by
      have h0 : algebraMap O (AdjoinRoot Φ) (ϖ ^ L) *
          (σ b - b - algebraMap O (AdjoinRoot Φ) ϖ * d) = 0 := by
        rw [mul_sub, ← hσa, ← hd, map_pow]; ring
      exact sub_eq_zero.1 (htf _ (fun y hy => (mul_eq_zero.1 hy).resolve_left
        (pow_ne_zero _ hϖ.ne_zero)) _ h0)
    have hfix : (baseReduce O Φ b) ^ Nat.card (IsLocalRing.ResidueField O) = baseReduce O Φ b := by
      rw [← hres b]
      exact Ideal.Quotient.eq.2 ((hmem1 _).2 ⟨d, by rw [hkey, mul_comm]⟩)
    obtain ⟨r, hr⟩ := (finite_field_frobenius_fixed_points _ _ ρ _).1 hfix
    obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective r
    have hbc : b - algebraMap O (AdjoinRoot Φ) c' ∈ baseIdeal O Φ := by
      apply Ideal.Quotient.eq.1
      rw [← hr]; rfl
    obtain ⟨e, he⟩ := (hmem1 _).1 hbc
    refine ⟨c + ϖ ^ L * c', ?_⟩
    rw [hpow, Ideal.mem_span_singleton']
    refine ⟨e, ?_⟩
    rw [ha', show b = algebraMap O (AdjoinRoot Φ) c' + e * algebraMap O (AdjoinRoot Φ) ϖ by
      rw [← he]; ring, map_add, map_mul, map_pow]
    ring

/-- The elements of `O[X]/(Φ)` fixed by the Frobenius are exactly the elements of `O`.
@isnad1 id=ex.2h3v.s8.3f2937beb7ad from=translated src=- shape=6df11471 vocab=2543a965
-/
theorem frobenius_fixed_ring (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a : AdjoinRoot Φ)
    (ha : unramifiedFrobenius O Φ a = a) :
    ∃ c : O, algebraMap O (AdjoinRoot Φ) c = a := by
  have hc : ∀ L : ℕ, ∃ c : O, a - algebraMap O (AdjoinRoot Φ) c ∈ (baseIdeal O Φ)^L :=
    fun L => frobenius_fixed_mod_pow O Φ hΦ L a (by rw [ha, sub_self]; exact Submodule.zero_mem _)
  choose c hc using hc
  set m := IsLocalRing.maximalIdeal O
  have hpure := base_ideal_pure O Φ hΦ.1 (natDegree_pos_of_isUnramifiedLift hΦ)
  have hcompat : ∀ {L L' : ℕ}, L ≤ L' → c L ≡ c L' [SMOD (m ^ L • ⊤ : Submodule O O)] := by
    intro L L' hLL'
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← hpure]
    have : algebraMap O (AdjoinRoot Φ) (c L - c L') =
        (a - algebraMap O (AdjoinRoot Φ) (c L')) - (a - algebraMap O (AdjoinRoot Φ) (c L)) := by
      rw [map_sub]; ring
    rw [this]; exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hLL' (hc L')) (hc L)
  obtain ⟨c0, hc0⟩ := IsPrecomplete.prec (I := m) inferInstance hcompat
  refine ⟨c0, ?_⟩
  rw [← sub_eq_zero, ← neg_sub, neg_eq_zero]
  refine (unramified_adic_complete O Φ hΦ.1).2.1 _ fun L => ?_
  have h3 : c L - c0 ∈ m ^ L := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hc0 L
  rw [← hpure] at h3
  have : a - algebraMap O (AdjoinRoot Φ) c0 =
      (a - algebraMap O (AdjoinRoot Φ) (c L)) + algebraMap O (AdjoinRoot Φ) (c L - c0) := by
    rw [map_sub]; ring
  rw [this]; exact Ideal.add_mem _ (hc L) h3

/-- Two roots of `Φ` in `O[X]/(Φ)` that are congruent modulo `𝔪` are equal.-/
private theorem root_unique_of_congruent (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a b : AdjoinRoot Φ)
    (ha : (Φ.map (AdjoinRoot.of Φ)).IsRoot a) (hb : (Φ.map (AdjoinRoot.of Φ)).IsRoot b)
    (hab : a - b ∈ baseIdeal O Φ) :
    a = b := by
  set Φ' := Φ.map (AdjoinRoot.of Φ)
  set d := b - a with hd
  have hdI : d ∈ baseIdeal O Φ := by simpa [hd] using (baseIdeal O Φ).neg_mem hab
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion Φ' a d
  rw [show a + d = b by simp [hd]] at hk
  have h0 : d * (Φ'.derivative.eval a + k * d) = 0 := by
    rw [show Φ'.eval b = 0 from hb, show Φ'.eval a = 0 from ha] at hk
    linear_combination -hk
  obtain ⟨v, hv⟩ := (simple_root_derivative_unit O Φ hΦ a (by
    change baseReduce O Φ (Φ'.eval a) = 0
    rw [show Φ'.eval a = 0 from ha, map_zero])).2
  have hC := (unramified_adic_complete O Φ hΦ.1).1
  have hJ : baseIdeal O Φ ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  have hkd : (↑v⁻¹ : AdjoinRoot Φ) * (k * d) ∈ baseIdeal O Φ :=
    (baseIdeal O Φ).mul_mem_left _ ((baseIdeal O Φ).mul_mem_left _ hdI)
  have h1 : IsUnit ((↑v⁻¹ : AdjoinRoot Φ) * (k * d) + 1) := by
    simpa using Ideal.mem_jacobson_bot.mp (hJ hkd) 1
  have h2 : IsUnit (Φ'.derivative.eval a + k * d) := by
    have : Φ'.derivative.eval a + k * d = v * ((↑v⁻¹ : AdjoinRoot Φ) * (k * d) + 1) := by
      rw [← hv, mul_add, ← mul_assoc, Units.mul_inv, one_mul, mul_one, add_comm]
    rw [this]; exact v.isUnit.mul h1
  have : d = 0 := h2.mul_right_cancel (by rw [h0, zero_mul])
  exact (sub_eq_zero.mp this).symm

/-- The `deg Φ`-th iterate of the Frobenius is the identity; in particular the Frobenius is
bijective.
@isnad1 id=and.1h2v.s8.605e2357c2f0 from=translated src=- shape=675a5869 vocab=a8fa570c
-/
theorem frobenius_pow_degree_eq_id (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    frobeniusIter O Φ Φ.natDegree = AlgHom.id O (AdjoinRoot Φ) ∧
      Function.Bijective (unramifiedFrobenius O Φ) := by
  -- roots are preserved by algebra maps
  have hroot : ∀ f : AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ,
      (Φ.map (AdjoinRoot.of Φ)).IsRoot (f (AdjoinRoot.root Φ)) := by
    intro f
    have h0 : Polynomial.aeval (AdjoinRoot.root Φ) Φ = 0 := AdjoinRoot.aeval_eq Φ ▸ by simp
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← AdjoinRoot.algebraMap_eq,
      ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, h0, map_zero]
  have hid : frobeniusIter O Φ Φ.natDegree = AlgHom.id O (AdjoinRoot Φ) := by
    apply AdjoinRoot.algHom_ext
    obtain ⟨hF, hFin, hcard⟩ := residue_extension_field O Φ hΦ
    let _ := hF.toField
    let _ := Fintype.ofFinite (residueExtension O Φ)
    have hc : Fintype.card (residueExtension O Φ) = residueCard O ^ Φ.natDegree := by
      rw [← Nat.card_eq_fintype_card, hcard]
    have h2 := (frobenius_residue_action O Φ hΦ).2 Φ.natDegree (AdjoinRoot.root Φ)
    rw [← hc, FiniteField.pow_card] at h2
    exact root_unique_of_congruent O Φ hΦ _ _ (hroot _) (hroot (AlgHom.id O _))
      (Ideal.Quotient.eq.mp h2)
  refine ⟨hid, ?_⟩
  have hcomm : ∀ i, frobeniusIter O Φ (i+1) =
      (frobeniusIter O Φ i).comp (unramifiedFrobenius O Φ) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih =>
      change (unramifiedFrobenius O Φ).comp (frobeniusIter O Φ (n+1)) = _
      conv_lhs => rw [ih]
      rw [← AlgHom.comp_assoc]; rfl
  obtain ⟨d, hd⟩ : ∃ d, Φ.natDegree = d + 1 :=
    ⟨Φ.natDegree - 1, by have := natDegree_pos_of_isUnramifiedLift hΦ; omega⟩
  rw [Function.bijective_iff_has_inverse]
  refine ⟨frobeniusIter O Φ d, fun x => ?_, fun x => ?_⟩
  · have := congrArg (fun f : AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ => f x) hid
    simp only [hd, hcomm] at this
    exact this
  · have := congrArg (fun f : AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ => f x) hid
    simp only [hd] at this
    exact this

/-- For an unramified lift `Φ`, the ring `O[X]/(Φ)` is an integral domain.-/
private theorem unramified_is_domain (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    IsDomain (AdjoinRoot Φ) := by
  classical
  obtain ⟨hcomp, hsep, htors⟩ := unramified_adic_complete O Φ hΦ.1
  obtain ⟨hfield, -, -⟩ := residue_extension_field O Φ hΦ
  let _ : Field (residueExtension O Φ) := hfield.toField
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set c : AdjoinRoot Φ := algebraMap O (AdjoinRoot Φ) ϖ with hc
  have hI : baseIdeal O Φ = Ideal.span {c} := by
    rw [baseIdeal, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hc,
      AdjoinRoot.algebraMap_eq]
  have hIpow : ∀ L : ℕ, (baseIdeal O Φ) ^ L = Ideal.span {c ^ L} := fun L => by
    rw [hI, Ideal.span_singleton_pow]
  have key : ∀ x : AdjoinRoot Φ, x ≠ 0 → ∃ (i : ℕ) (x' : AdjoinRoot Φ),
      x = c ^ i * x' ∧ x' ∉ baseIdeal O Φ := by
    intro x hx
    have hex : ∃ L, x ∉ (baseIdeal O Φ) ^ L := by
      by_contra h
      push Not at h
      exact hx (hsep x h)
    have hspec := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := fun h0 => hspec (by simp [h0])
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hmem : x ∈ (baseIdeal O Φ) ^ i := by
      simpa using Nat.find_min hex (show i < Nat.find hex by omega)
    rw [hIpow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨x', hx'⟩ := hmem
    refine ⟨i, x', by rw [← hx', mul_comm], fun hx'I => ?_⟩
    rw [hI, Ideal.mem_span_singleton'] at hx'I
    obtain ⟨d, hd⟩ := hx'I
    apply hspec
    rw [hi, hIpow, Ideal.mem_span_singleton']
    exact ⟨d, by rw [← hx', ← hd, pow_succ]; ring⟩
  have hnt : Nontrivial (AdjoinRoot Φ) := (baseReduce O Φ).domain_nontrivial
  have hnzd : NoZeroDivisors (AdjoinRoot Φ) := by
    constructor
    intro a b hab
    by_contra hne
    push Not at hne
    obtain ⟨i, a', rfl, ha'⟩ := key a hne.1
    obtain ⟨j, b', rfl, hb'⟩ := key b hne.2
    have h1 : algebraMap O (AdjoinRoot Φ) (ϖ ^ (i + j)) * (a' * b') = 0 := by
      rw [map_pow, ← hc, ← hab]; ring
    have h2 := htors _ (fun y hy => (mul_eq_zero.1 hy).resolve_left
      (pow_ne_zero _ hϖ.ne_zero)) _ h1
    have h3 : baseReduce O Φ a' * baseReduce O Φ b' = 0 := by
      rw [← map_mul, h2, map_zero]
    rcases mul_eq_zero.1 h3 with h | h
    · exact ha' (Ideal.Quotient.eq_zero_iff_mem.1 h)
    · exact hb' (Ideal.Quotient.eq_zero_iff_mem.1 h)
  exact NoZeroDivisors.to_isDomain _

/-! ### Conjugate products and descent of blocks -/

/-- For a block `b`, the product of the Frobenius conjugates of its monic polynomial is
Frobenius-invariant with coefficients in `O`, monic of degree `δ * r`, and reduces to
`∏ i, (X - θ̄ ^ (q ^ i)) ^ r`.-/
private theorem conjugate_product_invariant (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ)
    (b : Fin r → AdjoinRoot Φ) (hb : b ∈ blockCell O Φ r) :
    (conjugateProduct O Φ (monicPolyO b)).map (unramifiedFrobenius O Φ).toRingHom =
        conjugateProduct O Φ (monicPolyO b) ∧
      (∀ j, ∃ c : O,
        algebraMap O (AdjoinRoot Φ) c = (conjugateProduct O Φ (monicPolyO b)).coeff j) ∧
      (conjugateProduct O Φ (monicPolyO b)).Monic ∧
      (conjugateProduct O Φ (monicPolyO b)).natDegree = Φ.natDegree * r ∧
      (conjugateProduct O Φ (monicPolyO b)).map (baseReduce O Φ) =
        ∏ i : Fin Φ.natDegree, conjugateFactor O Φ i ^ r := by
  have := unramified_is_domain O Φ hΦ
  obtain ⟨hBm, hBd, -, -⟩ := monic_poly_reconstruct (AdjoinRoot Φ) r b
  set B := monicPolyO b
  set δ := Φ.natDegree
  have hid := (frobenius_pow_degree_eq_id O Φ hΦ).1
  have hcomp : ∀ a c : ℕ,
      frobeniusIter O Φ (a + c) = (frobeniusIter O Φ a).comp (frobeniusIter O Φ c) := by
    intro a c
    induction a with
    | zero => simp [frobeniusIter]
    | succ a ih =>
      rw [show a + 1 + c = (a + c) + 1 by omega]
      simp only [frobeniusIter, ih]
      rfl
  have hmul : ∀ m : ℕ, frobeniusIter O Φ (δ * m) = AlgHom.id O (AdjoinRoot Φ) := by
    intro m
    induction m with
    | zero => simp [frobeniusIter]
    | succ m ih => rw [Nat.mul_succ, hcomp, ih, hid]; rfl
  have hmod : ∀ n : ℕ, frobeniusIter O Φ n = frobeniusIter O Φ (n % δ) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n δ]
    rw [hcomp, hmul]; rfl
  have hP : ∀ i : Fin δ, (B.map (frobeniusIter O Φ i).toRingHom).Monic ∧
      (B.map (frobeniusIter O Φ i).toRingHom).natDegree = r := fun i =>
    ⟨hBm.map _, by rw [hBm.natDegree_map, hBd]⟩
  have hinv : (conjugateProduct O Φ B).map (unramifiedFrobenius O Φ).toRingHom =
      conjugateProduct O Φ B := by
    unfold conjugateProduct
    rw [Polynomial.map_prod]
    simp_rw [Polynomial.map_map]
    refine Fintype.prod_equiv (finRotate δ) _ _ (fun i => ?_)
    congr 1
    have hi := i.neZero
    rw [finRotate_apply, hmod ((i + 1 : Fin δ) : ℕ), Fin.val_add]
    have : (unramifiedFrobenius O Φ).toRingHom.comp (frobeniusIter O Φ i).toRingHom
        = (frobeniusIter O Φ ((i : ℕ) + 1)).toRingHom := rfl
    rw [this, hmod]
    congr 2
    simp [Nat.add_mod]
  refine ⟨hinv, fun j => ?_, Polynomial.monic_prod_of_monic _ _ (fun i _ => (hP i).1), ?_, ?_⟩
  · apply frobenius_fixed_ring O Φ hΦ
    simpa [Polynomial.coeff_map] using congrArg (fun p => Polynomial.coeff p j) hinv
  · unfold conjugateProduct
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => (hP i).1),
      Finset.sum_congr rfl (fun i _ => (hP i).2)]
    simp [mul_comm]
  · have hres := (frobenius_residue_action O Φ hΦ).2
    unfold conjugateProduct
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hle : baseIdeal O Φ ≤ (baseIdeal O Φ).comap (frobeniusIter O Φ i).toRingHom := by
      rw [← Ideal.map_le_iff_le_comap, baseIdeal, Ideal.map_map]
      apply le_of_eq
      congr 1
      exact RingHom.ext fun c => (frobeniusIter O Φ i).commutes c
    let g := Ideal.quotientMap (baseIdeal O Φ) (frobeniusIter O Φ i).toRingHom hle
    have hg : (baseReduce O Φ).comp (frobeniusIter O Φ i).toRingHom =
        g.comp (baseReduce O Φ) := by
      ext x <;> simp [g, Ideal.quotientMap_mk]
    rw [Polynomial.map_map, hg, ← Polynomial.map_map, hb, conjugateFactor, conjugateFactor,
      Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 3
    change g (baseReduce O Φ (AdjoinRoot.root Φ) ^ residueCard O ^ 0) = _
    rw [pow_zero, pow_one]
    simp only [g, Ideal.quotientMap_mk]
    exact hres i _

/-- The descent of a block lies in the residue cell of `residuePoly Φ ^ r`, and its monic
polynomial lifts to the conjugate product of the block.
@isnad1 id=and.2h4v.s8.009f40d57dd6 from=translated src=- shape=6a079dc8 vocab=b6ae7738
-/
theorem descend_block_mem_cell (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) (b : Fin r → AdjoinRoot Φ)
    (hb : b ∈ blockCell O Φ r) :
    descendBlock O Φ r b ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r) ∧
      (monicPolyO (descendBlock O Φ r b)).map (AdjoinRoot.of Φ) =
        conjugateProduct O Φ (monicPolyO b) := by
  obtain ⟨_, hdesc, hPm, hPdeg, hPred⟩ := conjugate_product_invariant O Φ hΦ r b hb
  obtain ⟨hcompat, hinj, _, _, hfac, _⟩ := conjugate_roots_distinct O Φ hΦ
  obtain ⟨hFm, hFdeg, hFcoeff, _⟩ :=
    monic_poly_reconstruct O (Φ.natDegree * r) (descendBlock O Φ r b)
  set P := conjugateProduct O Φ (monicPolyO b)
  set F := monicPolyO (descendBlock O Φ r b)
  have hlift : F.map (AdjoinRoot.of Φ) = P := by
    ext j
    rw [Polynomial.coeff_map]
    by_cases hj : j < Φ.natDegree * r
    · rw [show F.coeff j = _ from hFcoeff ⟨j, hj⟩]
      change (AdjoinRoot.of Φ) (descendCoeff O Φ (P.coeff j)) = P.coeff j
      unfold descendCoeff
      rw [dite_eq_left (hdesc j)]
      exact Classical.choose_spec (hdesc j)
    · rcases (not_lt.mp hj).eq_or_lt with h | h
      · subst h
        have h1 : F.coeff (Φ.natDegree * r) = 1 := by
          have := hFm.coeff_natDegree; rwa [hFdeg] at this
        have h2 : P.coeff (Φ.natDegree * r) = 1 := by
          have := hPm.coeff_natDegree; rwa [hPdeg] at this
        rw [h1, h2, map_one]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hFdeg]; exact h),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact h), map_zero]
  refine ⟨?_, hlift⟩
  change F.map (IsLocalRing.residue O) = residuePoly O Φ ^ r
  apply Polynomial.map_injective _ hinj
  have hcomp : (residueEmbed O Φ).comp (IsLocalRing.residue O)
      = (baseReduce O Φ).comp (AdjoinRoot.of Φ) := by
    ext c; exact hcompat c
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hlift, hPred, Polynomial.map_pow, hfac,
    Finset.prod_pow]

end SurfaceBlowup
