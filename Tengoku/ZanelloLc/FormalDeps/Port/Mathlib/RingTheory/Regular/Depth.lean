/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
module

public import Tengoku.Seed.Algebra.Category.Grp.Zero
public import Tengoku.Seed.Algebra.Category.ModuleCat.Ext.HasExt
public import Tengoku.Seed.Algebra.Module.FinitePresentation
public import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
public import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Localization
public import Tengoku.ZanelloLc.FormalDeps.Port.Mathlib.RingTheory.Regular.Category
public import Tengoku.Seed.RingTheory.Regular.IsSMulRegular
public import Tengoku.Seed.RingTheory.Regular.LinearMap
public import Tengoku.Seed.RingTheory.Regular.RegularSequence
public import Tengoku.Seed.RingTheory.Spectrum.Prime.Topology
public import Tengoku.Seed.RingTheory.Support
public import Tengoku.Seed.Tactic.ENatToNat
public import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Hom(N,M) is subsingleton iff there exists a smul regular element of M in ann(N)

Let `M` and `N` be `R`-modules. In this section we prove that `Hom(N,M)` is subsingleton iff
there exist `r : R`, such that `IsSMulRegular M r` and `r ∈ ann(N)`.
This is the case if `Depth[I](M) = 0`.

## Main statements

* `IsSMulRegular.subsingleton_linearMap_iff` : for `R` module `N M`, `Hom(N, M) = 0`
  iff there is a `M`-regular in `Module.annihilator R N`.

-/

@[expose] public section
namespace Tengoku.ZanelloLc end Tengoku.ZanelloLc open Tengoku.ZanelloLc 
universe w v u

open IsLocalRing LinearMap Module

/-!

# The Rees theorem

In this section we proved the rees theorem for depth, which build the relation between
the vanishing order of `Ext` and maximal regular sequence.

# Main results

* `exist_isRegular_tfae` : for `n : ℕ`, noetherian ring `R`, `I : Ideal R`,
  `M : ModuleCat R` finitely generated and nontrivial satisfying `IM < M`, we proved TFAE,
  · for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
    zerolucus of `I`, `∀ i < n, Ext N M i = 0`
  · `∀ i < n, Ext (A⧸I) M i = 0`
  · there exist a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
    zerolucus of `I`, `∀ i < n, Ext N M i = 0`
  · there exist a `M`-regular sequence of length `n` with every element in `I`

-/

open IsLocalRing LinearMap
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R] [Small.{v} R]

open Pointwise ModuleCat IsSMulRegular

lemma _root_.Tengoku.ZanelloLc.exist_isRegular_tfae_3_to_4 [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    ∀ M : ModuleCat.{v} R, Nontrivial M → Module.Finite R M →
    I • (⊤ : Submodule R M) < ⊤ → (∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
    Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i)) →
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n
  · intro M ntr M_fin smul_lt exist_N
    use []
    simp [isRegular_iff]
  · rename_i n ih
    intro M ntrM M_fin smul_lt exist_N
    rcases exist_N with ⟨N, ntr, fin, h_supp, h_ext⟩
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    have : Subsingleton (N →ₗ[R] M) :=
      let _ := h_ext 0 n.zero_lt_succ
      let _ : Subsingleton (N ⟶ M) := Ext.addEquiv₀.symm.subsingleton
      (ModuleCat.homAddEquiv (M := N) (N := M)).symm.subsingleton
    rcases subsingleton_linearMap_iff.mp this with ⟨x, mem_ann, hx⟩
    have := Ideal.le_radical mem_ann
    rw [h_supp', Ideal.mem_radical_iff] at this
    rcases this with ⟨k, hk⟩
    have hxk := IsSMulRegular.pow k hx
    let M' := QuotSMulTop (x ^ k) M
    have le_smul : x ^ k • (⊤ : Submodule R M) ≤ I • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact (Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk))
    have ntr' : Nontrivial M' :=
      Submodule.Quotient.nontrivial_iff.mpr (lt_of_lt_of_le' smul_lt le_smul).ne
    have smul_lt' : I • (⊤ : Submodule R M') < ⊤ := by
      rw [lt_top_iff_ne_top]
      by_contra eq
      absurd lt_top_iff_ne_top.mp smul_lt
      have := Submodule.smul_top_eq_comap_smul_top_of_surjective I
        (Submodule.mkQ ((x ^ k) • (⊤ : Submodule R M))) (Submodule.mkQ_surjective _)
      simpa [eq, le_smul] using this
    have exist_N' : (∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R M') i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi
      have zero1 : IsZero (AddCommGrpCat.of (Ext N M i)) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext i (Nat.lt_add_right 1 hi))
      have zero2 : IsZero (AddCommGrpCat.of (Ext N M (i + 1))) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N hxk.smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    rcases ih (ModuleCat.of R M') ntr'
      (Module.Finite.quotient R _) smul_lt' exist_N' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hxk, reg⟩

section

lemma CategoryTheory.Abelian.extFunctorObj_zero_preserve_momoMorphism (L M N : ModuleCat.{v} R)
    (f : M ⟶ N) (mono : Mono f) :
    Mono (AddCommGrpCat.ofHom <| ((Ext.mk₀ f)).postcomp L (add_zero 0)) := by
  apply ConcreteCategory.mono_of_injective
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply (AddSubgroup.eq_bot_iff_forall _).mpr (fun x hx ↦ ?_)
  simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.mem_ker, AddMonoidHom.flip_apply,
    Ext.bilinearComp_apply_apply] at hx
  rw [← Ext.mk₀_homEquiv₀_apply x, Ext.mk₀_comp_mk₀] at hx
  have : (Ext.addEquiv₀ x ≫ f) = 0 := (AddEquiv.map_eq_zero_iff Ext.addEquiv₀.symm).mp hx
  exact (AddEquiv.map_eq_zero_iff Ext.addEquiv₀).mp (zero_of_comp_mono f this)

lemma CategoryTheory.Abelian.extFunctor_post_apply_zero_preserve_momoMorphism
    (L M N : ModuleCat.{v} R) (g : M ⟶ N) (mono : Epi g) :
    Mono (AddCommGrpCat.ofHom <| ((Ext.mk₀ g)).precomp L (zero_add 0)) := by
  apply ConcreteCategory.mono_of_injective
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply (AddSubgroup.eq_bot_iff_forall _).mpr (fun x hx ↦ ?_)
  simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.mem_ker, Ext.bilinearComp_apply_apply] at hx
  rw [← Ext.mk₀_homEquiv₀_apply x, Ext.mk₀_comp_mk₀] at hx
  have : (g  ≫ Ext.addEquiv₀ x) = 0 := (AddEquiv.map_eq_zero_iff Ext.addEquiv₀.symm).mp hx
  exact (AddEquiv.map_eq_zero_iff Ext.addEquiv₀).mp (zero_of_epi_comp g this)

end

/-!

# The Definition of Depth

In this section, we give the definition of depth of a module over a local ring. We also extablished
some basic facts about it using the Rees theorem proven above.
In this section, we set `R` be a noetherian commutative ring, all modules refer to `R`-module.

# Main definition and results

* `moduleDepth` : The depth between two `R`-modules defined as the minimal nontrivial `Ext`
  between them, equal to `⊤ : ℕ∞` if no such index.

* `Ideal.depth` : The depth of a `R`-module `M` with respect to an ideal `I`,
  defined as `moduleDepth (R⧸ I, M)`.

* `IsLocalRing.depth` : For a local ring `R`, the depth of a `R`-module with respect to
  the maximal ideal.

* `moduleDepth_eq_depth_of_supp_eq` : For `I : Ideal R`, if support of a finitely generated module
  `N` is equal to `PrimeSpectrum.zeroLocus I`, then for any finitely generated nontrivial module
  `M` with `IM < M`, `moduleDepth N M = I.depth M`

* `moduleDepth_eq_sSup_length_regular` : For `I : Ideal R`, nontrivial finitely generated module
  `M` and N`, if support of `N` is equal to `PrimeSpectrum.zeroLocus I` and `IM < M`,
  `moduleDepth N M` is equal to the supremum of length of `M`-regular sequence in `I`

* `IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth` : For `R` local, a `R`-module `M` and a
  `M`-regular element `x` in `maximalIdeal R`,
  `IsLocalRing.depth (QuotSMulTop x M) + 1 = IsLocalRing.depth M`

* `moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth` : For `R` local, a `R`-module
  `M` and a `M`-regular sequence `rs` in `maximalIdeal R`,
  `moduleDepth N (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M)) + rs.length = moduleDepth N M`

-/

section depth

/-- The depth between two `R`-modules defined as the minimal nontrivial `Ext` between them.-/
noncomputable def _root_.Tengoku.ZanelloLc.moduleDepth (N M : ModuleCat.{v} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}

/-- The depth of a `R`-module `M` with respect to an ideal `I`,
defined as `moduleDepth (R⧸ I, M)`.-/
noncomputable def Ideal.depth (I : Ideal R) (M : ModuleCat.{v} R) : ℕ∞ :=
  moduleDepth (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M

/-- For a local ring `R`, the depth of a `R`-module with respect to the maximal ideal.-/
noncomputable def IsLocalRing.depth [IsLocalRing R] (M : ModuleCat.{v} R) : ℕ∞ :=
  (IsLocalRing.maximalIdeal R).depth M

open Classical in
lemma _root_.Tengoku.ZanelloLc.moduleDepth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext N M n)) :
    moduleDepth N M = Nat.find h := by
  apply le_antisymm
  · simp only [moduleDepth, sSup_le_iff, Set.mem_ofPred_eq]
    intro n hn
    by_contra gt
    absurd Nat.find_spec h
    exact not_nontrivial_iff_subsingleton.mpr (hn (Nat.find h) (not_le.mp gt))
  · simp only [moduleDepth]
    apply le_sSup
    simp only [Set.mem_ofPred_eq, Nat.cast_lt, Nat.lt_find_iff]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mp (hi i (le_refl i))

lemma _root_.Tengoku.ZanelloLc.moduleDepth_eq_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! exist
    rw [moduleDepth_eq_find N M exist] at h
    simp at h
  · simp [moduleDepth]
    exact csSup_eq_top_of_top_mem (fun i _ ↦ h i)

lemma _root_.Tengoku.ZanelloLc.moduleDepth_lt_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M < ⊤ ↔ ∃ n, Nontrivial (Ext N M n) := by
  convert (moduleDepth_eq_top_iff N M).not
  · exact lt_top_iff_ne_top
  · push_neg
    rfl

lemma _root_.Tengoku.ZanelloLc.moduleDepth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : moduleDepth N M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨ntr, h⟩ ↦ ?_⟩
  · have exist := (moduleDepth_lt_top_iff N M).mp (by simp [h])
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj] at h
    refine ⟨h ▸ Nat.find_spec exist, fun i hi ↦ ?_⟩
    exact not_nontrivial_iff_subsingleton.mp (Nat.find_min exist (lt_of_lt_of_eq hi h.symm))
  · have exist : ∃ n, Nontrivial (Ext N M n) := by use n
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj, Nat.find_eq_iff, ntr, true_and]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mpr (h i hi)

lemma _root_.Tengoku.ZanelloLc.ext_subsingleton_of_lt_moduleDepth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < moduleDepth N M) : Subsingleton (Ext N M i) := by
  by_cases lttop : moduleDepth N M < ⊤
  · let _ : Nonempty {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)} :=
      Nonempty.intro ⟨(0 : ℕ∞), by simp⟩
    exact ENat.sSup_mem_of_nonempty_of_lt_top lttop i lt
  · simp only [not_lt, top_le_iff, moduleDepth_eq_top_iff] at lttop
    exact lttop i

lemma _root_.Tengoku.ZanelloLc.moduleDepth_eq_sup_nat (N M : ModuleCat.{v} R) : moduleDepth N M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  simp only [moduleDepth]
  by_cases h : ⊤ ∈ {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)}
  · rw [csSup_eq_top_of_top_mem h, eq_comm, ENat.eq_top_iff_forall_ge]
    intro m
    apply le_sSup
    simp only [Set.mem_ofPred_eq, ENat.natCast_lt_top, forall_const] at h
    simpa using fun i _ ↦ h i
  · congr
    ext n
    exact ⟨fun mem ↦ ⟨top_notMem_iff.mp h n mem, mem⟩, fun mem ↦ mem.2⟩

open Opposite in
lemma _root_.Tengoku.ZanelloLc.moduleDepth_eq_of_iso_fst (M : ModuleCat.{v} R) {N N' : ModuleCat.{v} R} (e : N ≅ N') :
    moduleDepth N M = moduleDepth N' M := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    (((extFunctor.{v} i).mapIso e.symm.op).app M).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma _root_.Tengoku.ZanelloLc.moduleDepth_eq_of_iso_snd (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    moduleDepth N M = moduleDepth N M' := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    ((extFunctorObj N i).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma Ideal.depth_eq_of_iso (I : Ideal R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    I.depth M = I.depth M' :=
  moduleDepth_eq_of_iso_snd (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) e

lemma IsLocalRing.depth_eq_of_iso [IsLocalRing R] {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    IsLocalRing.depth M = IsLocalRing.depth M' :=
  (maximalIdeal R).depth_eq_of_iso e

lemma _root_.Tengoku.ZanelloLc.moduleDepth_eq_zero_of_hom_nontrivial (N M : ModuleCat.{v} R) :
    moduleDepth N M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [moduleDepth] at h
    have : 1 ∉ {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)} := by
      by_contra mem
      absurd le_sSup mem
      simp [h]
    simp only [Set.mem_ofPred_eq, Nat.cast_lt_one, forall_eq,
      not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr] at this
    exact (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mp this
  · apply nonpos_iff_eq_zero.mp (sSup_le (fun n mem ↦ ?_))
    by_contra pos
    absurd mem 0 (lt_of_not_ge pos)
    simpa [not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr]
      using (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mpr h

lemma _root_.Tengoku.ZanelloLc.moduleDepth_ge_min_of_shortExact_snd_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₂ N ≥ moduleDepth S.X₁ N ⊓ moduleDepth S.X₃ N := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrpCat.of (Ext S.X₁ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₂' hS N i)
    (zero3.eq_zero_of_src _) (zero1.eq_zero_of_tgt _)

lemma _root_.Tengoku.ZanelloLc.moduleDepth_ge_min_of_shortExact_fst_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₁ N ≥ moduleDepth S.X₂ N ⊓ (moduleDepth S.X₃ N - 1) := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi2 hi3
  have zero2 : IsZero (AddCommGrpCat.of (Ext S.X₂ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  have hi3' : (i + 1 : ℕ) < moduleDepth S.X₃ N := by
    simpa using lt_tsub_iff_right.mp hi3
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N (i + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3')
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₁' hS N i (i + 1) (add_comm _ _))
    (zero2.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)

lemma _root_.Tengoku.ZanelloLc.moduleDepth_ge_min_of_shortExact_trd_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₃ N ≥ moduleDepth S.X₂ N ⊓ (moduleDepth S.X₁ N + 1) := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi2 hi1
  have zero2 : IsZero (AddCommGrpCat.of (Ext S.X₂ N i)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  by_cases eq0 : i = 0
  · rw [eq0] at zero2 ⊢
    have := extFunctor_post_apply_zero_preserve_momoMorphism.{v} N _ _ S.g hS.epi_g
    exact AddCommGrpCat.subsingleton_of_isZero <| @zero2.of_mono _ _ _ _ _ _ this
  · have hi1' : (i - 1 : ℕ) < moduleDepth S.X₁ N := by
      have : i - 1 + 1 = i := Nat.succ_pred_eq_of_ne_zero eq0
      rw [← this, Nat.cast_add, Nat.cast_one] at hi1
      exact lt_of_add_lt_add_right hi1
    have zero1 : IsZero (AddCommGrpCat.of (Ext S.X₁ N (i - 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1')
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.contravariant_sequence_exact₃' hS N (i - 1) i (by omega))
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

lemma _root_.Tengoku.ZanelloLc.moduleDepth_ge_min_of_shortExact_snd_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₂ ≥ moduleDepth N S.X₁ ⊓ moduleDepth N S.X₃ := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrpCat.of (Ext N S.X₁ i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₂' N hS i)
    (zero1.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)

lemma _root_.Tengoku.ZanelloLc.moduleDepth_ge_min_of_shortExact_fst_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₁ ≥ moduleDepth N S.X₂ ⊓ (moduleDepth N S.X₃ + 1) := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi2 hi3
  have zero2 : IsZero (AddCommGrpCat.of (Ext N S.X₂ i)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  by_cases eq0 : i = 0
  · rw [eq0] at zero2 ⊢
    have := extFunctorObj_zero_preserve_momoMorphism.{v} N _ _ S.f hS.mono_f
    exact AddCommGrpCat.subsingleton_of_isZero <| @zero2.of_mono _ _ _ _ _ _ this
  · have hi3' : (i - 1 : ℕ) < moduleDepth N S.X₃ := by
      have : i - 1 + 1 = i := Nat.succ_pred_eq_of_ne_zero eq0
      rw [← this, Nat.cast_add, Nat.cast_one] at hi3
      exact lt_of_add_lt_add_right hi3
    have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ (i - 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3')
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.covariant_sequence_exact₁' N hS (i - 1) i (by omega))
      (zero3.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

lemma _root_.Tengoku.ZanelloLc.moduleDepth_ge_min_of_shortExact_trd_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₃ ≥ moduleDepth N S.X₂ ⊓ (moduleDepth N S.X₁ - 1) := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi2 hi1
  have zero2 : IsZero (AddCommGrpCat.of (Ext N S.X₂ i)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  have hi1' : (i + 1 : ℕ) < moduleDepth N S.X₁ := by
    simpa using lt_tsub_iff_right.mp hi1
  have zero1 : IsZero (AddCommGrpCat.of (Ext N S.X₁ (i + 1))) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1')
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl)
    (zero2.eq_zero_of_src _) (zero1.eq_zero_of_tgt _)

omit [Small.{v, u} R] in
lemma Submodule.comap_lt_top_of_lt_range {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (p : Submodule R N)
    (lt : p < LinearMap.range f) : Submodule.comap f p < ⊤ := by
  obtain ⟨x, ⟨y, hy⟩, nmem⟩ : ∃ x ∈ LinearMap.range f, x ∉ p := Set.exists_of_ssubset lt
  have : y ∉ Submodule.comap f p := by simpa [hy] using nmem
  exact lt_of_le_not_ge (fun _ a ↦ trivial) fun a ↦ this (a trivial)

lemma _root_.Tengoku.ZanelloLc.moduleDepth_quotSMulTop_succ_eq_moduleDepth (N M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (QuotSMulTop x M)) + 1 = moduleDepth N M := by
  simp only [moduleDepth, add_comm]
  have iff (i : ℕ) : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) ↔
    (Subsingleton (Ext N M i) ∧ Subsingleton (Ext N M (i + 1))) := by
    refine ⟨fun h ↦ ?_, fun ⟨h1, h3⟩ ↦ ?_⟩
    · constructor
      · exact @Function.Injective.subsingleton _ _ _ ((AddCommGrpCat.mono_iff_injective _).mp
          (ShortComplex.Exact.mono_g
          (Ext.covariant_sequence_exact₂' N reg.smulShortComplex_shortExact i)
          (ext_hom_eq_zero_of_mem_ann mem i))) h
      · exact @Function.Surjective.subsingleton _ _ _ h ((AddCommGrpCat.epi_iff_surjective _).mp
          (ShortComplex.Exact.epi_f
          (Ext.covariant_sequence_exact₁' N reg.smulShortComplex_shortExact i (i + 1) rfl)
          (ext_hom_eq_zero_of_mem_ann mem (i + 1))))
    · exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' N reg.smulShortComplex_shortExact i (i + 1) rfl)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h1).eq_zero_of_src _)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h3).eq_zero_of_tgt _)
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    by_cases eq0 : i = 0
    · rw [eq0, Ext.addEquiv₀.subsingleton_congr, ModuleCat.homAddEquiv.subsingleton_congr]
      exact linearMap_subsingleton_of_mem_annihilator reg mem
    · have eq : i - 1 + 1 = i := Nat.sub_one_add_one eq0
      have : i - 1 < n := by
        enat_to_nat
        omega
      have := ((iff (i - 1)).mp (hn (i - 1) this)).2
      simpa only [eq] using this
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        enat_to_nat
        omega
      rw [add_comm, ← this]
      apply add_le_add_left
      apply le_sSup
      intro i hi
      have lt2 : i + 1 < n := by
        enat_to_nat
        omega
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

lemma Ideal.depth_quotSMulTop_succ_eq_moduleDepth (I : Ideal R) (M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ I) :
    I.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = I.depth M := by
  apply moduleDepth_quotSMulTop_succ_eq_moduleDepth _ M x reg
  simpa [LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ I)), Ideal.annihilator_quotient]

lemma IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth [IsLocalRing R] (M : ModuleCat.{v} R)
    (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = IsLocalRing.depth M :=
  (maximalIdeal R).depth_quotSMulTop_succ_eq_moduleDepth M x reg mem

lemma _root_.Tengoku.ZanelloLc.moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth (N M : ModuleCat.{v} R)
    (rs : List R) (reg : IsWeaklyRegular M rs) (h : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    moduleDepth N M := by
  generalize len : rs.length = n
  induction n generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using moduleDepth_eq_of_iso_snd N (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  · rename_i n hn
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [moduleDepth_eq_of_iso_snd N
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso,
        ← moduleDepth_quotSMulTop_succ_eq_moduleDepth N M x this (h x List.mem_cons_self),
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
        (fun r hr ↦ h r (List.mem_cons_of_mem x hr)) len, add_assoc]

lemma _root_.Tengoku.ZanelloLc.ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth (I : Ideal R)
    (M : ModuleCat.{v} R) (rs : List R) (reg : IsWeaklyRegular M rs)
    (h : ∀ r ∈ rs, r ∈ I) :
    I.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    I.depth M := by
  apply moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth _ M rs reg
  convert h
  rw [LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ I)), Ideal.annihilator_quotient]

lemma _root_.Tengoku.ZanelloLc.depth_quotient_regular_sequence_add_length_eq_depth [IsLocalRing R]
    (M : ModuleCat.{v} R) (rs : List R)
    (reg : IsRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    IsLocalRing.depth M := by
  apply ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth _ M rs reg.toIsWeaklyRegular
  intro r hr
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  by_contra isu
  absurd reg.2
  simp [eq_top_of_isUnit_mem (ofList rs) (Ideal.subset_span hr) isu]

section ring

local instance (R : Type*) [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
    IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective

end ring

end depth

end
-- Tengoku: root names of this library moved to Tengoku.ZanelloLc so they do not collide with other libraries (generated)
