/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.SerreTorMultiplicity
import Tengoku.Seed.LinearAlgebra.TensorProduct.Prod
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two-element Koszul resolution

This file constructs the explicit Koszul complex
`0 → A → A × A → A` for a pair `a, b : A`.  If `[a, b]` is weakly regular on
`A`, the complex is a projective resolution of `A/(a,b)`, concentrated in degrees zero through
two.  It therefore supplies finite Tor amplitude and finite-length Euler data without relying on
a Koszul implementation in the frozen Mathlib base.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingTheory.Sequence
open scoped Pointwise

universe u

namespace AlgebraicGeometry.Chow.SerreTor

variable (A : Type u) [CommRing A]

/-- The degree-one differential `(x, y) ↦ a*x + b*y` of the two-element Koszul complex.-/
def koszulPairDOne (a b : A) : A × A →ₗ[A] A where
  toFun x := a * x.1 + b * x.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, mul_add]; abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

/-- The degree-two differential `r ↦ (-b*r, a*r)` of the two-element Koszul complex.-/
def koszulPairDTwo (a b : A) : A →ₗ[A] A × A where
  toFun r := (-b * r, a * r)
  map_add' x y := by ext <;> simp [mul_add]
  map_smul' r x := by
    ext <;> simp only [Prod.smul_mk, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The two Koszul differentials compose to zero.-/
lemma koszulPair_d_comp_d (a b : A) :
    (koszulPairDOne A a b).comp (koszulPairDTwo A a b) = 0 := by
  apply LinearMap.ext
  intro r
  simp [koszulPairDOne, koszulPairDTwo]
  ring

private noncomputable def zeroSuccessor
    (S : ShortComplex (ModuleCat.{u} A)) :
    Σ' (X₃ : ModuleCat.{u} A) (d : X₃ ⟶ S.X₁), d ≫ S.f = 0 :=
  ⟨ModuleCat.of A (Fin 0 → A), 0, by simp⟩

/-- The chain complex `0 → A → A × A → A` attached to `a, b`.-/
noncomputable def koszulPairComplex (a b : A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.mk
    (ModuleCat.of A A) (ModuleCat.of A (A × A)) (ModuleCat.of A A)
    (ModuleCat.ofHom (koszulPairDOne A a b))
    (ModuleCat.ofHom (koszulPairDTwo A a b))
    (ModuleCat.hom_ext (koszulPair_d_comp_d A a b))
    (zeroSuccessor A)

/-- Weak regularity of `[a,b]` identifies the kernel of the first differential with the image
of the second differential.-/
theorem koszulPair_exact_middle (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b]) :
    (ShortComplex.moduleCatMk (koszulPairDTwo A a b) (koszulPairDOne A a b)
      (koszulPair_d_comp_d A a b)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change koszulPairDOne A a b x = 0 at hx
  have hreg := (isWeaklyRegular_cons_iff (ModuleCat.of A A) a [b]).mp reg
  have regA : IsSMulRegular (ModuleCat.of A A) a := hreg.1
  have regB : IsSMulRegular (QuotSMulTop a A) b :=
    (isWeaklyRegular_singleton_iff (QuotSMulTop a A) b).mp hreg.2
  have hbq : b • (Submodule.Quotient.mk x.2 : QuotSMulTop a A) = 0 := by
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.mk_eq_zero (a • (⊤ : Submodule A A))).mpr
    change b * x.2 ∈ a • (⊤ : Submodule A A)
    have heq : b * x.2 = a * (-x.1) := by
      dsimp [koszulPairDOne] at hx
      linear_combination hx
    rw [heq]
    simpa only [smul_eq_mul] using
      Submodule.smul_mem_pointwise_smul (-x.1) a (⊤ : Submodule A A) trivial
  have hx2q : (Submodule.Quotient.mk x.2 : QuotSMulTop a A) = 0 :=
    regB.right_eq_zero_of_smul hbq
  have hx2mem : x.2 ∈ a • (⊤ : Submodule A A) :=
    (Submodule.Quotient.mk_eq_zero (a • (⊤ : Submodule A A))).mp hx2q
  rcases (Submodule.mem_smul_pointwise_iff_exists x.2 a (⊤ : Submodule A A)).mp hx2mem with
    ⟨r, -, har⟩
  have har' : a * r = x.2 := by simpa only [smul_eq_mul] using har
  have ha : a • (x.1 + b * r) = 0 := by
    change a * (x.1 + b * r) = 0
    dsimp [koszulPairDOne] at hx
    rw [← har'] at hx
    linear_combination hx
  have hfirst : x.1 = -b * r := by
    have hz := regA.right_eq_zero_of_smul ha
    linear_combination hz
  refine ⟨r, ?_⟩
  change koszulPairDTwo A a b r = x
  ext
  · exact hfirst.symm
  · exact har'

/-- The two-element Koszul complex vanishes in degrees at least three.-/
theorem koszulPairComplex_isZero (a b : A) (n : ℕ) :
    IsZero ((koszulPairComplex A a b).X (n + 3)) := by
  let Z := ModuleCat.of A (Fin 0 → A)
  have hZ : IsZero Z :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (inferInstance : Subsingleton (Fin 0 → A))
  apply IsZero.of_iso hZ
  exact ChainComplex.mkXIso
    (ModuleCat.of A A) (ModuleCat.of A (A × A)) (ModuleCat.of A A)
    (ModuleCat.ofHom (koszulPairDOne A a b))
    (ModuleCat.ofHom (koszulPairDTwo A a b))
    (ModuleCat.hom_ext (koszulPair_d_comp_d A a b))
    (zeroSuccessor A) n

/-- A weakly regular Koszul pair is exact in every positive degree.-/
theorem koszulPairComplex_exactAt_succ (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b]) (n : ℕ) :
    (koszulPairComplex A a b).ExactAt (n + 1) := by
  obtain _ | n := n
  · rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ x : A × A, koszulPairDOne A a b x = 0 →
      ∃ r : A, koszulPairDTwo A a b r = x
    have h := koszulPair_exact_middle A a b reg
    rw [ShortComplex.moduleCat_exact_iff] at h
    exact h
  · obtain _ | n := n
    · rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)]
      apply (ShortComplex.exact_iff_mono _
        ((koszulPairComplex_isZero A a b 0).eq_of_src _ _)).2
      change Mono (ModuleCat.ofHom (koszulPairDTwo A a b))
      rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      have regA : IsSMulRegular (ModuleCat.of A A) a :=
        ((isWeaklyRegular_cons_iff (ModuleCat.of A A) a [b]).mp reg).1
      apply regA
      have hsnd := congrArg Prod.snd hxy
      change a * x = a * y at hsnd
      simpa only [smul_eq_mul] using hsnd
    · exact HomologicalComplex.ExactAt.of_isZero
        (koszulPairComplex_isZero A a b n)

/-- The canonical quotient map `A → A/(a,b)`, regarded as an `A`-linear map.-/
noncomputable def koszulPairQuotientMap (a b : A) :
    A →ₗ[A] A ⧸ Ideal.span ({a, b} : Set A) :=
  (Ideal.Quotient.mkₐ A (Ideal.span ({a, b} : Set A))).toLinearMap

/-- The first Koszul differential lands in the kernel of the quotient map.-/
lemma koszulPair_quotient_comp (a b : A) :
    (koszulPairQuotientMap A a b).comp (koszulPairDOne A a b) = 0 := by
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (Ideal.span ({a, b} : Set A))
    (a * x.1 + b * x.2) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_pair.mpr
  refine ⟨x.1, x.2, ?_⟩
  ring

/-- The augmentation of the two-element Koszul complex onto `A/(a,b)`.-/
noncomputable def koszulPairAugmentation (a b : A) :
    koszulPairComplex A a b ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨
    ModuleCat.ofHom (koszulPairQuotientMap A a b), by
      change ModuleCat.ofHom (koszulPairDOne A a b) ≫
        ModuleCat.ofHom (koszulPairQuotientMap A a b) = 0
      exact ModuleCat.hom_ext (koszulPair_quotient_comp A a b)⟩

/-- The augmentation sequence `A² → A → A/(a,b)` is exact.-/
theorem koszulPair_augmentation_exact (a b : A) :
    (ShortComplex.moduleCatMk (koszulPairDOne A a b)
      (koszulPairQuotientMap A a b) (koszulPair_quotient_comp A a b)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change koszulPairQuotientMap A a b x = 0 at hx
  change Ideal.Quotient.mk (Ideal.span ({a, b} : Set A)) x = 0 at hx
  rcases Ideal.mem_span_pair.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx) with ⟨r, s, hrs⟩
  refine ⟨(r, s), ?_⟩
  change a * r + b * s = x
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- The canonical projective resolution of `A/(a,b)` associated to a weakly regular pair.-/
noncomputable def koszulPairResolution (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b]) :
    ProjectiveResolution
      (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) where
  complex := koszulPairComplex A a b
  projective n := by
    obtain _ | _ | _ | n := n
    · change Projective (ModuleCat.of A A)
      infer_instance
    · change Projective (ModuleCat.of A (A × A))
      infer_instance
    · change Projective (ModuleCat.of A A)
      infer_instance
    · exact IsZero.projective (koszulPairComplex_isZero A a b n)
  π := koszulPairAugmentation A a b
  quasiIso := ⟨fun n ↦ by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨koszulPair_augmentation_exact A a b, ?_⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by rfl) (by rfl)
        rw [ModuleCat.epi_iff_surjective]
        change Function.Surjective (koszulPairQuotientMap A a b)
        exact Ideal.Quotient.mk_surjective
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply koszulPairComplex_exactAt_succ A a b reg
      · apply ChainComplex.exactAt_succ_single_obj⟩

namespace BoundedProjectiveResolution

/-- A weakly regular pair gives a bounded projective resolution with bound two.-/
noncomputable def koszulPair (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b]) :
    BoundedProjectiveResolution A
      (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) where
  resolution := koszulPairResolution A a b reg
  bound := 2
  isZero n hn := by
    obtain _ | _ | _ | n := n
    · omega
    · omega
    · omega
    · exact koszulPairComplex_isZero A a b n

/-- Tor against `A/(a,b)` vanishes in degrees at least three for a weakly regular pair.-/
theorem isZero_module_koszulPair (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b])
    (M : ModuleCat.{u} A) (n : ℕ) :
    IsZero (module A M
      (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) (n + 3)) := by
  apply (koszulPair A a b reg).isZero_module A M
  change 2 < n + 3
  omega

/-- The high-Tor vanishing theorem transports to every module isomorphic to `A/(a,b)`.-/
theorem isZero_module_of_iso_koszulPair (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b])
    (M : ModuleCat.{u} A) {N' : ModuleCat.{u} A}
    (e : ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A)) ≅ N') (n : ℕ) :
    IsZero (module A M N' (n + 3)) := by
  apply ((koszulPair A a b reg).ofIso A e).isZero_module A M
  change 2 < n + 3
  omega

/-- Finite length of `M` supplies Euler data against a weakly regular two-element quotient.-/
noncomputable def koszulPairEulerData (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b])
    (M : ModuleCat.{u} A) (hM : Module.length A (↑M : Type u) ≠ ⊤) :
    EulerData A M
      (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) :=
  (koszulPair A a b reg).toEulerDataOfFiniteTerms A M (fun n hn ↦ by
    change n ≤ 2 at hn
    have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl | rfl
    · change Module.length A (TensorProduct A (↑M : Type u) A) ≠ ⊤
      rwa [(TensorProduct.rid A (↑M : Type u)).length_eq]
    · change Module.length A (TensorProduct A (↑M : Type u) (A × A)) ≠ ⊤
      rw [(TensorProduct.prodRight A A (↑M : Type u) A A).length_eq,
        Module.length_prod]
      exact WithTop.add_ne_top.mpr ⟨by
        rwa [(TensorProduct.rid A (↑M : Type u)).length_eq], by
        rwa [(TensorProduct.rid A (↑M : Type u)).length_eq]⟩
    · change Module.length A (TensorProduct A (↑M : Type u) A) ≠ ⊤
      rwa [(TensorProduct.rid A (↑M : Type u)).length_eq])

/-- For a weakly regular pair, the Euler characteristic is the alternating sum in degrees
zero, one, and two.-/
theorem koszulPairEulerData_multiplicity (a b : A)
    (reg : IsWeaklyRegular (ModuleCat.of A A) [a, b])
    (M : ModuleCat.{u} A) (hM : Module.length A (↑M : Type u) ≠ ⊤) :
    (koszulPairEulerData A a b reg M hM).multiplicity =
      (length A M (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) 0).toNat -
        (length A M (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) 1).toNat +
          (length A M (ModuleCat.of A (A ⧸ Ideal.span ({a, b} : Set A))) 2).toNat := by
  simp [koszulPairEulerData, toEulerDataOfFiniteTerms, toEulerData,
    koszulPair, EulerData.multiplicity, signedLength, Finset.sum_range_succ,
    sub_eq_add_neg]

end BoundedProjectiveResolution

end AlgebraicGeometry.Chow.SerreTor
