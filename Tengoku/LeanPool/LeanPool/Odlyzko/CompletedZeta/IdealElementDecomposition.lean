/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ConeGaussianIntegral
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ConeGaussianInterchange
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.UnitDecomposition

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- An unit shift index used in the Odlyzko-bound argument. -/
abbrev unitShiftIndex :=
  {w : InfinitePlace K // w ≠ w₀} → ℤ

open Classical in
/--
@isnad1 id=eq.0h3v.s7.1293a95c324a from=translated src=- shape=d3007646 vocab=03537683
-/
theorem fundamentalUnitForShift_add (z z' : unitShiftIndex K) :
    fundamentalUnitForShift (z + z') =
      fundamentalUnitForShift z * fundamentalUnitForShift z' := by
  classical
  rw [fundamentalUnitForShift, fundamentalUnitForShift,
    fundamentalUnitForShift, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.add_apply]
  rw [zpow_add]

open Classical in
/--
@isnad1 id=eq.0h1v.s7.bc543cf4bb3c from=translated src=- shape=aef0cf50 vocab=8e17ac6a
-/
@[simp]
theorem fundamentalUnitForShift_zero :
    fundamentalUnitForShift (0 : unitShiftIndex K) = 1 := by
  simp [fundamentalUnitForShift]

open Classical in
/--
@isnad1 id=eq.0h2v.s7.40b6841704ba from=translated src=- shape=59b851a8 vocab=cac9161a
-/
@[simp]
theorem fundamentalUnitForShift_neg (z : unitShiftIndex K) :
    fundamentalUnitForShift (-z) =
      (fundamentalUnitForShift z)⁻¹ := by
  rw [fundamentalUnitForShift, fundamentalUnitForShift]
  simp

open Classical in
/-- A nonzero ideal element used in the Odlyzko-bound argument. -/
abbrev nonzeroIdealElement (J : (Ideal (𝓞 K))⁰) :=
  {x : 𝓞 K // (x : 𝓞 K) ∈ (J : Ideal (𝓞 K)) ∧ x ≠ 0}

open Classical in
/-- An ideal set integer used in the Odlyzko-bound argument. -/
noncomputable def idealSetInteger
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : 𝓞 K :=
  preimageOfMemIntegerSet (idealSetEquiv K J a).val

open Classical in
/--
@isnad1 id=mem.0h3v.s10.50e689905b9d from=translated src=- shape=c8acd3ce vocab=08200a76
-/
theorem idealSetInteger_mem
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetInteger K J a ∈ (J : Ideal (𝓞 K)) := by
  exact (idealSetEquiv K J a).prop

open Classical in
/--
@isnad1 id=ne.0h3v.s9.bad6277a9a4c from=translated src=- shape=098411d3 vocab=d72424fe
-/
theorem idealSetInteger_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetInteger K J a ≠ 0 := by
  exact mem_nonZeroDivisors_iff_ne_zero.mp
    (preimageOfMemIntegerSet (idealSetEquiv K J a).val).2

open Classical in
/--
@isnad1 id=injectiv.0h2v.s9.4a634f87575d from=translated src=- shape=90a3821c vocab=24711b23
-/
theorem idealSetInteger_injective (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealSetInteger K J) := by
  intro a b hab
  apply idealSetElement_injective K J
  exact congrArg (fun x : 𝓞 K ↦ (x : K)) hab

open Classical in
/-- An ideal element decomposition map used in the Odlyzko-bound argument. -/
noncomputable def idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K → nonzeroIdealElement K J :=
  fun p ↦
    ⟨((fundamentalUnitForShift p.2)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J p.1,
      (J : Ideal (𝓞 K)).mul_mem_left _
        (idealSetInteger_mem K J p.1),
      mul_ne_zero (Units.ne_zero _) (idealSetInteger_ne_zero K J p.1)⟩

open Classical in
/--
@isnad1 id=eq.0h3v.s10.32825080cb53 from=translated src=- shape=3caa2dad vocab=47925a3a
-/
@[simp]
theorem idealElementDecompositionMap_coe
    (J : (Ideal (𝓞 K))⁰) (p : idealSet K J × unitShiftIndex K) :
    ((idealElementDecompositionMap K J p : 𝓞 K) : K) =
      (((fundamentalUnitForShift p.2)⁻¹ : (𝓞 K)ˣ) : K) *
        idealSetElement K J p.1 := by
  rfl

open Classical in
/--
@isnad1 id=injectiv.0h2v.s9.8e5e0ee45d85 from=translated src=- shape=f55dcd0c vocab=2a71c0f4
-/
theorem injective_idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealElementDecompositionMap K J) := by
  rintro ⟨a, z⟩ ⟨a', z'⟩ h
  have hval := congrArg
    (fun t : nonzeroIdealElement K J ↦ (t : 𝓞 K)) h
  change
    ((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J a =
      ((fundamentalUnitForShift z')⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J a' at hval
  let v : (𝓞 K)ˣ :=
    fundamentalUnitForShift z' * (fundamentalUnitForShift z)⁻¹
  have haeq :
      (v : 𝓞 K) * idealSetInteger K J a =
        idealSetInteger K J a' := by
    calc
      (v : 𝓞 K) * idealSetInteger K J a =
          (fundamentalUnitForShift z' : 𝓞 K) *
            (((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
              idealSetInteger K J a) := by
        simp only [v, Units.val_mul]
        ring
      _ = (fundamentalUnitForShift z' : 𝓞 K) *
            (((fundamentalUnitForShift z')⁻¹ : (𝓞 K)ˣ) *
              idealSetInteger K J a') := congrArg _ hval
      _ = idealSetInteger K J a' := by simp
  have haembed :
      mixedEmbedding K ((idealSetInteger K J a : 𝓞 K) : K) =
        (a : mixedSpace K) := by
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  have haembed' :
      mixedEmbedding K ((idealSetInteger K J a' : 𝓞 K) : K) =
        (a' : mixedSpace K) := by
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  have hsmul : v • (a : mixedSpace K) = (a' : mixedSpace K) := by
    rw [unitSMul_smul]
    grind
  have hv : v ∈ torsion K :=
    (unit_smul_mem_iff_mem_torsion a.prop.1 v).mp
      (hsmul ▸ a'.prop.1)
  have hvshift :
      v = fundamentalUnitForShift (z' + -z) := by
    rw [fundamentalUnitForShift_add,
      fundamentalUnitForShift_neg]
  have hp :
      ((⟨v, hv⟩ : torsion K), (0 : unitShiftIndex K)) =
        (1, z' + -z) := by
    apply (unitDecompositionEquiv K).injective
    simp_all
  have : z' = z := by grind
  subst z'
  apply Prod.ext
  · apply idealSetInteger_injective K J
    exact mul_left_cancel₀ (Units.ne_zero _) hval
  · simp

open Classical in
/--
@isnad1 id=surjecti.0h2v.s9.f8b2e6f908ca from=translated src=- shape=f55dcd0c vocab=f3dcaa79
-/
theorem surjective_idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    Function.Surjective (idealElementDecompositionMap K J) := by
  intro x
  have hxemb :
      mixedEmbedding K ((x : 𝓞 K) : K) ≠ 0 := by
    exact (map_ne_zero_iff (mixedEmbedding K)
      (mixedEmbedding_injective K)).mpr
        (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
  have hxnorm :
      mixedEmbedding.norm
          (mixedEmbedding K ((x : 𝓞 K) : K)) ≠ 0 :=
    (norm_eq_zero_iff'
      (Set.mem_range_self ((x : 𝓞 K) : K))).not.mpr hxemb
  obtain ⟨u, hu⟩ :=
    exists_unit_smul_mem hxnorm
  let a : idealSet K J :=
    ⟨u • mixedEmbedding K ((x : 𝓞 K) : K),
      mem_idealSet.mpr
        ⟨hu, ⟨(u : 𝓞 K) * x,
          (J : Ideal (𝓞 K)).mul_mem_left _ x.prop.1, by
            simp⟩⟩⟩
  have haInteger :
      idealSetInteger K J a = (u : 𝓞 K) * x := by
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
    change u • mixedEmbedding K ((x : 𝓞 K) : K) =
      mixedEmbedding K (((u : 𝓞 K) * x : 𝓞 K) : K)
    simp
  let p := (unitDecompositionEquiv K).symm u
  let ζ : torsion K := p.1
  let z : unitShiftIndex K := p.2
  have huDecomp :
      (ζ : (𝓞 K)ˣ) * fundamentalUnitForShift z = u := by
    have hp := (unitDecompositionEquiv K).apply_symm_apply u
    change unitDecompositionEquiv K (ζ, z) = u at hp
    simp_all
  have hζinv : ((ζ : (𝓞 K)ˣ)⁻¹) ∈ torsion K :=
    (torsion K).inv_mem ζ.prop
  let b : idealSet K J :=
    ⟨((ζ : (𝓞 K)ˣ)⁻¹) • (a : mixedSpace K),
      mem_idealSet.mpr
        ⟨torsion_smul_mem_of_mem a.prop.1 hζinv,
          ⟨(↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
              idealSetInteger K J a,
            (J : Ideal (𝓞 K)).mul_mem_left _
              (idealSetInteger_mem K J a), by
              rw [unitSMul_smul]
              push_cast
              rw [map_mul]
              rw [idealSetInteger,
                mixedEmbedding_preimageOfMemIntegerSet,
                idealSetEquiv_apply]⟩⟩⟩
  have hbInteger :
      idealSetInteger K J b =
        (↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          idealSetInteger K J a := by
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
    change ((ζ : (𝓞 K)ˣ)⁻¹) • (a : mixedSpace K) =
      mixedEmbedding K
        ((((↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          idealSetInteger K J a : 𝓞 K) : K))
    rw [unitSMul_smul]
    push_cast
    rw [map_mul]
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  refine ⟨(b, z), ?_⟩
  apply Subtype.ext
  change
    ((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J b = x
  rw [hbInteger, haInteger, ← huDecomp]
  calc
    (↑((fundamentalUnitForShift z)⁻¹) : 𝓞 K) *
        ((↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          (((ζ : (𝓞 K)ˣ) : 𝓞 K) *
            (fundamentalUnitForShift z : 𝓞 K) * x)) =
      ((↑((fundamentalUnitForShift z)⁻¹) : 𝓞 K) *
          (↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          ((ζ : (𝓞 K)ˣ) : 𝓞 K) *
          (fundamentalUnitForShift z : 𝓞 K)) * x := by ring
    _ = x := by simp

open Classical in
/-- An ideal element decomposition equiv used in the Odlyzko-bound argument. -/
noncomputable def idealElementDecompositionEquiv
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K ≃ nonzeroIdealElement K J :=
  Equiv.ofBijective (idealElementDecompositionMap K J)
    ⟨injective_idealElementDecompositionMap K J,
      surjective_idealElementDecompositionMap K J⟩

open Classical in
/--
@isnad1 id=eq.0h3v.s9.2b4c96bd8681 from=translated src=- shape=fb4e4164 vocab=95395095
-/
@[simp]
theorem idealElementDecompositionEquiv_apply
    (J : (Ideal (𝓞 K))⁰)
    (p : idealSet K J × unitShiftIndex K) :
    idealElementDecompositionEquiv K J p =
      idealElementDecompositionMap K J p :=
  rfl

open Classical in
/-- An unit shift neg equiv used in the Odlyzko-bound argument. -/
def unitShiftNegEquiv : unitShiftIndex K ≃ unitShiftIndex K where
  toFun z := -z
  invFun z := -z
  left_inv z := neg_neg z
  right_inv z := neg_neg z

open Classical in
/-- An ideal element mul decomposition equiv used in the Odlyzko-bound argument. -/
noncomputable def idealElementMulDecompositionEquiv
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K ≃ nonzeroIdealElement K J :=
  (Equiv.prodCongr (Equiv.refl _) (unitShiftNegEquiv K)).trans
    (idealElementDecompositionEquiv K J)

open Classical in
/--
@isnad1 id=eq.0h3v.s10.d967fb95f9b7 from=translated src=- shape=07a0ebc8 vocab=273b4248
-/
@[simp]
theorem idealElementMulDecompositionEquiv_coe
    (J : (Ideal (𝓞 K))⁰)
    (p : idealSet K J × unitShiftIndex K) :
    (((idealElementMulDecompositionEquiv K J p :
        nonzeroIdealElement K J) : 𝓞 K) : K) =
      ((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) *
        idealSetElement K J p.1 := by
  change
    (((idealElementDecompositionEquiv K J (p.1, -p.2) :
        nonzeroIdealElement K J) : 𝓞 K) : K) = _
  simp

end NumberField.Odlyzko
