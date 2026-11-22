/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku.LanaIut.Iut.Cor312.ThetaData.PlacesOver
import Tengoku.Seed.Algebra.Polynomial.SpecificDegree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quadratic extensions `K(√d)` inside `F̄`

For a number field `K ⊆ F̄` (an intermediate field of an algebraic closure `F̄` of `F`) and
`d ∈ K`, the field `K(√d) ⊆ F̄` obtained by adjoining a chosen square root of `d` in `F̄`:

* `Iut.sqrtField K d : IntermediateField ↥K Fbar` — the field `K(√d)`, a number field
  (`Iut.instNumberFieldSqrtField`), of degree `≤ 2` over `K` (`Iut.sqrtField_finrank_le`);
* `Iut.sqrtD K d : ↥(sqrtField K d)` — the chosen square root, `Iut.sqrtD_sq`;
* `Iut.conj K d hd : K(√d) ≃ₐ[K] K(√d)` — for `d` **not a square** in `K`, the conjugation
  `√d ↦ -√d` (`Iut.conj_sqrtD`), an involution (`Iut.conj_conj`) fixing exactly `K`
  (`Iut.eq_algebraMap_of_conj_eq`);
* `Iut.exists_sq_eq_of_isSquare` — the trivial case `d` a square in `K`.
-/

namespace Iut

open NumberField Polynomial

variable {F : Type*} [Field F]
variable {Fbar : Type*} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar)

/-! ### The polynomial `X² − d` -/

/-- The polynomial `X² − d` over `K`. -/
noncomputable abbrev sqrtPoly (d : ↥K) : (↥K)[X] := X ^ 2 - C d

/--
@isnad1 id=monic.0h4v.s7.455a358bbad9 from=translated src=- shape=84739327 vocab=0eb5eef7
-/
lemma sqrtPoly_monic (d : ↥K) : (sqrtPoly K d).Monic := monic_X_pow_sub_C d two_ne_zero

/--
@isnad1 id=eq.0h4v.s7.45c76904b151 from=translated src=- shape=d3389358 vocab=25156f3f
-/
lemma sqrtPoly_natDegree (d : ↥K) : (sqrtPoly K d).natDegree = 2 := natDegree_X_pow_sub_C

/--
@isnad1 id=ne.0h4v.s9.1aafff0bc86d from=translated src=- shape=1c75aff5 vocab=fabd1fe6
-/
lemma sqrtPoly_ne_zero (d : ↥K) : sqrtPoly K d ≠ 0 := X_pow_sub_C_ne_zero two_pos d

/-- The trivial case: if `d` is a square in `K` then it has a square root in `K`.
@isnad1 id=ex.1h4v.s9.89f3a15f1ed2 from=translated src=- shape=5a8da146 vocab=12cc999c
-/
theorem exists_sq_eq_of_isSquare {d : ↥K} (hd : IsSquare d) : ∃ y : ↥K, y ^ 2 = d := by
  obtain ⟨r, hr⟩ := hd
  exact ⟨r, by rw [sq, hr]⟩

/--
@isnad1 id=ne.1h4v.s8.48217708b926 from=translated src=- shape=95a8d7a2 vocab=e487a714
-/
lemma ne_zero_of_not_isSquare {d : ↥K} (hd : ¬ IsSquare d) : d ≠ 0 := by
  rintro rfl
  exact hd ⟨0, by simp⟩

/-- `X² − d` is irreducible over `K` when `d` is not a square in `K`.
@isnad1 id=irreduci.1h4v.s9.cbb8c398495b from=translated src=- shape=4b9248d3 vocab=89111352
-/
theorem sqrtPoly_irreducible {d : ↥K} (hd : ¬ IsSquare d) : Irreducible (sqrtPoly K d) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [sqrtPoly_natDegree]; decide
  · intro x hx
    apply hd
    refine ⟨x, ?_⟩
    have : x ^ 2 - d = 0 := by simpa [sqrtPoly] using hx
    rw [← sq, eq_comm, ← sub_eq_zero]
    exact this

/-! ### The chosen square root and the field `K(√d)` -/

variable [IsAlgClosure F Fbar]

/-- A chosen square root in `F̄` of `d ∈ K`. -/
noncomputable def sqrtRoot (d : ↥K) : Fbar :=
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Fbar d) two_pos)

/--
@isnad1 id=eq.0h4v.s8.3b8c8aa84de9 from=translated src=- shape=47ce4250 vocab=baaea77b
-/
lemma sqrtRoot_sq (d : ↥K) : sqrtRoot K d ^ 2 = algebraMap ↥K Fbar d :=
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Fbar d) two_pos)

/--
@isnad1 id=eq.0h4v.s10.5a3f74948826 from=translated src=- shape=2b9ee614 vocab=e8daf790
-/
lemma aeval_sqrtRoot (d : ↥K) : aeval (sqrtRoot K d) (sqrtPoly K d) = 0 := by
  simp [sqrtPoly, sqrtRoot_sq]

/--
@isnad1 id=isintegr.0h4v.s7.3bd0782366b2 from=translated src=- shape=6dce7854 vocab=56dbc9f7
-/
lemma sqrtRoot_isIntegral (d : ↥K) : IsIntegral ↥K (sqrtRoot K d) :=
  ⟨sqrtPoly K d, sqrtPoly_monic K d, by simpa [aeval_def] using aeval_sqrtRoot K d⟩

/--
@isnad1 id=dvd.0h4v.s10.c7a565759211 from=translated src=- shape=f9aa5830 vocab=0cb95c52
-/
lemma minpoly_sqrtRoot_dvd (d : ↥K) : minpoly ↥K (sqrtRoot K d) ∣ sqrtPoly K d :=
  minpoly.dvd _ _ (aeval_sqrtRoot K d)

/-- The field `K(√d) ⊆ F̄`, generated over `K` by the chosen square root of `d`. -/
noncomputable def sqrtField (d : ↥K) : IntermediateField ↥K Fbar :=
  IntermediateField.adjoin ↥K {sqrtRoot K d}

/-- The chosen square root of `d`, as an element of `K(√d)`. -/
noncomputable def sqrtD (d : ↥K) : ↥(sqrtField K d) :=
  ⟨sqrtRoot K d, IntermediateField.mem_adjoin_simple_self ↥K (sqrtRoot K d)⟩

/--
@isnad1 id=eq.0h4v.s8.cce57d6ddc14 from=translated src=- shape=abadb2ff vocab=e743add5
-/
@[simp] lemma coe_sqrtD (d : ↥K) : (sqrtD K d : Fbar) = sqrtRoot K d := rfl

/--
@isnad1 id=eq.0h4v.s8.6f46a70223f5 from=translated src=- shape=fcbd1198 vocab=f9661400
-/
lemma sqrtD_eq_gen (d : ↥K) :
    sqrtD K d = IntermediateField.AdjoinSimple.gen ↥K (sqrtRoot K d) := rfl

/-- `√d ^ 2 = d` in `K(√d)`.
@isnad1 id=eq.0h4v.s12.7875385a51de from=translated src=- shape=88f316de vocab=3439ea56
-/
theorem sqrtD_sq (d : ↥K) : sqrtD K d ^ 2 = algebraMap ↥K ↥(sqrtField K d) d := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, coe_sqrtD, sqrtRoot_sq]
  rfl

/-- `[K(√d) : K] ≤ 2`.
@isnad1 id=le.0h4v.s10.94cdd45bc4a7 from=translated src=- shape=5f237ad9 vocab=11475cbf
-/
theorem sqrtField_finrank_le (d : ↥K) : Module.finrank ↥K ↥(sqrtField K d) ≤ 2 := by
  rw [sqrtField, IntermediateField.adjoin.finrank (sqrtRoot_isIntegral K d)]
  calc (minpoly ↥K (sqrtRoot K d)).natDegree ≤ (sqrtPoly K d).natDegree :=
        natDegree_le_of_dvd (minpoly_sqrtRoot_dvd K d) (sqrtPoly_ne_zero K d)
    _ = 2 := sqrtPoly_natDegree K d

/-! ### The conjugation `√d ↦ -√d` when `d` is not a square -/

/--
@isnad1 id=ne.1h4v.s8.0617f7014cff from=translated src=- shape=0d5d0090 vocab=e1d2422d
-/
lemma sqrtRoot_ne_zero {d : ↥K} (hd : ¬ IsSquare d) : sqrtRoot K d ≠ 0 := by
  intro h
  have h2 := sqrtRoot_sq K d
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero] at h2
  exact ne_zero_of_not_isSquare K hd h2

/--
@isnad1 id=ne.1h4v.s9.84a9e41113e0 from=translated src=- shape=234bdc4a vocab=f2c991d3
-/
lemma sqrtD_ne_zero {d : ↥K} (hd : ¬ IsSquare d) : sqrtD K d ≠ 0 := by
  intro h
  exact sqrtRoot_ne_zero K hd (congrArg Subtype.val h)

/-- `X² − d` is the minimal polynomial of `√d` over `K` when `d` is not a square in `K`.
@isnad1 id=eq.1h4v.s8.ad9c51e9d44e from=translated src=- shape=18b0dd82 vocab=58367b54
-/
theorem minpoly_sqrtRoot {d : ↥K} (hd : ¬ IsSquare d) :
    minpoly ↥K (sqrtRoot K d) = sqrtPoly K d :=
  (minpoly.eq_of_irreducible_of_monic (sqrtPoly_irreducible K hd) (aeval_sqrtRoot K d)
    (sqrtPoly_monic K d)).symm

/-- The power basis `{1, √d}` of `K(√d)` over `K`. -/
noncomputable def sqrtPowerBasis (d : ↥K) : PowerBasis ↥K ↥(sqrtField K d) :=
  IntermediateField.adjoin.powerBasis (sqrtRoot_isIntegral K d)

/--
@isnad1 id=eq.0h4v.s10.f01cbbe51ec1 from=translated src=- shape=1b45bd6e vocab=41185627
-/
lemma sqrtPowerBasis_gen (d : ↥K) : (sqrtPowerBasis K d).gen = sqrtD K d := rfl

/--
@isnad1 id=eq.1h4v.s10.3c4b245a9447 from=translated src=- shape=2a41f6c4 vocab=7caaf884
-/
lemma sqrtPowerBasis_dim {d : ↥K} (hd : ¬ IsSquare d) : (sqrtPowerBasis K d).dim = 2 := by
  show (minpoly ↥K (sqrtRoot K d)).natDegree = 2
  rw [minpoly_sqrtRoot K hd, sqrtPoly_natDegree]

/--
@isnad1 id=eq.1h4v.s10.a30079ae42e8 from=translated src=- shape=39e1c588 vocab=6c4ea93b
-/
lemma minpoly_sqrtD {d : ↥K} (hd : ¬ IsSquare d) :
    minpoly ↥K (sqrtD K d) = sqrtPoly K d := by
  have h := IntermediateField.minpoly_gen (F := ↥K) (sqrtRoot K d)
  rw [minpoly_sqrtRoot K hd] at h
  exact h

/--
@isnad1 id=eq.0h4v.s12.36e0e52cc02e from=translated src=- shape=eb9c0156 vocab=dcdf18af
-/
lemma aeval_neg_sqrtD (d : ↥K) : aeval (-sqrtD K d) (sqrtPoly K d) = 0 := by
  simp [sqrtPoly, sqrtD_sq]

/-- The conjugation `√d ↦ -√d` as a `K`-algebra endomorphism of `K(√d)`. -/
noncomputable def conjHom {d : ↥K} (hd : ¬ IsSquare d) :
    ↥(sqrtField K d) →ₐ[↥K] ↥(sqrtField K d) :=
  (sqrtPowerBasis K d).lift (-sqrtD K d) (by
    rw [sqrtPowerBasis_gen, minpoly_sqrtD K hd]
    exact aeval_neg_sqrtD K d)

/--
@isnad1 id=eq.1h4v.s12.0ce1cc064528 from=translated src=- shape=95b5119e vocab=d6aacbfc
-/
lemma conjHom_sqrtD {d : ↥K} (hd : ¬ IsSquare d) : conjHom K hd (sqrtD K d) = -sqrtD K d :=
  (sqrtPowerBasis K d).lift_gen _ _

/--
@isnad1 id=eq.1h4v.s12.03f2b07492f6 from=translated src=- shape=07b5f246 vocab=b1cb2907
-/
lemma conjHom_comp_conjHom {d : ↥K} (hd : ¬ IsSquare d) :
    (conjHom K hd).comp (conjHom K hd) = AlgHom.id ↥K ↥(sqrtField K d) :=
  (sqrtPowerBasis K d).algHom_ext (by
    rw [sqrtPowerBasis_gen, AlgHom.comp_apply, conjHom_sqrtD, map_neg, conjHom_sqrtD, neg_neg,
      AlgHom.id_apply])

/-- **The conjugation** `√d ↦ -√d` of `K(√d)` over `K`, for `d` not a square in `K`. -/
noncomputable def conj {d : ↥K} (hd : ¬ IsSquare d) :
    ↥(sqrtField K d) ≃ₐ[↥K] ↥(sqrtField K d) :=
  AlgEquiv.ofAlgHom (conjHom K hd) (conjHom K hd) (conjHom_comp_conjHom K hd)
    (conjHom_comp_conjHom K hd)

/--
@isnad1 id=eq.1h5v.s13.e1a705055883 from=translated src=- shape=c4602e64 vocab=e09f4a8f
-/
lemma conj_apply {d : ↥K} (hd : ¬ IsSquare d) (x : ↥(sqrtField K d)) :
    conj K hd x = conjHom K hd x := rfl

/-- The conjugation sends `√d` to `-√d`.
@isnad1 id=eq.1h4v.s12.858d98e2530c from=translated src=- shape=95b5119e vocab=9813683a
-/
@[simp] theorem conj_sqrtD {d : ↥K} (hd : ¬ IsSquare d) : conj K hd (sqrtD K d) = -sqrtD K d :=
  conjHom_sqrtD K hd

/-- The conjugation is an involution.
@isnad1 id=eq.1h5v.s13.2a81a47b663f from=translated src=- shape=d43f1f12 vocab=aab935f1
-/
theorem conj_conj {d : ↥K} (hd : ¬ IsSquare d) (x : ↥(sqrtField K d)) :
    conj K hd (conj K hd x) = x := by
  rw [conj_apply, conj_apply, ← AlgHom.comp_apply, conjHom_comp_conjHom, AlgHom.id_apply]

/-- Every element of `K(√d)` is `a + b √d` with `a, b ∈ K`.
@isnad1 id=ex.1h5v.s13.9edbf150908f from=translated src=- shape=ab17b308 vocab=4dccf2b5
-/
theorem exists_eq_add_mul_sqrtD {d : ↥K} (hd : ¬ IsSquare d) (x : ↥(sqrtField K d)) :
    ∃ a b : ↥K, x = algebraMap ↥K _ a + algebraMap ↥K _ b * sqrtD K d := by
  obtain ⟨f, hf, rfl⟩ := (sqrtPowerBasis K d).exists_eq_aeval x
  rw [sqrtPowerBasis_dim K hd] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [sqrtPowerBasis_gen]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hf)]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  ring

/-! ### `K(√d)` as a number field -/

variable [NumberField ↥K]

/-- The conjugation moves `√d`.
@isnad1 id=ne.1h4v.s12.313805f037ff from=translated src=- shape=e81c807e vocab=de08c070
-/
theorem conj_sqrtD_ne {d : ↥K} (hd : ¬ IsSquare d) : conj K hd (sqrtD K d) ≠ sqrtD K d := by
  rw [conj_sqrtD]
  intro h
  have h2 : (2 : ↥(sqrtField K d)) * sqrtD K d = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact two_ne_zero h0
  · exact sqrtD_ne_zero K hd h0

/-- The conjugation is not the identity.
@isnad1 id=ne.1h4v.s11.0ce8a038b992 from=translated src=- shape=dcda9da4 vocab=312e0e5e
-/
theorem conj_ne_one {d : ↥K} (hd : ¬ IsSquare d) : conj K hd ≠ AlgEquiv.refl := by
  intro h
  exact conj_sqrtD_ne K hd (by rw [h]; rfl)

/-- **The fixed field of the conjugation is `K`.** -/
theorem eq_algebraMap_of_conj_eq {d : ↥K} (hd : ¬ IsSquare d) {x : ↥(sqrtField K d)}
    (hx : conj K hd x = x) : ∃ y : ↥K, algebraMap ↥K _ y = x := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_sqrtD K hd x
  refine ⟨a, ?_⟩
  simp only [map_add, map_mul, AlgEquiv.commutes, conj_sqrtD, mul_neg] at hx
  have h2 : (2 : ↥(sqrtField K d)) * (algebraMap ↥K _ b * sqrtD K d) = 0 := by
    linear_combination -hx
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 two_ne_zero
  rcases mul_eq_zero.mp h0 with h0 | h0
  · rw [h0, zero_mul, add_zero]
  · exact absurd h0 (sqrtD_ne_zero K hd)

end Iut
