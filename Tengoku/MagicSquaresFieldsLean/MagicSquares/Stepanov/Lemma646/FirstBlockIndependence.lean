import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.QuotientReduction
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.KummerGaussBridge
import Tengoku.Seed.Algebra.Polynomial.Reverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# From (6.20) to first-block independence

Evaluating the orbit identity at the inverse of a degree-`m` Kummer
root yields a zero orbit factor.  Reflecting that factor produces a
polynomial of degree below `m` vanishing at the root, so the existing
minimal-polynomial argument forces it, and all first-block coefficients,
to vanish.  The final theorems feed this into the block iteration in `Core`.

The normalized Kummer irreducibility hypothesis is explicit here.
`AbsoluteIrreducibility` derives it from absolute irreducibility, and
`Complete` handles translation and assembles the full Lemma 6.46.
-/

/-- A degree-`m` nonzero element has no nonzero polynomial relation of
degree below `m` in its inverse.  Reflection clears the inverse powers.-/
theorem polynomial_eq_zero_of_eval₂_inv_eq_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {m : ℕ} (hm : 0 < m) (Y : L) (hY : Y ≠ 0)
    (hYdeg : (minpoly K Y).natDegree = m)
    (P : Polynomial K) (hP : P.natDegree ≤ m - 1)
    (hroot : P.eval₂ (algebraMap K L) Y⁻¹ = 0) : P = 0 := by
  letI : Invertible (Y⁻¹) := invertibleOfNonzero (inv_ne_zero hY)
  have hreflect := (Polynomial.eval₂_reflect_eq_zero_iff
    (algebraMap K L) (Y⁻¹) (m - 1) P hP).mpr hroot
  have hr : (Polynomial.aeval Y) (P.reflect (m - 1)) = 0 := by
    simpa only [invOf_eq_inv, inv_inv, Polynomial.aeval_def] using hreflect
  have hd : (P.reflect (m - 1)).natDegree < m := by
    exact (Polynomial.natDegree_reflect_le.trans (max_le le_rfl hP)).trans_lt (by omega)
  exact Polynomial.reflect_eq_zero_iff.mp
    (polynomial_eq_zero_of_aeval_eq_zero_of_natDegree_lt_degree Y m hYdeg _ hd hr)

variable {F : Type*} [Field F]

theorem firstBlockPolynomial_coeff_fin {m : ℕ} (a : Fin m → Polynomial F) (i : Fin m) :
    (firstBlockPolynomial a).coeff (i : ℕ) = a i := by
  classical
  simp only [firstBlockPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : (i : ℕ) ≠ (j : ℕ) := by intro h; exact hji (Fin.ext h.symm)
    simp [hne]
  · simp

/-- The polynomial version of the zero-orbit-factor step on LN97 p.303.-/
theorem firstBlock_vanishes_of_inverse_root_orbit
    {L : Type*} [Field L] [Algebra (RatFunc F) L]
    {m : ℕ} (hm : 0 < m) {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (Y : L) (hY : Y ≠ 0) (hYdeg : (minpoly (RatFunc F) Y).natDegree = m)
    (a : Fin m → Polynomial F)
    (hG : (firstBlockSymmetric zeta a).eval₂
      ((algebraMap (RatFunc F) L).comp (algebraMap (Polynomial F) (RatFunc F)))
      ((Y⁻¹) ^ m) = 0) : ∀ i, a i = 0 := by
  let iota : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  let phi : Polynomial F →+* L := (algebraMap (RatFunc F) L).comp iota
  have hB : (firstBlockOrbitProduct zeta a).eval₂ phi Y⁻¹ = 0 := by
    rw [firstBlockOrbit_eq_symmetric_comp hm hzeta, Polynomial.eval₂_comp]
    simpa [phi, iota] using hG
  rw [firstBlockOrbitProduct, domainOrbitProduct, Polynomial.eval₂_finsetProd] at hB
  obtain ⟨j, hj, hfactor⟩ := Finset.prod_eq_zero_iff.mp hB
  let P := domainOrbitFactor (C zeta) (firstBlockPolynomial a) j
  have hP : P.natDegree ≤ m - 1 := by
    calc
      P.natDegree ≤ (firstBlockPolynomial a).natDegree *
          (C ((C zeta) ^ j) * X).natDegree := Polynomial.natDegree_comp_le
      _ ≤ (firstBlockPolynomial a).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        simpa using Polynomial.natDegree_C_mul_le ((C zeta) ^ j) (X : Polynomial (Polynomial F))
      _ ≤ m - 1 := by simpa using firstBlockPolynomial_natDegree_le hm a
  have hzero : P.map iota = 0 := by
    apply polynomial_eq_zero_of_eval₂_inv_eq_zero hm Y hY hYdeg
    · exact Polynomial.natDegree_map_le.trans hP
    · rw [Polynomial.eval₂_map]
      exact hfactor
  have hPzero : P = 0 := Polynomial.map_injective iota (RatFunc.algebraMap_injective F)
    (by simpa using hzero)
  have hscale : (C zeta) ^ j ∈ nonZeroDivisors (Polynomial F) := by
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero _ (Polynomial.C_ne_zero.mpr (hzeta.ne_zero (Nat.ne_of_gt hm))))
  have hA : firstBlockPolynomial a = 0 :=
    (Polynomial.comp_C_mul_X_eq_zero_iff hscale).mp hPzero
  intro i
  have hc := congrArg (fun Q : Polynomial (Polynomial F) => Q.coeff (i : ℕ)) hA
  simpa only [firstBlockPolynomial_coeff_fin, Polynomial.coeff_zero] using hc

/-- The normalization appearing after (6.20).-/
noncomputable def normalizedKummerBase (f : Polynomial F) : Polynomial F :=
  C ((f.eval 0)⁻¹) * f

variable [Fintype F]

/-- The roots of unity required by the orbit construction exist because
the multiplicative group of a finite field is cyclic.-/
theorem exists_primitiveRoot_of_dvd_card_sub_one
    {m : ℕ} (_hm : 0 < m) (hmq : m ∣ Fintype.card F - 1) :
    ∃ zeta : F, IsPrimitiveRoot zeta m := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hu' : IsPrimitiveRoot (u : F) (Fintype.card F - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
    simpa [Nat.card_eq_fintype_card, Fintype.card_units] using hu
  exact ⟨(u : F) ^ ((Fintype.card F - 1) / m),
    hu'.pow (by have := Fintype.one_lt_card (α := F); omega)
      (Nat.div_mul_cancel hmq).symm⟩

/-- The first-block independence needed by `Core`, now derived from a
degree-`m` root of the normalized Kummer polynomial.-/
theorem quotientPowerIndependent_of_kummerRootData
    {m D : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (f : Polynomial F) (hf0 : f.eval 0 ≠ 0)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (K : KummerRootData m (normalizedKummerBase f)) :
    QuotientPowerIndependent m (Fintype.card F) D
      (f ^ ((Fintype.card F - 1) / m)) := by
  intro a ha hrel
  let iota : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  let rho : RatFunc F →+* K.L := algebraMap (RatFunc F) K.L
  have hf : f ≠ 0 := by intro h; simp [h] at hf0
  have hf' : iota f ≠ 0 := RatFunc.algebraMap_ne_zero hf
  have hc : iota (C (f.eval 0)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr hf0)
  have hcinv : iota (C ((f.eval 0)⁻¹)) = (iota (C (f.eval 0)))⁻¹ :=
    map_inv₀ (iota.comp Polynomial.C) (f.eval 0)
  have hnorm : iota (normalizedKummerBase f) = (iota (C (f.eval 0)))⁻¹ * iota f := by
    rw [normalizedKummerBase, map_mul, hcinv]
  have hY : K.Y ≠ 0 := by
    intro hz
    have hp := K.pow_eq
    rw [hz, zero_pow (Nat.ne_of_gt hm)] at hp
    have hp' : rho (iota (normalizedKummerBase f)) = 0 := hp.symm
    rw [hnorm] at hp'
    exact ((_root_.map_ne_zero rho).mpr (mul_ne_zero (inv_ne_zero hc) hf')) hp'
  have hinv : (K.Y⁻¹) ^ m = rho (iota (C (f.eval 0)) / iota f) := by
    rw [inv_pow, K.pow_eq]
    change (rho (iota (normalizedKummerBase f)))⁻¹ = _
    rw [hnorm, map_mul, map_inv₀, mul_inv, inv_inv]
    simp only [div_eq_mul_inv, map_mul, map_inv₀]
  have h620 := ln97_6_20 hm hmq hzeta a ha f hf hbudget hrel
  have hG := congrArg rho h620
  rw [Polynomial.hom_eval₂, map_zero] at hG
  apply firstBlock_vanishes_of_inverse_root_orbit hm hzeta K.Y hY K.minpoly_degree a
  rw [hinv]
  exact hG

/-- Gauss's lemma and the new reduction discharge the quotient-independence
interface from explicit irreducibility of the normalized Kummer polynomial.-/
theorem quotientPowerIndependent_of_normalized_irreducible
    {m D : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (f : Polynomial F) (hf0 : f.eval 0 ≠ 0)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (hirr : Irreducible (kummerPolynomial m (normalizedKummerBase f))) :
    QuotientPowerIndependent m (Fintype.card F) D
      (f ^ ((Fintype.card F - 1) / m)) :=
  quotientPowerIndependent_of_kummerRootData hm hmq hzeta f hf0 hbudget
    (kummerRootDataOfIrreducible hm hirr)

/-- LN97 Lemma 6.46 for `f(0) ≠ 0`, with the
normalized irreducibility hypothesis exposed instead of an assumed
`QuotientPowerIndependent` interface.-/
theorem ln97_6_46_of_normalized_irreducible
    {m D : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (f : Polynomial F) (hf0 : f.eval 0 ≠ 0)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (hirr : Irreducible (kummerPolynomial m (normalizedKummerBase f)))
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hrel : BlockRelation (Fintype.card F) (f ^ ((Fintype.card F - 1) / m)) E) :
    ∀ i, E i = 0 :=
  ln97_6_46_of_quotientPowerIndependent
    (quotientPowerIndependent_of_normalized_irreducible hm hmq hzeta f hf0 hbudget hirr)
    E hdeg hrel

/-- The nonzero-constant case with the book's degree allowance
`D = q / m - deg f`.  Primitive roots and the strict degree budget are
derived internally.  Normalized Kummer irreducibility remains explicit.-/
theorem ln97_6_46_nonzero_constant
    {m : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hf0 : f.eval 0 ≠ 0)
    (hk : 0 < f.natDegree) (hkq : f.natDegree ≤ Fintype.card F / m)
    (hirr : Irreducible (kummerPolynomial m (normalizedKummerBase f)))
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ Fintype.card F / m - f.natDegree)
    (hrel : BlockRelation (Fintype.card F) (f ^ ((Fintype.card F - 1) / m)) E) :
    ∀ i, E i = 0 := by
  obtain ⟨zeta, hzeta⟩ := exists_primitiveRoot_of_dvd_card_sub_one hm hmq
  exact ln97_6_46_of_normalized_irreducible hm hmq hzeta f hf0
    (firstBlock_degree_budget hm hk hkq) hirr E hdeg hrel

end LN97
end MagicSquares
