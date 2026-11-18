import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap
set_option autoImplicit false

open ModularCurve Polynomial

namespace QDescent

variable {K₀ k : Type*} [Field K₀] [Field k] (ι : K₀ →+* k)

/--
@isnad1 id=linearin.1h5v.s8.5c156620956c from=translated src=- shape=6a77bfe7 vocab=6aa945d5
-/
theorem linearIndependent_coeffMap {I : Type*} [Fintype I] (v : I → LaurentSeries K₀) (hv : LinearIndependent K₀ v) :
    LinearIndependent k (fun i => coeffMap ι (v i)) := by
  classical
  letI : Algebra K₀ k := ι.toAlgebra
  rw [Fintype.linearIndependent_iff]
  intro c hc i₀
  let B := Module.Free.chooseBasis K₀ k
  suffices h : ∀ l, B.repr (c i₀) l = 0 by
    have : B.repr (c i₀) = 0 := Finsupp.ext h
    simpa using this
  intro l
  have hrel : ∑ i, (B.repr (c i) l) • v i = 0 := by
    ext n
    have hn := congrArg (fun f : LaurentSeries k => B.repr (f.coeff n) l) hc
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, map_sum,
      HahnSeries.coeff_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply] at hn
    rw [HahnSeries.coeff_sum]
    simp only [HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    rw [← hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : c i * ι ((v i).coeff n) = ((v i).coeff n) • c i := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  exact (Fintype.linearIndependent_iff.mp hv) (fun i => B.repr (c i) l) hrel i₀

/--
@isnad1 id=ex.2h6v.s9.d6770579fd4d from=translated src=- shape=01c276da vocab=6f711668
-/
theorem exists_rel_of_rel_coeffMap {I : Type*} [Fintype I] (v : I → LaurentSeries K₀) (c : I → k)
    (hc : ∑ i, c i • coeffMap ι (v i) = 0) (hc0 : c ≠ 0) :
    ∃ d : I → K₀, d ≠ 0 ∧ ∑ i, d i • v i = 0 := by
  classical
  by_contra h
  push Not at h
  have hv : LinearIndependent K₀ v := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    exact (h d (fun h0 => hi (by rw [h0]; rfl))) hd
  have := (Fintype.linearIndependent_iff.mp (linearIndependent_coeffMap ι v hv)) c hc
  exact hc0 (funext this)

/--
@isnad1 id=eq.0h4v.s7.4c441d2b8b68 from=translated src=- shape=b85dfaec vocab=978b8cf8
-/
theorem coeff_sum_monomial {R : Type*} [Semiring R] (n : ℕ) (e : Fin (n + 1) → R) (j : Fin (n + 1)) :
    (∑ i : Fin (n + 1), monomial (i : ℕ) (e i)).coeff (j : ℕ) = e j := by
  rw [finsetSum_coeff, Finset.sum_eq_single j]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro i _ hij
    rw [coeff_monomial, ite_eq_right (fun h => hij (Fin.ext h))]
  · intro h; exact absurd (Finset.mem_univ j) h

variable {K : Type*} [Field K] in
/--
@isnad1 id=eq.1h4v.s9.1e3e399cf454 from=translated src=- shape=6e55af5f vocab=3dcbf972
-/
theorem aeval_eq_sum_single (x : LaurentSeries K) (P : Polynomial K) {n : ℕ} (hn : P.natDegree < n + 1) :
    aeval x P = ∑ i : Fin (n + 1), HahnSeries.C (P.coeff i) * x ^ (i : ℕ) := by
  rw [aeval_def, eval₂_eq_sum_range' _ hn, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]

variable {K : Type*} [Field K] in
/--
@isnad1 id=eq.0h4v.s10.69b9b51dfa25 from=translated src=- shape=462654bc vocab=d4d7c7df
-/
theorem aeval_sum_monomial (n : ℕ) (e : Fin (n + 1) → K) (x : LaurentSeries K) :
    aeval x (∑ i : Fin (n + 1), monomial (i : ℕ) (e i)) = ∑ i : Fin (n + 1), HahnSeries.C (e i) * x ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_monomial, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]

variable {K : Type*} [Field K] in
/--
@isnad1 id=eq.0h3v.s8.a41404014d26 from=translated src=- shape=cd78b1f8 vocab=28c79441
-/
theorem smul_eq_single_mul (a : K) (x : LaurentSeries K) : a • x = HahnSeries.C a * x := by
  rw [← HahnSeries.C_mul_eq_smul]

/--
@isnad1 id=ex.2h5v.s11.30d3e8e7a73c from=translated src=- shape=816f81b6 vocab=d14c5e23
-/
theorem exists_polynomial_mul_aeval_eq_aeval (t r : LaurentSeries K₀) (ht : Transcendental K₀ t)
    (hr : ∃ P Q : Polynomial k, aeval (coeffMap ι t) Q ≠ 0 ∧
      coeffMap ι r * aeval (coeffMap ι t) Q = aeval (coeffMap ι t) P) :
    ∃ P Q : Polynomial K₀, Q ≠ 0 ∧ r * aeval t Q = aeval t P := by
  classical
  obtain ⟨P, Q, hQ, hPQ⟩ := hr
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  set n : ℕ := max P.natDegree Q.natDegree with hn
  set t' := coeffMap ι t with ht'
  set r' := coeffMap ι r with hr'
  let v : Fin (n + 1) ⊕ Fin (n + 1) → LaurentSeries K₀ :=
    fun s => Sum.elim (fun i : Fin (n + 1) => r * t ^ (i : ℕ)) (fun i : Fin (n + 1) => t ^ (i : ℕ)) s
  let c : Fin (n + 1) ⊕ Fin (n + 1) → k :=
    fun s => Sum.elim (fun i : Fin (n + 1) => Q.coeff i) (fun i : Fin (n + 1) => -P.coeff i) s
  have hP' := aeval_eq_sum_single t' P (show P.natDegree < n + 1 by omega)
  have hQ' := aeval_eq_sum_single t' Q (show Q.natDegree < n + 1 by omega)
  have hc : ∑ s, c s • coeffMap ι (v s) = 0 := by
    simp only [smul_eq_single_mul]
    rw [Fintype.sum_sum_type]
    simp only [v, c, Sum.elim_inl, Sum.elim_inr, map_mul, map_pow]
    rw [← ht', ← hr']
    have h1 : ∑ i : Fin (n + 1), HahnSeries.C (Q.coeff ↑i) * (r' * t' ^ (i : ℕ)) = r' * aeval t' Q := by
      rw [hQ', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have h2 : ∑ i : Fin (n + 1), HahnSeries.C (-P.coeff ↑i) * t' ^ (i : ℕ) = -aeval t' P := by
      rw [hP', ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_neg]; ring
    rw [h1, h2, hPQ, add_neg_cancel]
  have hc0 : c ≠ 0 := by
    intro h0
    have hlead : Q.coeff Q.natDegree ≠ 0 := by
      rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hQ0
    have := congrFun h0 (Sum.inl ⟨Q.natDegree, by omega⟩)
    simp only [c, Sum.elim_inl, Pi.zero_apply] at this
    exact hlead this
  obtain ⟨d, hd0, hd⟩ := exists_rel_of_rel_coeffMap ι v c hc hc0
  let Qb : Polynomial K₀ := ∑ i : Fin (n + 1), monomial (i : ℕ) (d (Sum.inl i))
  let Pb : Polynomial K₀ := ∑ i : Fin (n + 1), monomial (i : ℕ) (-d (Sum.inr i))
  have hrel : r * aeval t Qb = aeval t Pb := by
    simp only [smul_eq_single_mul] at hd
    rw [Fintype.sum_sum_type] at hd
    simp only [v, Sum.elim_inl, Sum.elim_inr] at hd
    rw [aeval_sum_monomial, aeval_sum_monomial, Finset.mul_sum]
    have h2 : ∑ i : Fin (n + 1), HahnSeries.C (-d (Sum.inr i)) * t ^ (i : ℕ)
        = -∑ i : Fin (n + 1), HahnSeries.C (d (Sum.inr i)) * t ^ (i : ℕ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_neg]; ring
    rw [h2, eq_neg_iff_add_eq_zero, ← hd]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine ⟨Pb, Qb, ?_, hrel⟩
  intro hQb
  have hPb : aeval t Pb = 0 := by rw [← hrel, hQb, map_zero, mul_zero]
  have hPb0 : Pb ≠ 0 := by
    intro hPb0
    apply hd0
    funext s
    rcases s with i | i
    · have := congrArg (fun P : Polynomial K₀ => P.coeff (i : ℕ)) hQb
      simp only [Qb, coeff_sum_monomial, coeff_zero] at this
      exact this
    · have := congrArg (fun P : Polynomial K₀ => P.coeff (i : ℕ)) hPb0
      simp only [Pb, coeff_sum_monomial, coeff_zero, neg_eq_zero] at this
      exact this
  exact ht ⟨Pb, hPb0, hPb⟩

end QDescent

/--
@isnad1 id=ex.2h5v.s11.30d3e8e7a73c from=translated src=- shape=816f81b6 vocab=d14c5e23
-/
theorem solution
    {K₀ k : Type*} [Field K₀] [Field k] (ι : K₀ →+* k)
    (t r : LaurentSeries K₀) (ht : Transcendental K₀ t)
    (hr : ∃ P Q : Polynomial k, Polynomial.aeval (coeffMap ι t) Q ≠ 0 ∧
      coeffMap ι r * Polynomial.aeval (coeffMap ι t) Q = Polynomial.aeval (coeffMap ι t) P) :
    ∃ P Q : Polynomial K₀, Q ≠ 0 ∧ r * Polynomial.aeval t Q = Polynomial.aeval t P :=
  QDescent.exists_polynomial_mul_aeval_eq_aeval ι t r ht hr
