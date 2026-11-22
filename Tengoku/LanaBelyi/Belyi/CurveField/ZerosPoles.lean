/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.Place
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Zeros and poles of functions on a curve

For a curve field `K`:

* every element has only finitely many zeros and poles
  (`Belyi.CurveField.Place.finite_setOf_ord_ne_zero`,
  `Belyi.CurveField.Place.finite_setOf_notMem`);
* every nonconstant element (i.e. transcendental over `ℚ`) has a zero and a pole
  (`Belyi.CurveField.Place.exists_ord_pos`, `Belyi.CurveField.Place.exists_ord_neg`);
* consequently the elements lying in every place are exactly the constants, i.e. the
  elements algebraic over `ℚ` (`Belyi.CurveField.Place.isAlgebraic_iff_forall_mem`).

Both facts are read off the chart ring `A_f`: the zeros of `f` are the height-one primes of
`A_f` containing `f` (finitely many, and at least one since `f` is not a unit of `A_f`).
-/

open IsDedekindDomain

namespace Belyi.CurveField.Place

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- A nonconstant function has a zero.
@isnad1 id=ex.1h2v.s6.ae701d125af9 from=translated src=- shape=9c570dc4 vocab=0c6b59b3
-/
theorem exists_ord_pos {f : K} (hf : Transcendental ℚ f) : ∃ P : Place K, 0 < P.ord f := by
  have : Fact (Transcendental ℚ f) := ⟨hf⟩
  have hf0 : f ≠ 0 := ne_zero_of_transcendental hf
  let fB : chartRing f := ⟨f, self_mem_chartRing f⟩
  have hfB0 : fB ≠ 0 := fun h ↦ hf0 (congrArg Subtype.val h)
  have hnu : ¬ IsUnit fB := by
    rintro ⟨u, hu⟩
    apply inv_notMem_chartRing hf
    have h1 : f * ((u⁻¹ : (chartRing f)ˣ) : chartRing f) = 1 := by
      have := congrArg Subtype.val u.mul_inv
      rwa [hu] at this
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact ((u⁻¹ : (chartRing f)ˣ) : chartRing f).2
  obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal (Ideal.span {fB})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hMb : M ≠ ⊥ := by
    intro h
    apply hfB0
    rw [← Ideal.mem_bot, ← h]
    exact hfM (Ideal.mem_span_singleton_self fB)
  let v : HeightOneSpectrum (chartRing f) := ⟨M, hM.isPrime, hMb⟩
  refine ⟨ofChart f v, (ord_pos_iff _).mpr ⟨hf0, ?_⟩⟩
  have hv : fB ∈ ((ofChart f v).toChart f (self_mem_ofChart f v)).asIdeal := by
    rw [toChart_ofChart]
    exact hfM (Ideal.mem_span_singleton_self fB)
  exact (mem_toChart_iff f _ _).mp hv

/-- A nonconstant function has a pole.
@isnad1 id=ex.1h2v.s6.fbf0c0b84ede from=translated src=- shape=c04d9a99 vocab=0c6b59b3
-/
theorem exists_ord_neg {f : K} (hf : Transcendental ℚ f) : ∃ P : Place K, P.ord f < 0 := by
  obtain ⟨P, hP⟩ := exists_ord_pos (transcendental_inv hf)
  exact ⟨P, by rw [ord_inv] at hP; omega⟩

/--
@isnad1 id=ex.1h2v.s6.229898a5d3d1 from=translated src=- shape=5a931662 vocab=2972f04a
-/
theorem exists_notMem {f : K} (hf : Transcendental ℚ f) : ∃ P : Place K, f ∉ P.1 := by
  obtain ⟨P, hP⟩ := exists_ord_neg hf
  exact ⟨P, (ord_neg_iff P).mp hP⟩

variable (K) in
instance : Nonempty (Place K) :=
  let ⟨_, ht⟩ := exists_transcendental K
  let ⟨P, _⟩ := exists_ord_pos ht
  ⟨P⟩

/-- An element lying in every place is a constant (algebraic over `ℚ`).
@isnad1 id=isalgebr.1h2v.s6.57f8276b4c3a from=translated src=- shape=35e5ccda vocab=2b7d4fb2
-/
theorem isAlgebraic_of_forall_mem {f : K} (h : ∀ P : Place K, f ∈ P.1) : IsAlgebraic ℚ f := by
  by_contra hf
  obtain ⟨P, hP⟩ := exists_notMem hf
  exact hP (h P)

/--
@isnad1 id=iff.0h2v.s6.1b7bdce63b84 from=translated src=- shape=fe715f31 vocab=2b7d4fb2
-/
theorem isAlgebraic_iff_forall_mem {f : K} : IsAlgebraic ℚ f ↔ ∀ P : Place K, f ∈ P.1 :=
  ⟨fun hf P ↦ P.mem_of_isAlgebraic hf, isAlgebraic_of_forall_mem⟩

/-- A nonzero element has order `0` everywhere iff it is a constant.
@isnad1 id=iff.0h2v.s5.1f99696157b1 from=translated src=- shape=dd353892 vocab=7f7490cd
-/
theorem isAlgebraic_iff_forall_ord_eq_zero {f : K} :
    IsAlgebraic ℚ f ↔ ∀ P : Place K, P.ord f = 0 := by
  refine ⟨fun hf P ↦ P.ord_eq_zero_of_isAlgebraic hf, fun h ↦ ?_⟩
  by_contra hf
  obtain ⟨P, hP⟩ := exists_ord_pos hf
  exact hP.ne' (h P)

/-- A function has only finitely many zeros.
@isnad1 id=finite.0h2v.s5.6c15a6b6deb0 from=translated src=- shape=e8824155 vocab=bbefdf2d
-/
theorem finite_setOf_ord_pos (f : K) : {P : Place K | 0 < P.ord f}.Finite := by
  by_cases hf : IsAlgebraic ℚ f
  · convert Set.finite_empty
    ext P
    simp [P.ord_eq_zero_of_isAlgebraic hf]
  have : Fact (Transcendental ℚ f) := ⟨hf⟩
  have hf0 : f ≠ 0 := ne_zero_of_transcendental hf
  let fB : chartRing f := ⟨f, self_mem_chartRing f⟩
  have hfB0 : fB ≠ 0 := fun h ↦ hf0 (congrArg Subtype.val h)
  have hfin := Ideal.finite_factors (I := Ideal.span {fB}) (by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hfB0)
  refine (hfin.image (ofChart f)).subset ?_
  intro P hP
  have hmem : f ∈ P.1 := P.mem_of_ord_nonneg (le_of_lt hP)
  refine ⟨P.toChart f hmem, ?_, ofChart_toChart f P hmem⟩
  rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton, mem_toChart_iff]
  exact ((P.ord_pos_iff).mp hP).2

/-- A function has only finitely many poles.
@isnad1 id=finite.0h2v.s5.0e09cc124a96 from=translated src=- shape=053a3a7d vocab=bbefdf2d
-/
theorem finite_setOf_ord_neg (f : K) : {P : Place K | P.ord f < 0}.Finite := by
  refine (finite_setOf_ord_pos f⁻¹).subset fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq, ord_inv] at hP ⊢
  omega

/-- A function has only finitely many zeros and poles.
@isnad1 id=finite.0h2v.s5.d0b3d83da3fe from=translated src=- shape=053a3a7d vocab=443b0c34
-/
theorem finite_setOf_ord_ne_zero (f : K) : {P : Place K | P.ord f ≠ 0}.Finite := by
  refine ((finite_setOf_ord_pos f).union (finite_setOf_ord_neg f)).subset fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hP ⊢
  omega

/-- A function lies in all but finitely many places.
@isnad1 id=finite.0h2v.s6.d6fb23dabf09 from=translated src=- shape=f223ceda vocab=c2656694
-/
theorem finite_setOf_notMem (f : K) : {P : Place K | f ∉ P.1}.Finite :=
  (finite_setOf_ord_neg f).subset fun P hP ↦ (ord_neg_iff P).mpr hP

end Belyi.CurveField.Place
