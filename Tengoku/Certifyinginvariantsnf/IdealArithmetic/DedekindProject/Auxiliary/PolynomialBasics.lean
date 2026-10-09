import Tengoku

/-! # Polynomials lifts

Basic results on lifts of polynomials mod `π`. -/

open Polynomial Pointwise
open scoped Polynomial

/--
@isnad1 id=iff.1h5v.s8.ed0965c51733 from=translated src=- shape=a34946c5 vocab=e4a82de4
-/
lemma pi_dvd_iff_mod_zero {K R: Type*} [CommRing R] [CommRing K] {q : R →+* K }
    {π : R} (hqker : RingHom.ker q = Ideal.span {π}) (T : Polynomial R) :
    C π ∣ T ↔ map q T = 0 := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]; rw [Polynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero,  ← RingHom.mem_ker, hqker, Ideal.mem_span_singleton]

/--
@isnad1 id=ex.3h6v.s8.c99f6f23865c from=translated src=- shape=ef6556e0 vocab=6e865dd7
-/
lemma exists_of_dvd_mod_pi {K R: Type*} [CommRing R] [CommRing K] {q : R →+* K }
    {π : R} (hqker : RingHom.ker q = Ideal.span {π}) (hqsurj : Function.Surjective q)
    (f h : Polynomial R) :
    map q f ∣ map q h →  ∃ g k : Polynomial R, h = f * g + (C π) * k := by
  rintro ⟨g', hg'⟩
  obtain ⟨g, hg⟩ :=
    (map_surjective q hqsurj)
      g'
  rw [← hg, ← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub,
    ← pi_dvd_iff_mod_zero hqker] at hg'
  obtain ⟨k, hk⟩ :=  hg'
  refine ⟨g, k, ?_ ⟩
  rw [← hk ] ; ring
