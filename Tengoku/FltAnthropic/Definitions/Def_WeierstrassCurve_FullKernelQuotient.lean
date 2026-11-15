import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluQuotientOfSums
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluOrderTwo

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace WeierstrassCurve

def fullKernelQuotient {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (N : ℕ) : WeierstrassCurve F :=
  W.veluQuotientOfSums
    (∑ P ∈ W.oddOrderSummingSet Q (N - 1), W.veluGx P.1 P.2)
    (∑ P ∈ W.oddOrderSummingSet Q (N - 1),
      (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))

/--
@isnad1 id=eq.0h4v.s5.a301c00f23eb from=translated src=- shape=aa3f8426 vocab=e072f880
-/
theorem veluGx_add_veluGx_negY {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    W.veluGx x y + W.veluGx x (W.toAffine.negY x y) = W.veluT x y := by
  simp only [veluGx, veluGy, veluT, Affine.negY]
  ring

/--
@isnad1 id=eq.0h4v.s7.a02e41233eac from=translated src=- shape=838b8a46 vocab=99fe1484
-/
theorem asymWeight_add_asymWeight_negY {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    (x * W.veluGx x y - y * W.veluGy x y) +
        (x * W.veluGx x (W.toAffine.negY x y) -
          W.toAffine.negY x y * W.veluGy x (W.toAffine.negY x y)) =
      W.veluW x y := by
  simp only [veluGx, veluGy, veluT, veluW, veluU, Affine.negY]
  ring

/--
@isnad1 id=eq.1h3v.s6.524d5ff690f4 from=translated src=- shape=500faf14 vocab=51d5df99
-/
theorem coordsOrZero_neg {R : Type*} [CommRing R] {W : WeierstrassCurve R} (P : W.toAffine.Point)
    (hP : P ≠ 0) :
    (-P).coordsOrZero = (P.coordsOrZero.1, W.toAffine.negY P.coordsOrZero.1 P.coordsOrZero.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

theorem eq_of_coordsOrZero_eq {R : Type*} [CommRing R] {W : WeierstrassCurve R} {P P' : W.toAffine.Point}
    (hP : P ≠ 0) (hP' : P' ≠ 0) (h : P.coordsOrZero = P'.coordsOrZero) : P = P' := by
  rcases P with _ | ⟨x, y, hx⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨x', y', hx'⟩
  · exact absurd rfl hP'
  simp only [Affine.Point.coordsOrZero_some, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/--
@isnad1 id=injectiv.0h2v.s5.1461dfd992ac from=translated src=- shape=2213aacb vocab=d2880df6
-/
theorem negPair_injective {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    Function.Injective (fun P : R × R => (P.1, W.toAffine.negY P.1 P.2)) := by
  intro P P' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := congrArg (W.toAffine.negY P.1) h2
  rw [Affine.negY_negY, h1, Affine.negY_negY] at h3
  exact Prod.ext h1 h3

/--
@isnad1 id=eq.1h4v.s7.2b16f0bd4158 from=translated src=- shape=997e2ee2 vocab=28f5ca98
-/
theorem oddOrderSummingSet_two_mul {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) :
    W.oddOrderSummingSet Q (2 * n) =
      W.oddOrderSummingSet Q n ∪
        (W.oddOrderSummingSet Q n).image (fun P => (P.1, W.toAffine.negY P.1 P.2)) := by
  have hrefl : ∀ k, 1 ≤ k → k ≤ 2 * n → (2 * n + 1 - k) • Q = -(k • Q) := fun k hk1 hk2 => by
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← add_nsmul, Nat.sub_add_cancel (by omega), ← hQ, addOrderOf_nsmul_eq_zero]
  have hne : ∀ k, 1 ≤ k → k ≤ 2 * n → k • Q ≠ 0 := fun k hk1 hk2 =>
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  ext P
  simp only [Finset.mem_union, Finset.mem_image, mem_oddOrderSummingSet]
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    by_cases hkn : k ≤ n
    · exact Or.inl ⟨k, hk1, hkn, rfl⟩
    · refine Or.inr ⟨((2 * n + 1 - k) • Q).coordsOrZero, ⟨2 * n + 1 - k, by omega, by omega, rfl⟩, ?_⟩
      rw [hrefl k hk1 hk2, coordsOrZero_neg _ (hne k hk1 hk2), Affine.negY_negY]
  · rintro (⟨k, hk1, hk2, rfl⟩ | ⟨P', ⟨k, hk1, hk2, rfl⟩, rfl⟩)
    · exact ⟨k, hk1, by omega, rfl⟩
    · refine ⟨2 * n + 1 - k, by omega, by omega, ?_⟩
      rw [hrefl k hk1 (by omega), coordsOrZero_neg _ (hne k hk1 (by omega))]

/--
@isnad1 id=disjoint.1h4v.s7.ec372c861707 from=translated src=- shape=c8d95764 vocab=43c9163f
-/
theorem disjoint_oddOrderSummingSet_image_neg {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) :
    Disjoint (W.oddOrderSummingSet Q n)
      ((W.oddOrderSummingSet Q n).image (fun P => (P.1, W.toAffine.negY P.1 P.2))) := by
  have hne : ∀ k, 1 ≤ k → k ≤ n → k • Q ≠ 0 := fun k hk1 hk2 =>
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  rw [Finset.disjoint_left]
  rintro P hP hP'
  rw [mem_oddOrderSummingSet] at hP
  simp only [Finset.mem_image, mem_oddOrderSummingSet] at hP'
  obtain ⟨k, hk1, hk2, rfl⟩ := hP
  obtain ⟨P', ⟨l, hl1, hl2, rfl⟩, h⟩ := hP'
  rw [← coordsOrZero_neg _ (hne l hl1 hl2)] at h
  have hkl : -(l • Q) = k • Q := eq_of_coordsOrZero_eq (neg_ne_zero.mpr (hne l hl1 hl2)) (hne k hk1 hk2) h
  have h0 : (k + l) • Q = 0 := by rw [add_nsmul, ← hkl, neg_add_cancel]
  have hdvd : addOrderOf Q ∣ k + l := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
  rw [hQ] at hdvd
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/--
@isnad1 id=eq.1h5v.s7.4fc2d99908db from=translated src=- shape=3ce5e8e1 vocab=83319f53
-/
theorem sum_oddOrderSummingSet_two_mul {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) (f : F × F → F) :
    ∑ P ∈ W.oddOrderSummingSet Q (2 * n), f P =
      ∑ P ∈ W.oddOrderSummingSet Q n, (f P + f (P.1, W.toAffine.negY P.1 P.2)) := by
  rw [oddOrderSummingSet_two_mul W Q n hQ, Finset.sum_union (disjoint_oddOrderSummingSet_image_neg W Q n hQ),
    Finset.sum_image (fun P _ P' _ h => negPair_injective W h), Finset.sum_add_distrib]

/--
@isnad1 id=eq.1h4v.s7.8c24c793d14e from=translated src=- shape=eda57570 vocab=746fa48f
-/
theorem sum_veluGx_oddOrderSummingSet_two_mul {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) :
    ∑ P ∈ W.oddOrderSummingSet Q (2 * n), W.veluGx P.1 P.2 = W.veluTSum (W.oddOrderSummingSet Q n) := by
  rw [sum_oddOrderSummingSet_two_mul W Q n hQ (fun P => W.veluGx P.1 P.2), veluTSum]
  exact Finset.sum_congr rfl fun P _ => veluGx_add_veluGx_negY W P.1 P.2

/--
@isnad1 id=eq.1h4v.s7.4db350a53770 from=translated src=- shape=90fb5f50 vocab=2053f6f1
-/
theorem sum_asymWeight_oddOrderSummingSet_two_mul {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) :
    ∑ P ∈ W.oddOrderSummingSet Q (2 * n), (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2) =
      W.veluWSum (W.oddOrderSummingSet Q n) := by
  rw [sum_oddOrderSummingSet_two_mul W Q n hQ (fun P => P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2),
    veluWSum]
  exact Finset.sum_congr rfl fun P _ => asymWeight_add_asymWeight_negY W P.1 P.2

/--
@isnad1 id=eq.1h4v.s7.e2a38624f8ed from=translated src=- shape=ae3e3c95 vocab=4d7c8653
-/
theorem fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) :
    W.fullKernelQuotient Q (2 * n + 1) = W.veluQuotient (W.oddOrderSummingSet Q n) := by
  rw [fullKernelQuotient, Nat.add_sub_cancel, sum_veluGx_oddOrderSummingSet_two_mul W Q n hQ,
    sum_asymWeight_oddOrderSummingSet_two_mul W Q n hQ]
  exact (W.veluQuotient_eq_veluQuotientOfSums _).symm

/--
@isnad1 id=eq.0h3v.s5.9eb93c7e16a0 from=translated src=- shape=654b9af3 vocab=174c4ae3
-/
theorem fullKernelQuotient_one {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) : W.fullKernelQuotient Q 1 = W := by
  have h : W.oddOrderSummingSet Q (1 - 1) = ∅ := by
    simp [oddOrderSummingSet]
  rw [fullKernelQuotient, h, Finset.sum_empty, Finset.sum_empty]
  ext <;> simp [veluQuotientOfSums]

/--
@isnad1 id=eq.2h4v.s6.f3c0bcacad7e from=translated src=- shape=57ac4971 vocab=6ecef65c
-/
theorem fullKernelQuotient_two {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) (hgy : W.veluGy x y = 0) :
    W.fullKernelQuotient (.some x y h) 2 = W.veluQuotient2 x y := by
  have hS : W.oddOrderSummingSet (.some x y h) (2 - 1) = {(x, y)} := by
    simp [oddOrderSummingSet]
  rw [fullKernelQuotient, hS]
  simp only [Finset.sum_singleton]
  rw [hgy, mul_zero, sub_zero]
  rfl

end WeierstrassCurve
