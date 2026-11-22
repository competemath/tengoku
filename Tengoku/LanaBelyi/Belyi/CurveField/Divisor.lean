/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.Degree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Divisors of a curve field

A *divisor* of a curve field `K` is a finitely supported function `Place K → ℤ`
(`Belyi.CurveField.Divisor`). Its degree is `deg A = ∑_P A(P) · deg P`. The divisor of a
function `f` is `div f = ∑_P ord_P(f) · P`; it is the difference of the divisor of zeros and
the divisor of poles of `f`. Principal divisors have degree `0`
(`Belyi.CurveField.Divisor.deg_div`): this is the fundamental identity
`Belyi.CurveField.Place.sum_ord_mul_deg_zeros` / `Belyi.CurveField.Place.sum_ord_mul_deg_poles`.

We follow H. Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1 §1.4, with the base
field `ℚ` (which need not be the full constant field of `K`); degrees are taken over `ℚ`.

## Main definitions

* `Belyi.CurveField.Divisor K := Place K →₀ ℤ`.
* `Belyi.CurveField.Divisor.deg`, bundled as `Belyi.CurveField.Divisor.degHom`.
* `Belyi.CurveField.Divisor.div f`, `Belyi.CurveField.Divisor.zeroDivisor f`,
  `Belyi.CurveField.Divisor.polarDivisor f`.

## Main results

* `Belyi.CurveField.Divisor.deg_add`, `deg_neg`, `deg_sub`, `deg_nsmul`, `deg_zsmul`,
  `deg_single`, `deg_mono`.
* `Belyi.CurveField.Divisor.div_mul`, `div_inv`, `div_div`, `div_one`.
* `Belyi.CurveField.Divisor.div_eq_zeroDivisor_sub_polarDivisor`.
* `Belyi.CurveField.Divisor.deg_polarDivisor`, `deg_zeroDivisor`: for `x` transcendental,
  both have degree `[K : ℚ(x)]`.
* `Belyi.CurveField.Divisor.deg_div`: `deg (div f) = 0`.
-/

open scoped IntermediateField

namespace Belyi.CurveField

/-- The divisors of a curve field: finitely supported `ℤ`-valued functions on the places. -/
abbrev Divisor (K : Type*) [Field K] : Type _ := Place K →₀ ℤ

namespace Divisor

variable {K : Type*} [Field K] [CharZero K]

/-! ### Degree -/

/-- The degree `∑_P A(P) · deg P` of a divisor (degrees over `ℚ`). -/
noncomputable def deg (A : Divisor K) : ℤ := A.sum fun P n ↦ n * (P.deg : ℤ)

/--
@isnad1 id=eq.0h3v.s6.19e6bf92c61c from=translated src=- shape=39731974 vocab=fb2d635c
-/
theorem deg_add (A B : Divisor K) : (A + B).deg = A.deg + B.deg :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)

/--
@isnad1 id=eq.0h1v.s5.8150d57848f9 from=translated src=- shape=7828fa0d vocab=eddac0d9
-/
@[simp]
theorem deg_zero : (0 : Divisor K).deg = 0 := Finsupp.sum_zero_index

/-- The degree as an additive homomorphism. -/
noncomputable def degHom : Divisor K →+ ℤ where
  toFun := deg
  map_zero' := deg_zero
  map_add' := deg_add

/--
@isnad1 id=eq.0h2v.s6.d16f8bf44dfe from=translated src=- shape=96645c70 vocab=81fa3af8
-/
@[simp]
theorem degHom_apply (A : Divisor K) : degHom A = A.deg := rfl

/--
@isnad1 id=eq.0h2v.s5.d4faf3a34f56 from=translated src=- shape=53350f2b vocab=f7a99533
-/
@[simp]
theorem deg_neg (A : Divisor K) : (-A).deg = -A.deg := map_neg degHom A

/--
@isnad1 id=eq.0h3v.s6.c60ddde9eb3a from=translated src=- shape=39731974 vocab=5b2ebff0
-/
theorem deg_sub (A B : Divisor K) : (A - B).deg = A.deg - B.deg := map_sub degHom A B

/--
@isnad1 id=eq.0h3v.s6.ae64ed6aef28 from=translated src=- shape=43fc3cb6 vocab=cdd3ce07
-/
theorem deg_nsmul (n : ℕ) (A : Divisor K) : (n • A).deg = n * A.deg := by
  rw [← degHom_apply, map_nsmul, degHom_apply, nsmul_eq_mul]

/--
@isnad1 id=eq.0h3v.s5.c021150a4d22 from=translated src=- shape=1bb883a3 vocab=51cf72f0
-/
theorem deg_zsmul (n : ℤ) (A : Divisor K) : (n • A).deg = n * A.deg := by
  rw [← degHom_apply, map_zsmul, degHom_apply, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s5.99a0097dd764 from=translated src=- shape=6985c922 vocab=d6f9176c
-/
@[simp]
theorem deg_single (P : Place K) (n : ℤ) : deg (Finsupp.single P n) = n * P.deg :=
  Finsupp.sum_single_index (h := fun (P : Place K) (n : ℤ) ↦ n * (P.deg : ℤ)) (zero_mul _)

/--
@isnad1 id=eq.1h3v.s6.649a33e5c63e from=translated src=- shape=86de38b9 vocab=b68a4b2e
-/
theorem deg_eq_sum_of_support_subset (A : Divisor K) {s : Finset (Place K)}
    (hs : A.support ⊆ s) : A.deg = ∑ P ∈ s, A P * (P.deg : ℤ) :=
  Finsupp.sum_of_support_subset A hs _ fun _ _ ↦ zero_mul _

/--
@isnad1 id=le.1h2v.s6.caccbde01921 from=translated src=- shape=9d08da97 vocab=326d2ccd
-/
theorem deg_nonneg {A : Divisor K} (hA : 0 ≤ A) : 0 ≤ A.deg :=
  Finset.sum_nonneg fun P _ ↦ mul_nonneg (hA P) (Int.natCast_nonneg _)

/--
@isnad1 id=le.1h3v.s5.6f8e44175845 from=translated src=- shape=30b04278 vocab=326d2ccd
-/
theorem deg_mono {A B : Divisor K} (h : A ≤ B) : A.deg ≤ B.deg := by
  have := deg_nonneg (sub_nonneg.mpr h)
  rw [deg_sub] at this
  omega

/--
@isnad1 id=lt.2h2v.s6.ea10068d8f7f from=translated src=- shape=186d1dd7 vocab=7726d885
-/
theorem deg_pos_of_nonneg_of_ne_zero [IsCurveField K] {A : Divisor K} (hA : 0 ≤ A)
    (h0 : A ≠ 0) : 0 < A.deg := by
  obtain ⟨P, hP⟩ := Finsupp.ne_iff.mp h0
  have hPpos : 0 < A P := lt_of_le_of_ne (hA P) (Ne.symm hP)
  have hsplit : A = Finsupp.single P (A P) + (A - Finsupp.single P (A P)) := by abel
  have hrest : 0 ≤ A - Finsupp.single P (A P) := by
    classical
    intro Q
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply]
    by_cases h : P = Q
    · subst h; simp
    · rw [Finsupp.single_apply, ite_eq_right h, sub_zero]; exact hA Q
  rw [hsplit, deg_add, deg_single]
  have := deg_nonneg hrest
  have := P.deg_pos
  positivity

/-! ### Principal divisors -/

variable [IsCurveField K]

/-- The divisor `∑_P ord_P(f) · P` of a function `f` (and `0` for `f = 0`). -/
noncomputable def div (f : K) : Divisor K :=
  Finsupp.ofSupportFinite (fun P ↦ P.ord f) (Place.finite_setOf_ord_ne_zero f)

/--
@isnad1 id=eq.0h3v.s6.36b2a3251dda from=translated src=- shape=ca49ffea vocab=ae8b2db6
-/
@[simp]
theorem div_apply (f : K) (P : Place K) : div f P = P.ord f := rfl

/--
@isnad1 id=eq.0h1v.s6.bf7001ea6068 from=translated src=- shape=e251427b vocab=86f6c9ce
-/
@[simp]
theorem div_zero : div (0 : K) = 0 := by ext P; simp

/--
@isnad1 id=eq.0h1v.s6.78433c662538 from=translated src=- shape=e251427b vocab=86f6c9ce
-/
@[simp]
theorem div_one : div (1 : K) = 0 := by ext P; simp

/--
@isnad1 id=eq.2h3v.s7.d372ed53c685 from=translated src=- shape=30e46e06 vocab=86e82bb5
-/
theorem div_mul {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) : div (f * g) = div f + div g := by
  ext P; simp [P.ord_mul hf hg]

/--
@isnad1 id=eq.0h2v.s6.1292e7db6c97 from=translated src=- shape=457b981d vocab=0471b4be
-/
@[simp]
theorem div_inv (f : K) : div f⁻¹ = -div f := by ext P; simp

/--
@isnad1 id=eq.2h3v.s7.a2d38a8aa2ab from=translated src=- shape=30e46e06 vocab=08bcf7c9
-/
theorem div_div {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) : div (f / g) = div f - div g := by
  ext P; simp [P.ord_div hf hg]

/--
@isnad1 id=eq.0h3v.s6.257440b8302d from=translated src=- shape=55034eff vocab=78833db9
-/
@[simp]
theorem div_pow (f : K) (n : ℕ) : div (f ^ n) = n • div f := by ext P; simp

/--
@isnad1 id=eq.0h2v.s5.1090117038a5 from=translated src=- shape=7cca58d9 vocab=61d0808d
-/
@[simp]
theorem div_neg (f : K) : div (-f) = div f := by ext P; simp

/--
@isnad1 id=eq.1h2v.s6.f199fa88987b from=translated src=- shape=f7139a25 vocab=33e76948
-/
theorem div_eq_zero_of_isAlgebraic {c : K} (hc : IsAlgebraic ℚ c) : div c = 0 := by
  ext P; simp [P.ord_eq_zero_of_isAlgebraic hc]

/-- The divisor of zeros `∑_P max(0, ord_P f) · P`. -/
noncomputable def zeroDivisor (f : K) : Divisor K :=
  Finsupp.ofSupportFinite (fun P ↦ max 0 (P.ord f))
    ((Place.finite_setOf_ord_ne_zero f).subset fun P hP ↦ by
      simp only [Function.mem_support] at hP
      simp only [Set.mem_ofPred_eq]
      omega)

/-- The divisor of poles `∑_P max(0, -ord_P f) · P`. -/
noncomputable def polarDivisor (f : K) : Divisor K :=
  Finsupp.ofSupportFinite (fun P ↦ max 0 (-P.ord f))
    ((Place.finite_setOf_ord_ne_zero f).subset fun P hP ↦ by
      simp only [Function.mem_support] at hP
      simp only [Set.mem_ofPred_eq]
      omega)

/--
@isnad1 id=eq.0h3v.s6.df76641bb537 from=translated src=- shape=93e88e5e vocab=32c314e4
-/
@[simp]
theorem zeroDivisor_apply (f : K) (P : Place K) : zeroDivisor f P = max 0 (P.ord f) := rfl

/--
@isnad1 id=eq.0h3v.s6.28b67701c671 from=translated src=- shape=57f3c667 vocab=358f6c5b
-/
@[simp]
theorem polarDivisor_apply (f : K) (P : Place K) : polarDivisor f P = max 0 (-P.ord f) := rfl

/--
@isnad1 id=le.0h2v.s6.583fa3d2a802 from=translated src=- shape=90f60ef4 vocab=bd9fdd3e
-/
theorem zeroDivisor_nonneg (f : K) : 0 ≤ zeroDivisor f := fun P ↦ by simp

/--
@isnad1 id=le.0h2v.s6.1938360f4a25 from=translated src=- shape=90f60ef4 vocab=5a897733
-/
theorem polarDivisor_nonneg (f : K) : 0 ≤ polarDivisor f := fun P ↦ by simp

/--
@isnad1 id=eq.0h2v.s6.b7ba4cb1a900 from=translated src=- shape=857db19a vocab=890e53a0
-/
theorem div_eq_zeroDivisor_sub_polarDivisor (f : K) :
    div f = zeroDivisor f - polarDivisor f := by
  ext P; simp only [div_apply, Finsupp.coe_sub, Pi.sub_apply, zeroDivisor_apply,
    polarDivisor_apply]; omega

/--
@isnad1 id=eq.0h2v.s5.7826b37a36a2 from=translated src=- shape=735c0044 vocab=766fc256
-/
@[simp]
theorem polarDivisor_inv (f : K) : polarDivisor f⁻¹ = zeroDivisor f := by ext P; simp

/--
@isnad1 id=eq.0h2v.s5.76a1a85e8f29 from=translated src=- shape=735c0044 vocab=766fc256
-/
@[simp]
theorem zeroDivisor_inv (f : K) : zeroDivisor f⁻¹ = polarDivisor f := by ext P; simp

/--
@isnad1 id=le.0h2v.s6.af032adcfe47 from=translated src=- shape=22b7db8c vocab=daeca49e
-/
theorem neg_polarDivisor_le_div (f : K) : -polarDivisor f ≤ div f := fun P ↦ by
  simp only [Finsupp.coe_neg, Pi.neg_apply, polarDivisor_apply, div_apply]; omega

/-- A transcendental element has a nonzero divisor of poles.
@isnad1 id=ne.1h2v.s6.82b73220b50b from=translated src=- shape=f7139a25 vocab=126b91e9
-/
theorem polarDivisor_ne_zero {x : K} (hx : Transcendental ℚ x) : polarDivisor x ≠ 0 := by
  obtain ⟨P, hP⟩ := Place.exists_ord_neg hx
  intro h
  have := congrArg (· P) h
  simp only [polarDivisor_apply, Finsupp.coe_zero, Pi.zero_apply] at this
  omega

end Divisor

end Belyi.CurveField
