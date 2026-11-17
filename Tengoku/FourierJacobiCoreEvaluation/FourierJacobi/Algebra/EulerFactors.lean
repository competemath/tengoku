import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Euler factors and normalization

Here t denotes the positive real q^(-1/2), subsequently embedded in the field.
The definitions in this file are explicit rational expressions. They are not
definitions of an L-function or of a Fourier--Jacobi period.
-/

namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]

def poincare (t : K) : K := 1 + 2 * t ^ 2 + 2 * t ^ 4 + 2 * t ^ 6 + t ^ 8

/--
@isnad1 id=eq.0h2v.s7.95ccc61369cb from=translated src=- shape=c59260fc vocab=7fa6fb58
-/
theorem poincare_factorization (t : K) :
    poincare t = (1 + t ^ 2) ^ 2 * (1 + t ^ 4) := by
  unfold poincare
  ring

def satakeNumerator (a b : K) : K := (1 + a) ^ 2 * (1 + b) ^ 2 / (a * b)

/--
@isnad1 id=eq.2h3v.s7.7fb1c4a6e781 from=translated src=- shape=2cbad6c6 vocab=abe49cd1
-/
theorem satakeNumerator_eq (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    satakeNumerator a b = (a + 2 + a⁻¹) * (b + 2 + b⁻¹) := by
  unfold satakeNumerator
  field_simp
  ring

def fourFactors (a b x : K) : K :=
  (1 - a * x) * (1 - a⁻¹ * x) * (1 - b * x) * (1 - b⁻¹ * x)

def n₁ (t a b : K) : K := fourFactors a b (t ^ 2)

def n₂ (t a b : K) : K :=
  (1 - a * b * t ^ 2) * (1 - a / b * t ^ 2) *
    (1 - b / a * t ^ 2) * (1 - (a * b)⁻¹ * t ^ 2)

def d₁ (t a b d : K) : K := fourFactors a b (d * t)
def d₂ (t a b d : K) : K := fourFactors a b (t / d)

/-- The rational expression obtained for the core on the regular parameter locus.-/
def closedCore (t a b d : K) : K :=
  satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b /
    (poincare t * d₁ t a b d * d₂ t a b d)

def piAdjointInverse (t a b : K) : K := (1 - t ^ 2) ^ 2 * n₁ t a b * n₂ t a b

def principalAdjointInverse (t d : K) : K :=
  (1 - d * t) * (1 + d * t) * (1 - t ^ 2) * (1 - t / d) * (1 + t / d)

/--
@isnad1 id=eq.0h3v.s8.4db4203f7e49 from=translated src=- shape=261ba0dc vocab=5971c902
-/
theorem principalAdjointInverse_eq (t d : K) :
    principalAdjointInverse t d =
      (1 - d ^ 2 * t ^ 2) * (1 - t ^ 2) * (1 - t ^ 2 / d ^ 2) := by
  unfold principalAdjointInverse
  simp only [div_eq_mul_inv]
  ring

def principalTensorInverse (t a b d : K) : K :=
  (1 - d * t) * (1 - t / d) * d₁ t a b d * d₂ t a b d

def principalNormalizer (t a b d : K) : K :=
  (1 - t ^ 4) * (1 - t ^ 8) * principalTensorInverse t a b d /
    (piAdjointInverse t a b * principalAdjointInverse t d)

/-- Cancellation isolated from the larger Satake products, to keep its proof small.
@isnad1 id=eq.10h8v.s10.be72ffdece5b from=translated src=- shape=dffc827d vocab=1f04bedb
-/
theorem principal_cancellation (t d p n₁ n₂ d₁ d₂ : K)
    (hc : poincare t ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    (p * (1 - t ^ 2) * n₁ * n₂ / (poincare t * d₁ * d₂)) *
      ((1 - t ^ 4) * (1 - t ^ 8) * ((1 - d * t) * (1 - t / d) * d₁ * d₂) /
        ((1 - t ^ 2) ^ 2 * n₁ * n₂ * principalAdjointInverse t d)) =
      p / ((1 + d * t) * (1 + t / d)) := by
  unfold principalAdjointInverse
  generalize d * t = x at *
  generalize t / d = y at *
  field_simp
  simp only [poincare]
  ring

/--
@isnad1 id=eq.10h5v.s9.879a460c05f8 from=translated src=- shape=4b35d2ba vocab=5ba3254f
-/
theorem normalized_closedCore_principal (t a b d : K)
    (hc : poincare t ≠ 0) (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hd₁ : d₁ t a b d ≠ 0) (hd₂ : d₂ t a b d ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    closedCore t a b d * principalNormalizer t a b d =
      satakeNumerator a b / ((1 + d * t) * (1 + t / d)) :=
  principal_cancellation t d (satakeNumerator a b) (n₁ t a b) (n₂ t a b)
    (d₁ t a b d) (d₂ t a b d) hc hn₁ hn₂ hd₁ hd₂ ht hm hp him hip

def specialTensorInverse (t a b e : K) : K :=
  (1 - e * t ^ 2) * fourFactors a b (e * t ^ 2)

def specialNormalizer (t a b e : K) : K :=
  (1 - t ^ 4) * (1 - t ^ 8) * specialTensorInverse t a b e /
    (piAdjointInverse t a b * (1 - t ^ 4))

/--
@isnad1 id=eq.0h4v.s6.5a6a40aa4ed7 from=translated src=- shape=d582e658 vocab=6f359d35
-/
theorem special_negative_d₁ (t a b : K) :
    d₁ t a b (-t) = fourFactors a b (-t ^ 2) := by
  unfold d₁
  congr 1
  ring

/--
@isnad1 id=eq.3h4v.s6.467cb4ddd012 from=translated src=- shape=6cec7949 vocab=db7e4a45
-/
theorem special_negative_d₂ (t a b : K) (ht : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    d₂ t a b (-t) = satakeNumerator a b := by
  unfold d₂ fourFactors satakeNumerator
  field_simp
  ring

/--
@isnad1 id=eq.7h6v.s9.f4136c78c393 from=translated src=- shape=2a14e493 vocab=b04dead8
-/
theorem special_negative_cancellation (t p n₁ n₂ f : K)
    (hc : poincare t ≠ 0) (hp : p ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hf : f ≠ 0) (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    (p * (1 - t ^ 2) * n₁ * n₂ / (poincare t * f * p)) *
      ((1 - t ^ 4) * (1 - t ^ 8) * ((1 + t ^ 2) * f) /
        ((1 - t ^ 2) ^ 2 * n₁ * n₂ * (1 - t ^ 4))) = 1 := by
  field_simp
  simp only [poincare]
  ring

/--
@isnad1 id=eq.10h4v.s8.a815ec58f8d5 from=translated src=- shape=f8435c11 vocab=5214e7b6
-/
theorem normalized_closedCore_special_negative (t a b : K)
    (ht₀ : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : poincare t ≠ 0) (hp : satakeNumerator a b ≠ 0)
    (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hf : fourFactors a b (-t ^ 2) ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    closedCore t a b (-t) * specialNormalizer t a b (-1) = 1 := by
  unfold closedCore specialNormalizer specialTensorInverse piAdjointInverse
  rw [special_negative_d₁, special_negative_d₂ t a b ht₀ ha hb]
  simp only [neg_one_mul, sub_neg_eq_add]
  exact special_negative_cancellation t (satakeNumerator a b) (n₁ t a b)
    (n₂ t a b) (fourFactors a b (-t ^ 2)) hc hp hn₁ hn₂ hf ht ht₄

/-- The positive special sign kills the entire damped expression before any limit.
@isnad1 id=eq.0h3v.s7.a8640a5ac25b from=translated src=- shape=9641087a vocab=9b715242
-/
theorem special_positive_prefactor (q x : K) : (1 - (1 : K)) / (q + 1) * x = 0 := by
  simp

end Algebra
end FourierJacobi
