import Tengoku.Cliffordchain.Clifford.Basic
import Tengoku.Cliffordchain.Clifford.Clean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bridges from the algebraic definitions to Mathlib geometry

`Transversal`, the non-vanishing of `triP` / `cycP`, `OnCircleM` and `GenTriple` are stated in
`Clifford.Basic` as polynomial conditions in the centres and their conjugates. Here they are
identified with `Collinear ℝ` and `Metric.sphere`.

The key identity (`cross_second`) is
`cross (P₁₂, P₁₃, P₂₃) · ∏ |cᵢ - cⱼ|² = triP² · cycP`, so non-collinearity of the second
intersections is equivalent to `cycP ≠ 0` only when the centres themselves are not collinear
(for collinear centres the three second intersections coincide).
-/

namespace Clifford

open Complex ComplexConjugate

/-- Three points of `ℂ` are collinear iff `conj (y - x) * (z - x)` is real.
@isnad1 id=iff.0h3v.s7.09a86d7684e0 from=translated src=- shape=5b942be5 vocab=3368c255
-/
theorem collinear_iff_conj_mul (x y z : ℂ) :
    Collinear ℝ ({x, y, z} : Set ℂ) ↔ conj (y - x) * (z - x) = (y - x) * conj (z - x) := by
  constructor
  · intro h
    rw [collinear_iff_of_mem (p₀ := x) (by simp)] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨r, hr⟩ := hv y (by simp)
    obtain ⟨s, hs⟩ := hv z (by simp)
    rw [vadd_eq_add, Complex.real_smul] at hr hs
    rw [hr, hs]
    simp only [add_sub_cancel_right, map_mul, Complex.conj_ofReal]
    ring
  · intro h
    by_cases hxy : y = x
    · subst hxy
      rw [Set.insert_eq_of_mem (Set.mem_insert _ _)]
      exact collinear_pair ℝ _ _
    have hd : y - x ≠ 0 := sub_ne_zero.2 hxy
    have hcd : conj (y - x) ≠ 0 := (map_ne_zero _).2 hd
    set w := (z - x) / (y - x) with hw
    have hwr : conj w = w := by
      rw [hw, map_div₀, div_eq_div_iff hcd hd]
      linear_combination -h
    obtain ⟨t, ht⟩ : ∃ t : ℝ, (t : ℂ) = w := Complex.conj_eq_iff_real.1 hwr |>.imp fun _ h => h.symm
    rw [collinear_iff_of_mem (p₀ := x) (by simp)]
    refine ⟨y - x, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨t, ?_⟩
      rw [vadd_eq_add, Complex.real_smul, ht, hw]
      field_simp
      ring

/--
@isnad1 id=iff.0h2v.s6.8238205e9643 from=translated src=- shape=b372a70c vocab=a66af892
-/
theorem transversal_iff (c d : ℂ) : Transversal c d ↔ ¬ Collinear ℝ ({0, c, d} : Set ℂ) := by
  rw [collinear_iff_conj_mul, Transversal]
  simp only [sub_zero]

/--
@isnad1 id=iff.0h3v.s7.d782d903ba17 from=translated src=- shape=37c0e113 vocab=34f16a98
-/
theorem triP_ne_zero_iff (a b c : ℂ) :
    triP a b c (conj a) (conj b) (conj c) ≠ 0 ↔ ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
  have e : triP a b c (conj a) (conj b) (conj c) =
      (b - a) * conj (c - a) - conj (b - a) * (c - a) := by
    simp only [triP, det3, map_sub]; ring
  rw [collinear_iff_conj_mul, e, Ne, sub_eq_zero, eq_comm]

/-- The key identity: cross product of the second intersections, times `∏ |cᵢ - cⱼ|²`.
@isnad1 id=eq.3h3v.s9.7d14260eda8e from=translated src=- shape=0f30cbe1 vocab=f74eecef
-/
theorem cross_second {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (conj (second a c - second a b) * (second b c - second a b) -
        (second a c - second a b) * conj (second b c - second a b)) *
      ((conj a - conj b) * (conj a - conj c) * (conj b - conj c) * ((a - b) * (a - c) * (b - c))) =
      triP a b c (conj a) (conj b) (conj c) ^ 2 * cycP a b c (conj a) (conj b) (conj c) := by
  have h1 := conj_sub_ne_zero hab; have h2 := conj_sub_ne_zero hac
  have h3 := conj_sub_ne_zero hbc
  have h4 := sub_ne_zero.2 hab; have h5 := sub_ne_zero.2 hac; have h6 := sub_ne_zero.2 hbc
  simp only [map_sub, conj_second]
  simp only [second, triP, cycP, det3]
  field_simp
  ring

/--
@isnad1 id=iff.4h3v.s8.5da50d69b97d from=translated src=- shape=ac18ea5e vocab=df14fcba
-/
theorem cycP_ne_zero_iff {a b c : ℂ} (hab : Transversal a b) (hac : Transversal a c)
    (hbc : Transversal b c) (htri : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    cycP a b c (conj a) (conj b) (conj c) ≠ 0 ↔
      ¬ Collinear ℝ ({second a b, second a c, second b c} : Set ℂ) := by
  have ht := (triP_ne_zero_iff a b c).2 htri
  have e := cross_second hab.ne hac.ne hbc.ne
  have hp : (conj a - conj b) * (conj a - conj c) * (conj b - conj c) * ((a - b) * (a - c) * (b - c))
      ≠ 0 := by
    have := conj_sub_ne_zero hab.ne; have := conj_sub_ne_zero hac.ne
    have := conj_sub_ne_zero hbc.ne
    have := sub_ne_zero.2 hab.ne; have := sub_ne_zero.2 hac.ne; have := sub_ne_zero.2 hbc.ne
    positivity
  rw [collinear_iff_conj_mul, not_iff_not, ← sub_eq_zero (a := conj _ * _)]
  constructor
  · intro h0
    rw [h0, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_right hp
  · intro h0
    rw [h0, zero_mul, eq_comm] at e
    exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero 2 ht)

/--
@isnad1 id=iff.0h2v.s4.844d3a6c8694 from=translated src=- shape=c77f3f00 vocab=a024b19b
-/
theorem onCircleM_iff_mem_sphere (c z : ℂ) : OnCircleM c z ↔ z ∈ Metric.sphere c ‖c‖ := by
  rw [Metric.mem_sphere, Complex.dist_eq, OnCircleM,
    ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> linear_combination h

/--
@isnad1 id=iff.3h3v.s7.3cd099d54e44 from=translated src=- shape=d49d4400 vocab=b6e5a76e
-/
theorem genTriple_iff {a b c : ℂ} (hab : Transversal a b) (hac : Transversal a c)
    (hbc : Transversal b c) :
    GenTriple a b c ↔ (¬ Collinear ℝ ({a, b, c} : Set ℂ) ∧
      ¬ Collinear ℝ ({second a b, second a c, second b c} : Set ℂ)) := by
  rw [GenTriple, triP_ne_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (cycP_ne_zero_iff hab hac hbc h1).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (cycP_ne_zero_iff hab hac hbc h1).2 h2⟩

end Clifford
