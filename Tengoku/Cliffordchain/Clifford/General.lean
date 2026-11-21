import Tengoku.Cliffordchain.Clifford.Clean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unfolding the Clifford chain predicate at low levels

Lemmas reading off what `Chain 2`, `Chain 3`, `Chain 4`, `Chain 5` force, used to refute
`CliffordChain 6` (`Clifford.Counter6`). `cD` is the real concyclicity determinant: it vanishes
for four points on one generalized circle (`cD_eq_zero`).
-/

namespace Clifford

open Complex ComplexConjugate

/-- The real concyclicity determinant of four points: it vanishes when the four points lie on
one circle or one line.-/
def cD (a b c q : ℂ) : ℝ :=
  det4 (a.re ^ 2 + a.im ^ 2) a.re a.im 1 (b.re ^ 2 + b.im ^ 2) b.re b.im 1
    (c.re ^ 2 + c.im ^ 2) c.re c.im 1 (q.re ^ 2 + q.im ^ 2) q.re q.im 1

/--
@isnad1 id=eq.1h3v.s6.1916d0891bcc from=translated src=- shape=ba397cec vocab=eef2e834
-/
theorem mem_sphere_eq {o z : ℂ} {r : ℝ} (h : z ∈ Metric.sphere o r) :
    (z.re - o.re) ^ 2 + (z.im - o.im) ^ 2 = r ^ 2 := by
  rw [Metric.mem_sphere, Complex.dist_eq] at h
  rw [← h, Complex.sq_norm, Complex.normSq_apply]; simp; ring

/--
@isnad1 id=eq.0h11v.s7.ca14faaefeff from=translated src=- shape=002c7b01 vocab=ac4465c6
-/
theorem det4_col1 (k₁ k₂ k₃ x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) :
    det4 (k₁ * x₁ + k₂ * y₁ + k₃) x₁ y₁ 1 (k₁ * x₂ + k₂ * y₂ + k₃) x₂ y₂ 1
      (k₁ * x₃ + k₂ * y₃ + k₃) x₃ y₃ 1 (k₁ * x₄ + k₂ * y₄ + k₃) x₄ y₄ 1 = 0 := by
  unfold det4 det3; ring

/-- Four points on a generalized circle satisfy `cD = 0`.
@isnad1 id=eq.5h5v.s5.dac733c762bb from=translated src=- shape=7837d05e vocab=606dd8d6
-/
theorem cD_eq_zero {Y : Set ℂ} (hY : IsGCircle Y) {a b c q : ℂ} (ha : a ∈ Y) (hb : b ∈ Y)
    (hc : c ∈ Y) (hq : q ∈ Y) : cD a b c q = 0 := by
  rcases hY with ⟨o, r, rfl⟩ | ⟨p, v, -, rfl⟩
  · have e : ∀ z ∈ Metric.sphere o r, z.re ^ 2 + z.im ^ 2 =
        2 * o.re * z.re + 2 * o.im * z.im + (r ^ 2 - o.re ^ 2 - o.im ^ 2) := fun z hz => by
      linear_combination mem_sphere_eq hz
    rw [cD, e a ha, e b hb, e c hc, e q hq]
    exact det4_col1 _ _ _ _ _ _ _ _ _ _ _
  · obtain ⟨ta, rfl⟩ := ha; obtain ⟨tb, rfl⟩ := hb; obtain ⟨tc, rfl⟩ := hc
    obtain ⟨tq, rfl⟩ := hq
    simp only [cD, det4, det3, Complex.add_re, Complex.add_im, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

/--
@isnad1 id=eq.1h2v.s6.81639f2565bc from=translated src=- shape=8a563369 vocab=cd81edc3
-/
theorem chain2_eq {c : Fin 2 → ℂ} {p : ℂ} (h : Chain 2 c {p}) : p = second (c 0) (c 1) :=
  Set.singleton_eq_singleton_iff.1 h

/--
@isnad1 id=and.1h4v.s6.8af8b01db9e3 from=translated src=- shape=61041215 vocab=46a75520
-/
theorem chain3_mem {x y z : ℂ} {Y : Set ℂ} (h : Chain 3 ![x, y, z] Y) :
    IsGCircle Y ∧ second y z ∈ Y ∧ second x z ∈ Y ∧ second x y ∈ Y := by
  obtain ⟨hY, h⟩ := (h : IsGCircle Y ∧
    ∀ i : Fin 3, ∃ p, Chain 2 (![x, y, z] ∘ i.succAbove) {p} ∧ p ∈ Y)
  obtain ⟨p0, e0, m0⟩ := h 0
  obtain ⟨p1, e1, m1⟩ := h 1
  obtain ⟨p2, e2, m2⟩ := h 2
  rw [chain2_eq e0] at m0; rw [chain2_eq e1] at m1; rw [chain2_eq e2] at m2
  exact ⟨hY, m0, m1, m2⟩

/-- A level-4 point lies, with the three second intersections of each triple, on a generalized
circle.
@isnad1 id=and.1h5v.s7.190d91b00250 from=translated src=- shape=35b8cb60 vocab=59e8986d
-/
theorem chain4_cD {x y z w q : ℂ} (h : Chain 4 ![x, y, z, w] {q}) :
    cD (second z w) (second y w) (second y z) q = 0 ∧
    cD (second z w) (second x w) (second x z) q = 0 ∧
    cD (second y w) (second x w) (second x y) q = 0 ∧
    cD (second y z) (second x z) (second x y) q = 0 := by
  obtain ⟨p, hp, h⟩ := (h : ∃ p, ({q} : Set ℂ) = {p} ∧
    ∀ i : Fin 4, ∃ Y, Chain 3 (![x, y, z, w] ∘ i.succAbove) Y ∧ p ∈ Y)
  rw [← Set.singleton_eq_singleton_iff.1 hp] at h
  have e0 : ![x, y, z, w] ∘ Fin.succAbove 0 = ![y, z, w] := by funext k; fin_cases k <;> rfl
  have e1 : ![x, y, z, w] ∘ Fin.succAbove 1 = ![x, z, w] := by funext k; fin_cases k <;> rfl
  have e2 : ![x, y, z, w] ∘ Fin.succAbove 2 = ![x, y, w] := by funext k; fin_cases k <;> rfl
  have e3 : ![x, y, z, w] ∘ Fin.succAbove 3 = ![x, y, z] := by funext k; fin_cases k <;> rfl
  obtain ⟨Y0, h0, q0⟩ := h 0; obtain ⟨Y1, h1, q1⟩ := h 1
  obtain ⟨Y2, h2, q2⟩ := h 2; obtain ⟨Y3, h3, q3⟩ := h 3
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  obtain ⟨g0, a0, b0, c0⟩ := chain3_mem h0; obtain ⟨g1, a1, b1, c1⟩ := chain3_mem h1
  obtain ⟨g2, a2, b2, c2⟩ := chain3_mem h2; obtain ⟨g3, a3, b3, c3⟩ := chain3_mem h3
  exact ⟨cD_eq_zero g0 a0 b0 c0 q0, cD_eq_zero g1 a1 b1 c1 q1, cD_eq_zero g2 a2 b2 c2 q2,
    cD_eq_zero g3 a3 b3 c3 q3⟩

/--
@isnad1 id=eq.2h3v.s7.9d7c8959d05f from=translated src=- shape=8bd60871 vocab=d584fc79
-/
theorem second_eq {c d z : ℂ} (h : c ≠ d)
    (hz : conj c * d - c * conj d = z * (conj c - conj d)) : second c d = z := by
  rw [second, div_eq_iff (conj_sub_ne_zero h)]; exact hz

/-- Unfolding `Chain 5`: a generalized circle through level-4 points of the subfamilies omitting the
first, second and third circle.
@isnad1 id=and.1h6v.s7.aa7ef54c7736 from=translated src=- shape=ff7c12db vocab=6e2b66bf
-/
theorem chain5_mem {a b c d e : ℂ} {Y : Set ℂ} (h : Chain 5 ![a, b, c, d, e] Y) :
    IsGCircle Y ∧ (∃ q, Chain 4 ![b, c, d, e] {q} ∧ q ∈ Y) ∧
      (∃ q, Chain 4 ![a, c, d, e] {q} ∧ q ∈ Y) ∧ (∃ q, Chain 4 ![a, b, d, e] {q} ∧ q ∈ Y) := by
  obtain ⟨hY, h⟩ := (h : IsGCircle Y ∧
    ∀ i : Fin 5, ∃ q, Chain 4 (![a, b, c, d, e] ∘ i.succAbove) {q} ∧ q ∈ Y)
  have e0 : ![a, b, c, d, e] ∘ Fin.succAbove 0 = ![b, c, d, e] := by funext k; fin_cases k <;> rfl
  have e1 : ![a, b, c, d, e] ∘ Fin.succAbove 1 = ![a, c, d, e] := by funext k; fin_cases k <;> rfl
  have e2 : ![a, b, c, d, e] ∘ Fin.succAbove 2 = ![a, b, d, e] := by funext k; fin_cases k <;> rfl
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2
  exact ⟨hY, h0, h1, h2⟩

end Clifford
