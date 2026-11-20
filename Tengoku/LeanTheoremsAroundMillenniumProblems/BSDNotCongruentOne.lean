/-
1 is not a congruent number (Fermat), through `x ^ 4 - y ^ 4 ≠ z ^ 2`.

`congruentNumber` is copied verbatim from google-deepmind/formal-conjectures,
FormalConjectures/Wikipedia/CongruentNumber.lean (Copyright 2025 The Formal Conjectures Authors,
Apache License 2.0), where `not_congruentNumber_1` is stated with `sorry`.

Mathlib has `not_fermat_42` (`a ^ 4 + b ^ 4 ≠ c ^ 2`). The variant with a minus sign is proved
here the same way, by infinite descent on `|x|`, following the structure of
`Mathlib/NumberTheory/FLT/Four.lean`:

* a minimal solution has `x` and `y` coprime, and then `y` and `z` coprime;
* if `y` is odd, `(y², z, x²)` is a primitive Pythagorean triple: `y² = m² - n²`, `z = 2mn`,
  `x² = m² + n²`, so `m⁴ - n⁴ = (xy)²` with `|m| < |x|`;
* if `y` is even, `(z, y², x²)` is one: `y² = 2mn` with `m`, `n` coprime of opposite parity, which
  makes the odd one a square `q²` and half the even one a square; a second triple
  `(odd, even, x)` then gives `q² = u⁴ - v⁴` with `|u| < |x|`.

Then a rational right triangle of area 1, with denominators cleared, gives `C⁴ - (2D)⁴ = (A² - B²)²`.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms NotCongruentOne.not_fermat_4_minus` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms NotCongruentOne.not_congruentNumber_1` (it only prints; the queue checks the axioms of every declaration). -/

namespace NotCongruentOne

/-- A solution of `x ^ 4 - y ^ 4 = z ^ 2` with `y` and `z` nonzero.-/
def Sol (x y z : ℤ) : Prop := y ≠ 0 ∧ z ≠ 0 ∧ x ^ 4 - y ^ 4 = z ^ 2

/--
@isnad1 id=ne.1h3v.s4.695d69a1e6c5 from=translated src=- shape=11958059 vocab=71c0ff36
-/
theorem Sol.x_ne_zero {x y z : ℤ} (h : Sol x y z) : x ≠ 0 := by
  rintro rfl
  have h1 : 0 < y ^ 4 := Even.pow_pos (by decide) h.1
  have h2 : 0 ≤ z ^ 2 := sq_nonneg z
  have := h.2.2
  nlinarith

/-- A solution with the smallest `|x|`.-/
def Minimal (x y z : ℤ) : Prop := Sol x y z ∧ ∀ x1 y1 z1 : ℤ, Sol x1 y1 z1 → x.natAbs ≤ x1.natAbs

/--
@isnad1 id=ex.1h3v.s4.f0ae69ea8f2b from=translated src=- shape=13c20c3d vocab=5dc249b7
-/
theorem exists_minimal {x y z : ℤ} (h : Sol x y z) : ∃ x0 y0 z0, Minimal x0 y0 z0 := by
  classical
  let S : Set ℕ := { n | ∃ s : ℤ × ℤ × ℤ, Sol s.1 s.2.1 s.2.2 ∧ n = s.1.natAbs }
  have hS : S.Nonempty := ⟨x.natAbs, ⟨x, y, z⟩, h, rfl⟩
  obtain ⟨s0, hs0, hs1⟩ := Nat.find_spec hS
  refine ⟨s0.1, s0.2.1, s0.2.2, hs0, fun x1 y1 z1 h1 => ?_⟩
  rw [← hs1]
  exact Nat.find_min' hS ⟨⟨x1, y1, z1⟩, h1, rfl⟩

/-- In a minimal solution, `x` and `y` are coprime.
@isnad1 id=eq.1h3v.s4.2cf376add2d8 from=translated src=- shape=f3b1284f vocab=b9dce42f
-/
theorem coprime_xy {x y z : ℤ} (h : Minimal x y z) : Int.gcd x y = 1 := by
  by_contra hxy
  obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hxy
  obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
  obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
  have hpz : (p : ℤ) ^ 2 ∣ z := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2]
    exact ⟨x1 ^ 4 - y1 ^ 4, by ring⟩
  obtain ⟨z1, rfl⟩ := hpz
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hs : Sol x1 y1 z1 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl; exact h.1.1 (by simp)
    · rintro rfl; exact h.1.2.1 (by simp)
    · have := h.1.2.2
      have hp4 : ((p : ℤ) ^ 4) ≠ 0 := pow_ne_zero 4 hp0
      apply mul_left_cancel₀ hp4
      linear_combination this
  have hx1 : x1 ≠ 0 := hs.x_ne_zero
  apply Nat.le_lt_asymm (h.2 _ _ _ hs)
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have := hp.one_lt
  have : 0 < x1.natAbs := Int.natAbs_pos.mpr hx1
  nlinarith

/-- In a minimal solution, `y` and `z` are coprime.
@isnad1 id=eq.1h3v.s4.050bf3476f70 from=translated src=- shape=addb8cf1 vocab=b9dce42f
-/
theorem coprime_yz {x y z : ℤ} (h : Minimal x y z) : Int.gcd y z = 1 := by
  by_contra hyz
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp hyz
  have hpy' : (p : ℤ) ∣ y := Int.natCast_dvd.mpr hpy
  have hpz' : (p : ℤ) ∣ z := Int.natCast_dvd.mpr hpz
  have hpx4 : (p : ℤ) ∣ x ^ 4 := by
    have : x ^ 4 = y ^ 4 + z ^ 2 := by linear_combination h.1.2.2
    rw [this]
    exact dvd_add (dvd_pow hpy' (by norm_num)) (dvd_pow hpz' (by norm_num))
  have hpx : (p : ℤ) ∣ x := Int.Prime.dvd_pow' hp hpx4
  have h1 : (p : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hpx hpy'
  rw [coprime_xy h] at h1
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hp.one_lt.ne' (by exact_mod_cast this)

/-- The descent in the case `y` even: from `x² = o² + e²` and `y² = 2·o·e` (o odd, e even,
coprime, all positive) a solution with smaller `|x|`.
@isnad1 id=ex.8h4v.s7.fac69430b30a from=translated src=- shape=07820816 vocab=8249499d
-/
theorem descenso_par {o e x y : ℤ} (ho : 0 < o) (he : 0 < e) (hx : 0 < x) (ho2 : o % 2 = 1)
    (he2 : e % 2 = 0) (hoe : Int.gcd o e = 1) (hxoe : x ^ 2 = o ^ 2 + e ^ 2)
    (hy : y ^ 2 = 2 * o * e) :
    ∃ u v q, Sol u v q ∧ u.natAbs < x.natAbs := by
  obtain ⟨e', rfl⟩ : 2 ∣ e := Int.dvd_of_emod_eq_zero he2
  have he' : 0 < e' := by linarith
  have hy2 : (2 : ℤ) ∣ y := by
    have h2 : ((2 : ℕ) : ℤ) ∣ y := Int.Prime.dvd_pow' (k := 2) Nat.prime_two
      (by rw [hy]; exact ⟨o * (2 * e'), by push_cast; ring⟩)
    exact_mod_cast h2
  obtain ⟨y', rfl⟩ := hy2
  have hy' : o * e' = y' ^ 2 :=
    mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) (by linear_combination -hy)
  have hoe' : Int.gcd o e' = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hoe).of_mul_right_right
  -- o and e' are squares
  obtain ⟨q, hq⟩ := Int.sq_of_gcd_eq_one hoe' hy'
  have hq' : o = q ^ 2 := hq.resolve_right (by intro h; nlinarith [sq_nonneg q])
  -- (o, 2e', x) is a primitive Pythagorean triple with o odd
  have ht : PythagoreanTriple o (2 * e') x := by
    delta PythagoreanTriple
    linear_combination -hxoe
  obtain ⟨r, s, h1, h2, h3, h4, -, h6⟩ := ht.coprime_classification' hoe ho2 hx
  have hrs : e' = r * s := mul_left_cancel₀ (two_ne_zero) (by linear_combination h2)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hrs; linarith
  have hr : 0 < r := lt_of_le_of_ne h6 (Ne.symm hr0)
  have hs : 0 < s := by
    rcases le_or_gt s 0 with hs | hs
    · have : r * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le hs
      linarith
    · exact hs
  -- r and s are squares, since r * s = e' is
  obtain ⟨p, hp⟩ : ∃ p, e' = p ^ 2 := by
    obtain ⟨p, hp⟩ := Int.sq_of_gcd_eq_one (by rw [Int.gcd_comm]; exact hoe')
      (by rw [mul_comm]; exact hy')
    exact ⟨p, hp.resolve_right (by intro h; nlinarith [sq_nonneg p])⟩
  have hrsp : r * s = p ^ 2 := by rw [← hrs, hp]
  obtain ⟨u, hu⟩ := Int.sq_of_gcd_eq_one h4 hrsp
  have hu' : r = u ^ 2 := hu.resolve_right (by intro h; nlinarith [sq_nonneg u])
  have h4' : Int.gcd s r = 1 := by rw [Int.gcd_comm]; exact h4
  obtain ⟨v, hv⟩ := Int.sq_of_gcd_eq_one h4' (by rw [mul_comm]; exact hrsp)
  have hv' : s = v ^ 2 := hv.resolve_right (by intro h; nlinarith [sq_nonneg v])
  refine ⟨u, v, q, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro rfl; simp at hv'; linarith
  · rintro rfl; simp at hq'; linarith
  · rw [← hq', h1, hu', hv']; ring
  · rw [Int.natAbs_lt_iff_sq_lt]
    have hr1 : 1 ≤ r := by omega
    have hx1 : 1 ≤ x := by omega
    have hs2 : 0 < s ^ 2 := by positivity
    have hrr : r ≤ r ^ 2 := by
      rw [sq]; simpa using mul_le_mul_of_nonneg_left hr1 hr.le
    have hxx : x ≤ x ^ 2 := by
      rw [sq]; simpa using mul_le_mul_of_nonneg_left hx1 hx.le
    calc u ^ 2 = r := hu'.symm
      _ ≤ r ^ 2 := hrr
      _ < r ^ 2 + s ^ 2 := by linarith
      _ = x := h3.symm
      _ ≤ x ^ 2 := hxx

/--
@isnad1 id=false.1h3v.s3.ecff645bd241 from=translated src=- shape=2324b133 vocab=f9262c3f
-/
theorem not_minimal {x y z : ℤ} (h : Minimal x y z) : False := by
  -- work with |x|, |y|, |z|: the same equation and the same measure
  set X : ℤ := (x.natAbs : ℤ) with hX
  set Y : ℤ := (y.natAbs : ℤ) with hY
  set Z : ℤ := (z.natAbs : ℤ) with hZ
  have hX2 : X ^ 2 = x ^ 2 := Int.natAbs_sq x
  have hY2 : Y ^ 2 = y ^ 2 := Int.natAbs_sq y
  have hZ2 : Z ^ 2 = z ^ 2 := Int.natAbs_sq z
  have hx0 : x ≠ 0 := h.1.x_ne_zero
  have hXp : 0 < X := Int.natCast_pos.mpr (Int.natAbs_pos.mpr hx0)
  have hYp : 0 < Y := Int.natCast_pos.mpr (Int.natAbs_pos.mpr h.1.1)
  have hZp : 0 < Z := Int.natCast_pos.mpr (Int.natAbs_pos.mpr h.1.2.1)
  have heq : X ^ 4 - Y ^ 4 = Z ^ 2 := by
    have := h.1.2.2
    calc X ^ 4 - Y ^ 4 = (X ^ 2) ^ 2 - (Y ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 - (y ^ 2) ^ 2 := by rw [hX2, hY2]
      _ = z ^ 2 := by linear_combination this
      _ = Z ^ 2 := hZ2.symm
  have hcxy : Int.gcd X Y = 1 := by
    have := coprime_xy h
    simpa [X, Y, Int.gcd, Int.natAbs_abs] using this
  have hcyz : Int.gcd Y Z = 1 := by
    have := coprime_yz h
    simpa [Y, Z, Int.gcd, Int.natAbs_abs] using this
  have hXabs : X.natAbs = x.natAbs := by simp [X, Int.natAbs_abs]
  -- any smaller solution contradicts minimality
  have menor : ∀ u v q, Sol u v q → u.natAbs < X.natAbs → False := by
    intro u v q hs hlt
    have := h.2 u v q hs
    omega
  rcases Int.emod_two_eq_zero_or_one Y with hYe | hYo
  · -- y even: then z is odd
    have hZo : Z % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one Z with hZe | hZo
      · exfalso
        have h2 : (2 : ℤ) ∣ (Int.gcd Y Z : ℤ) :=
          Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hYe) (Int.dvd_of_emod_eq_zero hZe)
        rw [hcyz] at h2
        revert h2; decide
      · exact hZo
    have ht : PythagoreanTriple Z (Y ^ 2) (X ^ 2) := by
      delta PythagoreanTriple
      linear_combination -heq
    have hg : Int.gcd Z (Y ^ 2) = 1 := by
      rw [Int.gcd_comm]
      exact Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_iff_gcd_eq_one.mpr hcyz).pow_left
    obtain ⟨m, n, h1, h2, h3, h4, h5, h6⟩ := ht.coprime_classification' hg hZo (by positivity)
    have hm : 0 < m := by
      rcases h6.lt_or_eq with h6 | h6
      · exact h6
      · subst h6; have : 0 < Y ^ 2 := by positivity
        simp at h2; linarith
    have hn : 0 < n := by
      have : 0 < Y ^ 2 := by positivity
      rcases le_or_gt n 0 with hn | hn
      · have : 2 * m * n ≤ 0 := by nlinarith
        linarith
      · exact hn
    rcases h5 with ⟨hme, hno⟩ | ⟨hmo, hne⟩
    · obtain ⟨u, v, q, hs, hlt⟩ := descenso_par hn hm hXp hno hme
        (by rw [Int.gcd_comm]; exact h4) (show X ^ 2 = n ^ 2 + m ^ 2 by rw [h3]; ring)
        (show Y ^ 2 = 2 * n * m by rw [h2]; ring)
      exact menor u v q hs hlt
    · obtain ⟨u, v, q, hs, hlt⟩ := descenso_par hm hn hXp hmo hne h4 h3 h2
      exact menor u v q hs hlt
  · -- y odd
    have ht : PythagoreanTriple (Y ^ 2) Z (X ^ 2) := by
      delta PythagoreanTriple
      linear_combination -heq
    have hg : Int.gcd (Y ^ 2) Z = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_iff_gcd_eq_one.mpr hcyz).pow_left
    have hY22 : Y ^ 2 % 2 = 1 := by rw [sq, Int.mul_emod, hYo]; decide
    obtain ⟨m, n, h1, h2, h3, h4, -, -⟩ := ht.coprime_classification' hg hY22 (by positivity)
    have hn0 : n ≠ 0 := by rintro rfl; simp at h2; linarith
    refine menor m n (X * Y) ⟨hn0, by positivity, ?_⟩ ?_
    · have : X ^ 2 * Y ^ 2 = (m ^ 2 + n ^ 2) * (m ^ 2 - n ^ 2) := by rw [h3, h1]
      linear_combination -this
    · rw [Int.natAbs_lt_iff_sq_lt, h3]
      have : 0 < n ^ 2 := by positivity
      linarith

/-- **`x ^ 4 - y ^ 4 = z ^ 2` has no solution with `y` and `z` nonzero.**
@isnad1 id=ne.2h3v.s6.8ab5131c10f8 from=translated src=- shape=d78b1b48 vocab=57452192
-/
theorem not_fermat_4_minus {x y z : ℤ} (hy : y ≠ 0) (hz : z ≠ 0) : x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro h
  obtain ⟨x0, y0, z0, hm⟩ := exists_minimal ⟨hy, hz, h⟩
  exact not_minimal hm

/-- `congruentNumber`, copied verbatim from google-deepmind/formal-conjectures
(FormalConjectures/Wikipedia/CongruentNumber.lean, Apache License 2.0).-/
def congruentNumber (n : ℕ) : Prop :=
  ∃ (a b c : ℚ), a ^ 2 + b ^ 2 = c ^ 2 ∧ n = (2⁻¹ : ℚ) * a * b

/-- **1 is not a congruent number** (Fermat).
@isnad1 id=not.0h0v.s2.f759b7f3aff1 from=translated src=- shape=8d7dbbf6 vocab=95ebbc01
-/
theorem not_congruentNumber_1 : ¬ congruentNumber 1 := by
  rintro ⟨a, b, c, hp, ha⟩
  have hab : a * b = 2 := by push_cast at ha; linarith
  by_cases hsq : a ^ 2 = b ^ 2
  · -- then a = b and a ^ 2 = 2: impossible, √2 is irrational
    have ha2 : a ^ 2 = 2 := by
      have h0 : (a ^ 2 - 2) * (a ^ 2 + 2) = 0 := by
        linear_combination a ^ 2 * hsq + (a * b + 2) * hab
      have hpos : a ^ 2 + 2 ≠ 0 := by positivity
      have := (mul_eq_zero.mp h0).resolve_right hpos
      linarith
    apply irrational_sqrt_two
    refine ⟨|a|, ?_⟩
    rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs]
    congr 1
    exact_mod_cast ha2
  · -- clear denominators: A = a·D, B = b·D, C = c·D with D = den a · den b · den c
    set D : ℤ := (a.den : ℤ) * b.den * c.den with hD
    have hD0 : (D : ℚ) ≠ 0 := by
      simp only [hD]; push_cast; positivity
    set A : ℤ := a.num * b.den * c.den
    set B : ℤ := b.num * a.den * c.den
    set C : ℤ := c.num * a.den * b.den
    have hA : (A : ℚ) = a * D := by
      simp only [A, hD]; push_cast; rw [← Rat.mul_den_eq_num a]; ring
    have hB : (B : ℚ) = b * D := by
      simp only [B, hD]; push_cast; rw [← Rat.mul_den_eq_num b]; ring
    have hC : (C : ℚ) = c * D := by
      simp only [C, hD]; push_cast; rw [← Rat.mul_den_eq_num c]; ring
    have hpZ : A ^ 2 + B ^ 2 = C ^ 2 := by
      have : (A : ℚ) ^ 2 + (B : ℚ) ^ 2 = (C : ℚ) ^ 2 := by
        rw [hA, hB, hC]; linear_combination (D : ℚ) ^ 2 * hp
      exact_mod_cast this
    have habZ : A * B = 2 * D ^ 2 := by
      have : (A : ℚ) * B = 2 * (D : ℚ) ^ 2 := by
        rw [hA, hB]; linear_combination (D : ℚ) ^ 2 * hab
      exact_mod_cast this
    have hne : A ^ 2 - B ^ 2 ≠ 0 := by
      intro h0
      apply hsq
      have : (A : ℚ) ^ 2 = (B : ℚ) ^ 2 := by exact_mod_cast (sub_eq_zero.mp h0)
      rw [hA, hB] at this
      have hD2 : (D : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hD0
      apply mul_right_cancel₀ hD2
      linear_combination this
    have hD0' : D ≠ 0 := by exact_mod_cast hD0
    apply not_fermat_4_minus (x := C) (y := 2 * D) (z := A ^ 2 - B ^ 2)
      (mul_ne_zero two_ne_zero hD0') hne
    linear_combination (C ^ 2 + A ^ 2 + B ^ 2) * hpZ.symm + 4 * (A * B + 2 * D ^ 2) * habZ

end NotCongruentOne

