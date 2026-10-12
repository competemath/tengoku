/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2002, Problem 4

Find all functions f : ℝ → ℝ such that for all x, y ∈ ℝ:
f(x² - y²) = x f(x) - y f(y).
-/

namespace Usa2002P4

def FE (f : ℝ → ℝ) : Prop :=
  ∀ x y, f (x^2 - y^2) = x * (f x) - y * (f y)

-- Following https://web.evanchen.cc/exams/USAMO-2002-notes.pdf

-- f(0)=0
/--
@isnad1 id=eq.1h1v.s4.162ffa84a1a6 from=translated src=- shape=18892e30 vocab=cd9c36ed
-/
lemma f_zero {f : ℝ → ℝ} (hf : FE f) : f 0 = 0 := by
  simpa using hf 0 0

-- f(x^2) = xf(x)
/--
@isnad1 id=eq.1h2v.s5.dcb8d80886f1 from=translated src=- shape=d7c7f0f8 vocab=b6430aed
-/
lemma squarish {f : ℝ → ℝ} (hf : FE f) (x : ℝ) : f (x^2) = x * f x := by
  simpa [f_zero hf] using hf x 0

-- f(x^2) = f(x^2)-f(y^2)
/--
@isnad1 id=eq.1h3v.s6.e291a8aec3b4 from=translated src=- shape=296bc1a6 vocab=204b0a76
-/
lemma square_additive {f : ℝ → ℝ} (hf : FE f) (x : ℝ) (y : ℝ)  :
    f (x^2 - y^2) = f (x^2) - f (y^2) := by
  simp [squarish hf]
  apply hf

-- f is odd
/--
@isnad1 id=eq.1h2v.s4.5e897518683c from=translated src=- shape=a9b82267 vocab=91fb9d01
-/
lemma f_odd {f : ℝ → ℝ} (hf : FE f) (x : ℝ)  :
    -f x = f (-x) := by
  by_cases hx : x ≥ 0
  · have h := square_additive hf 0 (Real.sqrt x)
    simp_all [f_zero hf]
  · replace hx : - x ≥ 0 := by grind only
    have h := square_additive hf 0 (Real.sqrt (- x))
    simp_all [f_zero hf]

-- f(x+y) = f(x)+f(y) with x,y ≥ 0 first
/--
@isnad1 id=eq.3h3v.s5.bc9d0201c1ec from=translated src=- shape=72fc4237 vocab=cdf27318
-/
lemma additive_pos {f : ℝ → ℝ} (hf : FE f) {x : ℝ} {y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y):
    f (x + y) = f x + f y := by
  have h := square_additive hf (Real.sqrt (x + y)) (Real.sqrt y)
  grind only [usr Real.sq_sqrt', = max_def]

-- Now show Cauchy FE holds with x,y not necessarily positive (lots of cases)
/--
@isnad1 id=eq.1h3v.s5.9ab191f3d8f6 from=translated src=- shape=3c6d9fce vocab=4a8cd360
-/
lemma additive {f : ℝ → ℝ} (hf : FE f) (x : ℝ) (y : ℝ)  :
    f (x + y) = f x + f y := by
  wlog hwlog : x ≤ y generalizing x y with H
  · have h := H y x
    simp [show y ≤ x by grind only] at h
    convert h using 1
    · rw [add_comm]
    · grind only
  by_cases hx : 0 ≤ x
  · exact additive_pos hf hx (show 0 ≤ y by grind only)
  · replace hx : 0 ≤ -x := by grind only
    by_cases hy : 0 ≤ y
    · by_cases hxy : 0 ≤ x + y
      · have h := additive_pos hf hxy hx
        rw [← f_odd hf] at h
        simp_all
      · have h := additive_pos hf (show 0 ≤ -(x+y) by grind only) hy
        simp at h
        rw [show -y+-x = -(x+y) by ring] at h
        rw [← f_odd hf x, ← f_odd hf (x+y)] at h
        linarith
    · have h := additive_pos hf hx (show 0 ≤ -y by grind only)
      rw [show -x+-y = -(x+y) by ring] at h
      rw [← f_odd hf x, ← f_odd hf y, ← f_odd hf (x+y)] at h
      linarith

-- Apply Cauchy four times to f
/--
@isnad1 id=eq.1h5v.s6.ceb8f380e77a from=translated src=- shape=ba8e02d8 vocab=4a8cd360
-/
lemma four_additive {f : ℝ → ℝ} (hf : FE f) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) :
    f (a + b + c + d) = f a + f b + f c + f d := by
  have h1 := additive hf (a+b+c) d
  have h2 := additive hf (a+b) c
  have h3 := additive hf a b
  linarith

-- Show the FE implies f(x) = f(1)*x
/--
@isnad1 id=eq.1h2v.s4.b3391e4d83a6 from=translated src=- shape=3148032b vocab=36eb1d1e
-/
lemma main_proof {f : ℝ → ℝ} (hf : FE f) (x : ℝ)  :
    f x = f 1 * x := by
  have h := squarish hf (x+1)
  rw [additive hf x 1] at h
  rw [show (x+1)^2 = x^2 + x + x + 1 by ring] at h
  rw [four_additive hf] at h
  rw [squarish hf] at h
  grind only

abbrev solution_set : Set (ℝ → ℝ) := { f | ∃ c : ℝ, ∀ x, f x = c * x }

end Usa2002P4
