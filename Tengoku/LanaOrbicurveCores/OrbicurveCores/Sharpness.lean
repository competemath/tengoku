/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.FourGroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Certified coset enumeration: finite index in `SL(2, ℤ)`

The framework used to show that Takeuchi's four explicit groups are arithmetic
(`OrbicurveCores.SharpnessData`). Let `Γ = ⟨A, B⟩ ⊆ SL(2, ℝ)` with `A = M/√n`, `B = N/√k` for
integral `M, N` of determinants `n, k`. A word `w` in `A^{±1}, B^{±1}` evaluates to
`(1/√n)^a (1/√k)^b · W` with `W` integral (`coe_evalSL`). Hence identities between words and
integral matrices can be checked in integer arithmetic.

* A **cover certificate** is a finite list `R` of integral matrices (containing `1`, all of
  determinant `1`). For each `r ∈ R` and each `g ∈ {S, T, S⁻¹, T⁻¹}` it gives `r' ∈ R` and a
  word `w` with `r g = w r'`. Then `SL(2, ℤ) = ⋃_{r ∈ R} (Γ ∩ SL(2, ℤ)) r`, so `Γ ∩ SL(2, ℤ)`
  has finite index in `SL(2, ℤ)` (`relIndex_ne_zero_of_coverOK`).
* A **transversal certificate** is a finite list of words `u` (containing the empty word). For
  each `u` and each letter `x` it gives `u'` with `u x u'⁻¹` integral. Then `Γ ∩ SL(2, ℤ)` has
  finite index in `Γ` (`relIndex_ne_zero_of_transOK`).

All checks are Boolean functions evaluated by `decide`.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open scoped MatrixGroups

namespace OrbicurveCores.Sharp

/-- Integral `2 × 2` matrices as quadruples, for fast kernel evaluation. -/
structure IM where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

namespace IM

/-- Matrix product. -/
def mul (x y : IM) : IM :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

/-- The identity. -/
def one : IM := ⟨1, 0, 0, 1⟩

/-- Scalar multiple. -/
def smul (k : ℤ) (x : IM) : IM := ⟨k * x.a, k * x.b, k * x.c, k * x.d⟩

/-- The adjugate. -/
def adj (x : IM) : IM := ⟨x.d, -x.b, -x.c, x.a⟩

/-- The determinant. -/
def det (x : IM) : ℤ := x.a * x.d - x.b * x.c

/-- The negative. -/
def neg (x : IM) : IM := ⟨-x.a, -x.b, -x.c, -x.d⟩

/-- The real matrix. -/
def toR (x : IM) : Matrix (Fin 2) (Fin 2) ℝ := !![(x.a : ℝ), x.b; x.c, x.d]

lemma toR_one : one.toR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [one, toR]

lemma toR_smul (k : ℤ) (x : IM) : (smul k x).toR = (k : ℝ) • x.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [smul, toR]

/-- The element of `SL(2, ℤ)` (or `1` if the determinant is not `1`). -/
def toSLZ (x : IM) : SL(2, ℤ) :=
  if h : x.det = 1 then ⟨!![x.a, x.b; x.c, x.d], by simpa [det_fin_two, det] using h⟩ else 1

end IM

/-- `S`, `T`, `S⁻¹`, `T⁻¹` as integral matrices. -/
def genS : IM := ⟨0, -1, 1, 0⟩
/-- `T`. -/
def genT : IM := ⟨1, 1, 0, 1⟩
/-- `S⁻¹`. -/
def genSi : IM := ⟨0, 1, -1, 0⟩
/-- `T⁻¹`. -/
def genTi : IM := ⟨1, -1, 0, 1⟩

/-- The real homomorphism `SL(2, ℤ) → SL(2, ℝ)`. -/
abbrev φ : SL(2, ℤ) →* SL(2, ℝ) := SpecialLinearGroup.map (algebraMap ℤ ℝ)

/-! ### Words -/

section words

variable (M N : IM)

/-- The integral matrices of the letters `A, A⁻¹, B, B⁻¹` (up to the scalars `1/√n`, `1/√k`). -/
def letterInt : Fin 4 → IM
  | 0 => M
  | 1 => M.adj
  | 2 => N
  | 3 => N.adj

/-- The integral matrix of a word. -/
def evalInt : List (Fin 4) → IM
  | [] => IM.one
  | x :: w => (letterInt M N x).mul (evalInt w)

/-- Number of letters `A^{±1}` in a word. -/
def countA (w : List (Fin 4)) : ℕ := w.countP (fun x ↦ x.val < 2)

/-- Number of letters `B^{±1}` in a word. -/
def countB (w : List (Fin 4)) : ℕ := w.countP (fun x ↦ ¬ x.val < 2)

/-- The inverse word. -/
def invLetter : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

/-- The inverse of a word. -/
def invWord (w : List (Fin 4)) : List (Fin 4) := (w.map invLetter).reverse

end words

section evalSL

variable (A B : SL(2, ℝ))

/-- The letters `A, A⁻¹, B, B⁻¹`. -/
def letterSL : Fin 4 → SL(2, ℝ)
  | 0 => A
  | 1 => A⁻¹
  | 2 => B
  | 3 => B⁻¹

/-- The value of a word. -/
def evalSL : List (Fin 4) → SL(2, ℝ)
  | [] => 1
  | x :: w => letterSL A B x * evalSL w

end evalSL

lemma scal_cons (cA cB : ℝ) (x : Fin 4) (w : List (Fin 4)) :
    cA ^ countA (x :: w) * cB ^ countB (x :: w) =
      (if x.val < 2 then cA else cB) * (cA ^ countA w * cB ^ countB w) := by
  fin_cases x <;> simp [countA, countB, pow_succ] <;> ring

/-- The scalar `(1/√n)^a (1/√k)^b` is `1/s` when `s² = nᵃ kᵇ`. -/
lemma scalar_eq {n k a b s : ℕ} (hn : 0 < n) (hk : 0 < k) (hs : s ^ 2 = n ^ a * k ^ b) :
    ((Real.sqrt n)⁻¹ ^ a * (Real.sqrt k)⁻¹ ^ b) = (s : ℝ)⁻¹ := by
  have hs' : ((s : ℝ)) = Real.sqrt n ^ a * Real.sqrt k ^ b := by
    have h1 : (0 : ℝ) ≤ Real.sqrt n ^ a * Real.sqrt k ^ b := by positivity
    rw [← Real.sqrt_sq (Nat.cast_nonneg s), ← Real.sqrt_sq h1]
    congr 1
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a 2, mul_comm b 2, pow_mul, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast hs
  rw [hs', mul_inv, inv_pow, inv_pow]

/-! ### Cover certificates: finite index in `SL(2, ℤ)` -/

/-- An entry of a cover certificate: target index, word, scale. -/
abbrev Entry := ℕ × List (Fin 4) × ℕ

section cert

variable (M N : IM) (n k : ℕ)

/-- Check `r g = w r'` (up to the scale `s`, with `s² = nᵃkᵇ`). -/
def entryOK (R : List IM) (r g : IM) (e : Entry) : Bool :=
  decide (e.1 < R.length) &&
    ((evalInt M N e.2.1).mul (R.getD e.1 IM.one) == IM.smul e.2.2 (r.mul g)) &&
    (e.2.2 ^ 2 == n ^ countA e.2.1 * k ^ countB e.2.1)

/-- A cover certificate: rows `(r, e_S, e_T, e_{S⁻¹}, e_{T⁻¹})`. -/
abbrev CoverCert := List (IM × Entry × Entry × Entry × Entry)

/-- The Boolean check of a cover certificate. -/
def coverOK (C : CoverCert) : Bool :=
  (C.map (·.1)).contains IM.one &&
    C.all (fun row ↦ row.1.det == 1 &&
      entryOK M N n k (C.map (·.1)) row.1 genS row.2.1 &&
      entryOK M N n k (C.map (·.1)) row.1 genT row.2.2.1 &&
      entryOK M N n k (C.map (·.1)) row.1 genSi row.2.2.2.1 &&
      entryOK M N n k (C.map (·.1)) row.1 genTi row.2.2.2.2)

variable {M N n k}

lemma entryOK_sound {R : List IM} {r g : IM} {e : Entry} (h : entryOK M N n k R r g e = true) :
    ∃ r' ∈ R, ∃ w : List (Fin 4), ∃ s : ℕ, (evalInt M N w).mul r' = IM.smul s (r.mul g) ∧
      s ^ 2 = n ^ countA w * k ^ countB w := by
  simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hlt, heq⟩, hs⟩ := h
  refine ⟨R.getD e.1 IM.one, ?_, e.2.1, e.2.2, heq, hs⟩
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

lemma coverOK_sound {C : CoverCert} (h : coverOK M N n k C = true) :
    IM.one ∈ C.map (·.1) ∧ ∀ r ∈ C.map (·.1), r.det = 1 ∧
      ∀ g ∈ ({genS, genT, genSi, genTi} : Set IM), ∃ r' ∈ C.map (·.1),
        ∃ w : List (Fin 4), ∃ s : ℕ, (evalInt M N w).mul r' = IM.smul s (r.mul g) ∧
          s ^ 2 = n ^ countA w * k ^ countB w := by
  simp only [coverOK, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  intro r hr
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hr
  obtain ⟨⟨⟨⟨hdet, hS⟩, hT⟩, hSi⟩, hTi⟩ := h2 row hrow
  refine ⟨hdet, ?_⟩
  rintro g (rfl | rfl | rfl | rfl)
  · exact entryOK_sound hS
  · exact entryOK_sound hT
  · exact entryOK_sound hSi
  · exact entryOK_sound hTi

end cert

section cover

variable {A B : SL(2, ℝ)} {M N : IM} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
  (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt n)⁻¹ • M.toR)
  (hB : (B : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt k)⁻¹ • N.toR)
include hn hk hA hB

end cover

/-! ### Transversal certificates: finite index in `Γ` -/

/-- An entry of a transversal certificate: target index, integral matrix, scale. -/
abbrev Entry2 := ℕ × IM × ℕ

section trans

variable (M N : IM) (n k : ℕ)

/-- The word `u x u'⁻¹` of a transversal entry. -/
def transWord (U : List (List (Fin 4))) (u : List (Fin 4)) (x : Fin 4) (j : ℕ) : List (Fin 4) :=
  u ++ [x] ++ invWord (U.getD j [])

/-- Check that `u x u'⁻¹` is the integral matrix `Z` of determinant `1` (up to the scale `s`). -/
def entry2OK (U : List (List (Fin 4))) (u : List (Fin 4)) (x : Fin 4) (e : Entry2) : Bool :=
  decide (e.1 < U.length) &&
    (evalInt M N (transWord U u x e.1) == IM.smul e.2.2 e.2.1) &&
    (e.2.1.det == 1) &&
    (e.2.2 ^ 2 == n ^ countA (transWord U u x e.1) * k ^ countB (transWord U u x e.1))

/-- A transversal certificate: rows `(u, e_A, e_{A⁻¹}, e_B, e_{B⁻¹})`. -/
abbrev TransCert := List (List (Fin 4) × Entry2 × Entry2 × Entry2 × Entry2)

/-- The Boolean check of a transversal certificate. -/
def transOK (C : TransCert) : Bool :=
  (C.map (·.1)).contains [] &&
    C.all (fun row ↦
      entry2OK M N n k (C.map (·.1)) row.1 0 row.2.1 &&
      entry2OK M N n k (C.map (·.1)) row.1 1 row.2.2.1 &&
      entry2OK M N n k (C.map (·.1)) row.1 2 row.2.2.2.1 &&
      entry2OK M N n k (C.map (·.1)) row.1 3 row.2.2.2.2)

variable {M N n k}

lemma entry2OK_sound {U : List (List (Fin 4))} {u : List (Fin 4)} {x : Fin 4} {e : Entry2}
    (h : entry2OK M N n k U u x e = true) :
    ∃ u' ∈ U, ∃ Z : IM, ∃ s : ℕ, evalInt M N (u ++ [x] ++ invWord u') = IM.smul s Z ∧
      Z.det = 1 ∧
        s ^ 2 = n ^ countA (u ++ [x] ++ invWord u') * k ^ countB (u ++ [x] ++ invWord u') := by
  simp only [entry2OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hlt, heq⟩, hdet⟩, hs⟩ := h
  refine ⟨U.getD e.1 [], ?_, e.2.1, e.2.2, heq, hdet, hs⟩
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

end trans

section transversal

variable {A B : SL(2, ℝ)} {M N : IM} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
  (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt n)⁻¹ • M.toR)
  (hB : (B : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt k)⁻¹ • N.toR)
include hn hk hA hB

end transversal

end OrbicurveCores.Sharp
