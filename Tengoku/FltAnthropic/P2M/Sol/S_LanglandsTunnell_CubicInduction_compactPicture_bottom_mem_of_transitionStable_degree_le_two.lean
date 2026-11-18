import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.LinearAlgebra.Span.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two

set_option autoImplicit false

open MvPolynomial

namespace CompactPictureBottom

abbrev P3 := MvPolynomial (Fin 3) ℂ

noncomputable def Xi (ν : Fin 3 → ℂ) (p : P3) : Matrix (Fin 3) (Fin 3) P3 :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

noncomputable def lowerTwo (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))

noncomputable def lowerOne (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
      (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))

noncomputable def qsum (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)

noncomputable def sameTwo (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
    (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))

/--
@isnad1 id=eq.0h1v.s11.9f1eeb69ea46 from=translated src=- shape=13ebe92e vocab=32bf6227
-/
theorem sameTwo_eq (M : Matrix (Fin 3) (Fin 3) P3) :
    sameTwo M = C 6 * qsum M - (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2) *
      (pderiv 0 (pderiv 0 (qsum M)) + pderiv 1 (pderiv 1 (qsum M)) + pderiv 2 (pderiv 2 (qsum M))) := by
  simp only [sameTwo, qsum, Fin.sum_univ_three]

/--
@isnad1 id=eq.0h4v.s8.7f285222cca2 from=translated src=- shape=01ca82e0 vocab=2a808418
-/
theorem coeff_pderiv {σ : Type*} [DecidableEq σ] (i : σ) (m : σ →₀ ℕ) (f : MvPolynomial σ ℂ) :
    coeff m (pderiv i f) = (m i + 1) * coeff (m + Finsupp.single i 1) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = m + Finsupp.single i 1
    · subst h
      simp [mul_comm]
    · rw [ite_eq_right h]
      split_ifs with h'
      · have hs : s i = 0 := by
          by_contra hne
          apply h
          rw [← h']
          ext j
          simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
            Finsupp.single_apply]
          split_ifs with hj
          · subst hj; omega
          · omega
        simp [hs]
      · simp
  | add f g hf hg => simp [hf, hg, mul_add]

/--
@isnad1 id=eq.0h4v.s9.d1aa950ea35f from=translated src=- shape=c5da84c4 vocab=5af0ac4f
-/
theorem pderiv_comm {σ : Type*} [DecidableEq σ] (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  ext m
  simp only [coeff_pderiv]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [add_right_comm]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, ite_eq_right hij,
      ite_eq_right (Ne.symm hij), add_zero]
    ring

/--
@isnad1 id=eq.0h0v.s6.78037072c731 from=translated src=- shape=a01f1bb0 vocab=26950770
-/
@[scoped simp] lemma max01 : max (0 : Fin 3) 1 = 1 := by decide
/--
@isnad1 id=eq.0h0v.s6.4a4d9b703c99 from=translated src=- shape=a01f1bb0 vocab=26950770
-/
@[scoped simp] lemma max02 : max (0 : Fin 3) 2 = 2 := by decide
/--
@isnad1 id=eq.0h0v.s6.2b41fa172ba6 from=translated src=- shape=a01f1bb0 vocab=26950770
-/
@[scoped simp] lemma max12 : max (1 : Fin 3) 2 = 2 := by decide
/--
@isnad1 id=eq.0h0v.s6.fc10e1a7e517 from=translated src=- shape=a01f1bb0 vocab=26950770
-/
@[scoped simp] lemma max10 : max (1 : Fin 3) 0 = 1 := by decide
/--
@isnad1 id=eq.0h0v.s6.3b2225acd672 from=translated src=- shape=a01f1bb0 vocab=26950770
-/
@[scoped simp] lemma max20 : max (2 : Fin 3) 0 = 2 := by decide
/--
@isnad1 id=eq.0h0v.s6.40e12d716413 from=translated src=- shape=a01f1bb0 vocab=26950770
-/
@[scoped simp] lemma max21 : max (2 : Fin 3) 1 = 2 := by decide
/--
@isnad1 id=eq.0h0v.s6.2e01f5120853 from=translated src=- shape=a01f1bb0 vocab=a1354ccf
-/
@[scoped simp] lemma min01 : min (0 : Fin 3) 1 = 0 := by decide
/--
@isnad1 id=eq.0h0v.s6.a85db61277a2 from=translated src=- shape=a01f1bb0 vocab=a1354ccf
-/
@[scoped simp] lemma min02 : min (0 : Fin 3) 2 = 0 := by decide
/--
@isnad1 id=eq.0h0v.s6.fce0d82f7bbe from=translated src=- shape=a01f1bb0 vocab=a1354ccf
-/
@[scoped simp] lemma min12 : min (1 : Fin 3) 2 = 1 := by decide
/--
@isnad1 id=eq.0h0v.s6.2b0cebdf4c2d from=translated src=- shape=a01f1bb0 vocab=a1354ccf
-/
@[scoped simp] lemma min10 : min (1 : Fin 3) 0 = 0 := by decide
/--
@isnad1 id=eq.0h0v.s6.b739267593be from=translated src=- shape=a01f1bb0 vocab=a1354ccf
-/
@[scoped simp] lemma min20 : min (2 : Fin 3) 0 = 0 := by decide
/--
@isnad1 id=eq.0h0v.s6.9496f45d583c from=translated src=- shape=a01f1bb0 vocab=a1354ccf
-/
@[scoped simp] lemma min21 : min (2 : Fin 3) 1 = 1 := by decide

/--
@isnad1 id=eq.0h2v.s9.499c837758a2 from=translated src=- shape=cb223b64 vocab=b7fde74a
-/
lemma pdX (i j : Fin 3) : pderiv i (X j : P3) = if j = i then 1 else 0 := by
  classical
  rw [pderiv_X]; simp [Pi.single_apply]

/--
@isnad1 id=eq.0h2v.s9.1a3abf3c4d0b from=translated src=- shape=e50c0bc7 vocab=ab18e224
-/
lemma pdXsq (i j : Fin 3) : pderiv i (X j ^ 2 : P3) = if j = i then C 2 * X j else 0 := by
  rw [sq, pderiv_mul, pdX]
  split_ifs
  · simp only [map_ofNat]; ring
  · ring

/--
@isnad1 id=eq.0h2v.s8.af3f1c0f95a3 from=translated src=- shape=a5ab08f3 vocab=23cd0ceb
-/
lemma pd_ofNat (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (no_index (OfNat.ofNat n) : P3) = 0 := by
  rw [← map_ofNat (C : ℂ →+* P3) n]; exact pderiv_C

/--
@isnad1 id=eq.0h1v.s10.d8dbe6a4eb28 from=translated src=- shape=29c6ece3 vocab=efeb78a9
-/
lemma c10 (f : P3) : pderiv 1 (pderiv 0 f) = pderiv 0 (pderiv 1 f) := pderiv_comm _ _ _
/--
@isnad1 id=eq.0h1v.s10.b71783b6fde3 from=translated src=- shape=29c6ece3 vocab=efeb78a9
-/
lemma c20 (f : P3) : pderiv 2 (pderiv 0 f) = pderiv 0 (pderiv 2 f) := pderiv_comm _ _ _
/--
@isnad1 id=eq.0h1v.s10.347918354d14 from=translated src=- shape=29c6ece3 vocab=efeb78a9
-/
lemma c21 (f : P3) : pderiv 2 (pderiv 1 f) = pderiv 1 (pderiv 2 f) := pderiv_comm _ _ _

/--
@isnad1 id=eq.0h2v.s13.5a38936bf07d from=translated src=- shape=28bcea3c vocab=6d524274
-/
theorem lowerTwo_Xi (ν : Fin 3 → ℂ) (p : P3) :
    lowerTwo (Xi ν p) = C 2 * ((C (ν 0) - 1) * pderiv 0 (pderiv 0 p) + C (ν 1) * pderiv 1 (pderiv 1 p)
      + (C (ν 2) + 1) * pderiv 2 (pderiv 2 p)
      + X 0 * pderiv 0 (pderiv 1 (pderiv 1 p)) + X 0 * pderiv 0 (pderiv 2 (pderiv 2 p))
      - X 1 * pderiv 1 (pderiv 0 (pderiv 0 p)) + X 1 * pderiv 1 (pderiv 2 (pderiv 2 p))
      - X 2 * pderiv 2 (pderiv 0 (pderiv 0 p)) - X 2 * pderiv 2 (pderiv 1 (pderiv 1 p))) := by
  simp only [lowerTwo, Xi, Fin.sum_univ_three, Matrix.of_apply, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
    max01, max02, max12, max10, max20, max21, min01, min02, min12, min10, min20, min21,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pdX, zero_mul, add_zero,
    zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

/--
@isnad1 id=eq.0h1v.s14.66dd39301331 from=translated src=- shape=2d6ea1cb vocab=c876a8c8
-/
theorem lowerOne_eq (M : Matrix (Fin 3) (Fin 3) P3) :
    lowerOne M =
      (X 1 * pderiv 0 (pderiv 2 (M 0 0)) + X 1 * pderiv 1 (pderiv 2 (M 0 1)) + X 1 * pderiv 2 (pderiv 2 (M 0 2)))
      - (X 2 * pderiv 0 (pderiv 1 (M 0 0)) + X 2 * pderiv 1 (pderiv 1 (M 0 1)) + X 2 * pderiv 1 (pderiv 2 (M 0 2)))
      + (X 2 * pderiv 0 (pderiv 0 (M 1 0)) + X 2 * pderiv 0 (pderiv 1 (M 1 1)) + X 2 * pderiv 0 (pderiv 2 (M 1 2)))
      - (X 0 * pderiv 0 (pderiv 2 (M 1 0)) + X 0 * pderiv 1 (pderiv 2 (M 1 1)) + X 0 * pderiv 2 (pderiv 2 (M 1 2)))
      + (X 0 * pderiv 0 (pderiv 1 (M 2 0)) + X 0 * pderiv 1 (pderiv 1 (M 2 1)) + X 0 * pderiv 1 (pderiv 2 (M 2 2)))
      - (X 1 * pderiv 0 (pderiv 0 (M 2 0)) + X 1 * pderiv 0 (pderiv 1 (M 2 1)) + X 1 * pderiv 0 (pderiv 2 (M 2 2))) := by
  simp only [lowerOne, Fin.sum_univ_three, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, c10, c20, c21]
  norm_num
  ring

/--
@isnad1 id=eq.0h2v.s13.c4e165740279 from=translated src=- shape=af00edbb vocab=b1f5950f
-/
theorem lowerOne_Xi (ν : Fin 3 → ℂ) (p : P3) :
    lowerOne (Xi ν p) = C 2 * (C (ν 1 - ν 0 + 1) * (X 2 * pderiv 0 (pderiv 1 p))
      + C (ν 0 - ν 2 - 1) * (X 1 * pderiv 0 (pderiv 2 p))
      + C (ν 2 - ν 1 + 1) * (X 0 * pderiv 1 (pderiv 2 p))
      + X 2 * (X 1 * pderiv 1 (pderiv 0 (pderiv 1 p)))
      - X 1 * (X 1 * pderiv 1 (pderiv 0 (pderiv 2 p)))
      - X 0 * (X 2 * pderiv 1 (pderiv 1 (pderiv 1 p)))
      + X 0 * (X 1 * pderiv 1 (pderiv 1 (pderiv 2 p)))) := by
  rw [lowerOne_eq]
  simp only [Xi, Matrix.of_apply, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
    max01, max02, max12, max10, max20, max21, min01, min02, min12, min10, min20, min21,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pdX, zero_mul, add_zero,
    zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

/--
@isnad1 id=eq.0h2v.s13.fa37349fd787 from=translated src=- shape=562672e1 vocab=f8c711a0
-/
theorem qsum_Xi (ν : Fin 3 → ℂ) (p : P3) :
    qsum (Xi ν p) = C 2 * (C (ν 0) * (X 0 * pderiv 0 p) + C (ν 1) * (X 1 * pderiv 1 p)
      + C (ν 2) * (X 2 * pderiv 2 p))
      + X 0 ^ 2 * (pderiv 1 (pderiv 1 p) + pderiv 2 (pderiv 2 p))
      + X 1 ^ 2 * (pderiv 2 (pderiv 2 p) - pderiv 0 (pderiv 0 p))
      - X 2 ^ 2 * (pderiv 0 (pderiv 0 p) + pderiv 1 (pderiv 1 p)) := by
  simp only [qsum, Xi, Fin.sum_univ_three, Matrix.of_apply, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
    max01, max02, max12, max10, max20, max21, min01, min02, min12, min10, min20, min21,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pdX, zero_mul, add_zero,
    zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

/--
@isnad1 id=eq.0h3v.s10.44b76141de4c from=translated src=- shape=1e32713a vocab=f65a0b44
-/
theorem lowerTwo_Xi_dq (ν : Fin 3 → ℂ) (α β : ℂ) :
    lowerTwo (Xi ν (C α * (X 0 ^ 2 - X 2 ^ 2) + C β * (X 1 ^ 2 - X 2 ^ 2))) =
      C (4 * (α * (ν 0 - ν 2 - 2) + β * (ν 1 - ν 2 - 1))) := by
  rw [lowerTwo_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdXsq, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, ite_true, ite_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

/--
@isnad1 id=eq.0h3v.s11.d13eaaca942a from=translated src=- shape=90558ee5 vocab=cfecd39f
-/
theorem sameTwo_Xi_dq (ν : Fin 3 → ℂ) (α β : ℂ) :
    sameTwo (Xi ν (C α * (X 0 ^ 2 - X 2 ^ 2) + C β * (X 1 ^ 2 - X 2 ^ 2))) =
      C (16 * α * ν 0 + 8 * α * ν 2 + 4 * α - 8 * β * ν 1 + 8 * β * ν 2 + 8 * β) * (X 0 ^ 2 - X 2 ^ 2)
      + C (-8 * α * ν 0 + 8 * α * ν 2 - 8 * α + 16 * β * ν 1 + 8 * β * ν 2 - 4 * β) * (X 1 ^ 2 - X 2 ^ 2) := by
  rw [sameTwo_eq, qsum_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdXsq, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, ite_true, ite_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

/--
@isnad1 id=eq.0h2v.s9.d5ece2996529 from=translated src=- shape=b60efaff vocab=babbc349
-/
theorem lowerOne_Xi_X01 (ν : Fin 3 → ℂ) (z : ℂ) :
    lowerOne (Xi ν (C z * (X 0 * X 1))) = C (-2 * z * (ν 0 - ν 1 - 1)) * X 2 := by
  rw [lowerOne_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, ite_true, ite_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one, one_mul]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

/--
@isnad1 id=eq.0h2v.s9.f019d42a6c91 from=translated src=- shape=7e89b1e4 vocab=bf4ba64c
-/
theorem lowerOne_Xi_X02 (ν : Fin 3 → ℂ) (z : ℂ) :
    lowerOne (Xi ν (C z * (X 0 * X 2))) = C (2 * z * (ν 0 - ν 2 - 1)) * X 1 := by
  rw [lowerOne_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, ite_true, ite_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one, one_mul]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

/--
@isnad1 id=mem.2h3v.s8.a97c8d26ab47 from=translated src=- shape=3567c6e2 vocab=012826e4
-/
lemma mem_of_C_mul_mem (S : Submodule ℂ P3) (v : P3) (L : ℂ) (hL : L ≠ 0) (h : C L * v ∈ S) : v ∈ S := by
  have := S.smul_mem L⁻¹ h
  rwa [smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hL, map_one, one_mul] at this

/--
@isnad1 id=mem.7h3v.s11.e5a4b2cae80e from=translated src=- shape=316df7c5 vocab=5e30d39a
-/
theorem one_mem_of_stable (ν : Fin 3 → ℂ)
    (h01 : ν 0 - ν 1 - 1 ≠ 0) (h02 : ν 0 - ν 2 - 1 ≠ 0) (h12 : ν 1 - ν 2 - 1 ≠ 0)
    (S₀ S₂ : Submodule ℂ P3)
    (hS₀ : S₀ ≤ Submodule.span ℂ {(1 : P3)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 ^ 2 - X 2 ^ 2 : P3), X 1 ^ 2 - X 2 ^ 2})
    (hst : ∀ p ∈ S₂, lowerTwo (Xi ν p) ∈ S₀ ∧ sameTwo (Xi ν p) ∈ S₂)
    (hne : S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) : (1 : P3) ∈ S₀ := by

  have key : ∀ L : ℂ, C L ∈ S₀ → L = 0 ∨ (1 : P3) ∈ S₀ := by
    intro L hmem
    rcases eq_or_ne L 0 with hL | hL
    · exact Or.inl hL
    · exact Or.inr (mem_of_C_mul_mem S₀ 1 L hL (by rwa [mul_one]))
  rcases hne with h0 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h0
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₀ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul, mul_one] at hs
    exact (key z hs).resolve_left hz
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 (hS₂ hp)
    rw [smul_eq_C_mul, smul_eq_C_mul] at hp hp0
    obtain ⟨hL1, hS⟩ := hst _ hp
    obtain ⟨hL2, -⟩ := hst _ hS
    rw [lowerTwo_Xi_dq] at hL1
    rw [sameTwo_Xi_dq, lowerTwo_Xi_dq] at hL2
    rcases key _ hL1 with hz1 | h
    swap; · exact h
    rcases key _ hL2 with hz2 | h
    swap; · exact h
    exfalso
    apply hp0
    have hdet : (ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h01 h02) h12
    have hα : α = 0 := by
      have e : α * ((ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1)) = 0 := by
        linear_combination
          (-(-2 * ν 0 * ν 1 + 2 * ν 0 * ν 2 + 2 * ν 0 + 4 * ν 1 ^ 2 - ν 1 - 4 * ν 2 ^ 2 - 7 * ν 2 - 3) / 24) * hz1
          + ((ν 1 - ν 2 - 1) / 96) * hz2
      exact (mul_eq_zero.1 e).resolve_right hdet
    have hβ : β = 0 := by
      have e : β * ((ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1)) = 0 := by
        linear_combination
          ((4 * ν 0 ^ 2 - 2 * ν 0 * ν 1 - 5 * ν 0 + 2 * ν 1 * ν 2 - 2 * ν 1 - 4 * ν 2 ^ 2 - 5 * ν 2) / 24) * hz1
          + (-(ν 0 - ν 2 - 2) / 96) * hz2
      exact (mul_eq_zero.1 e).resolve_right hdet
    simp [hα, hβ]

/--
@isnad1 id=mem.5h3v.s10.2ad6ad822e10 from=translated src=- shape=94f9c338 vocab=99a85486
-/
theorem X_two_mem_of_stable (ν : Fin 3 → ℂ) (h01 : ν 0 - ν 1 - 1 ≠ 0)
    (S₁ S₂ : Submodule ℂ P3)
    (hS₁ : S₁ ≤ Submodule.span ℂ {(X 2 : P3)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 * X 1 : P3)})
    (hst : ∀ p ∈ S₂, lowerOne (Xi ν p) ∈ S₁)
    (hne : S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) : (X 2 : P3) ∈ S₁ := by
  rcases hne with h1 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₁ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hs
    exact mem_of_C_mul_mem S₁ _ z hz hs
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₂ hp)
    have hz : z ≠ 0 := by rintro rfl; exact hp0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hp
    have h := hst _ hp
    rw [lowerOne_Xi_X01] at h
    refine mem_of_C_mul_mem S₁ _ _ ?_ h
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) h01

/--
@isnad1 id=mem.5h3v.s10.19ac00928109 from=translated src=- shape=94f9c338 vocab=99a85486
-/
theorem X_one_mem_of_stable (ν : Fin 3 → ℂ) (h02 : ν 0 - ν 2 - 1 ≠ 0)
    (S₁ S₂ : Submodule ℂ P3)
    (hS₁ : S₁ ≤ Submodule.span ℂ {(X 1 : P3)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 * X 2 : P3)})
    (hst : ∀ p ∈ S₂, lowerOne (Xi ν p) ∈ S₁)
    (hne : S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) : (X 1 : P3) ∈ S₁ := by
  rcases hne with h1 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₁ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hs
    exact mem_of_C_mul_mem S₁ _ z hz hs
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₂ hp)
    have hz : z ≠ 0 := by rintro rfl; exact hp0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hp
    have h := hst _ hp
    rw [lowerOne_Xi_X02] at h
    refine mem_of_C_mul_mem S₁ _ _ ?_ h
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) h02

/--
@isnad1 id=ne.1h1v.s4.b2220dd7eff8 from=translated src=- shape=790175b1 vocab=d58150df
-/
lemma ne_zero_of_re_ne_zero {z : ℂ} (h : z.re ≠ 0) : z ≠ 0 := fun hz => h (by simp [hz])

end CompactPictureBottom
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two.CompactPictureBottom

open CompactPictureBottom in
/--
@isnad1 id=other.0h2v.s13.b4ddf4704998 from=translated src=- shape=70f7c38d vocab=e790db27
-/
theorem solution
    (τ τ₃ : ℝ) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₂ p) ∈ S₀ ∧ same₂ (Ξ ν₁₂ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₂ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ S₁) ∧
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₃ p) ∈ S₀ ∧ same₂ (Ξ ν₁₃ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₃ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ S₁) := by
  intro Ξ lower₂ lower₁ same₂ ν₁₂ ν₁₃

  have A01 : ν₁₂ 0 - ν₁₂ 1 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₂]; norm_num
  have A02 : ν₁₂ 0 - ν₁₂ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₂]; norm_num
  have A12 : ν₁₂ 1 - ν₁₂ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₂]; norm_num
  have B01 : ν₁₃ 0 - ν₁₃ 1 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₃]; norm_num
  have B02 : ν₁₃ 0 - ν₁₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₃]; norm_num
  have B12 : ν₁₃ 1 - ν₁₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₃]; norm_num
  refine ⟨fun S₀ S₂ h0 h2 hst hne => ?_, fun S₁ S₂ h1 h2 hst hne => ?_,
    fun S₀ S₂ h0 h2 hst hne => ?_, fun S₁ S₂ h1 h2 hst hne => ?_⟩
  · exact one_mem_of_stable ν₁₂ A01 A02 A12 S₀ S₂ h0 h2 hst hne
  · exact X_two_mem_of_stable ν₁₂ A01 S₁ S₂ h1 h2 hst hne
  · exact one_mem_of_stable ν₁₃ B01 B02 B12 S₀ S₂ h0 h2 hst hne
  · exact X_one_mem_of_stable ν₁₃ B02 S₁ S₂ h1 h2 hst hne
