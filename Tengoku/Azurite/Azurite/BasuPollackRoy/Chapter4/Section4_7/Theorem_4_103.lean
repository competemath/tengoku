/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.Elimination
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveZeroSet
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68
import Tengoku.Seed.Algebra.MvPolynomial.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.7, Theorem 4.103 (projective weak Bézout / projection of an algebraic set)

The projection of an algebraic subset of `ℙ_{k₀}(C) × ℙ_{k₁}(C)` onto the second factor `ℙ_{k₁}(C)`
is again algebraic. We wire the affine-cone elimination core (`Elimination.elimination`) to the
projective-space API of §4.7.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

namespace Theorem_4_103

/-! ### The variable-split equivalence `Σ → ⊕`. -/

/-- The variable-split equivalence: the sigma index `(i : Fin 2) × Fin (k i + 1)` is identified with
the sum `Fin (k 0 + 1) ⊕ Fin (k 1 + 1)`, block `0` going to `inl` and block `1` to `inr`.-/
def σequiv (k : Fin 2 → ℕ) :
    ((i : Fin 2) × Fin (k i + 1)) ≃ Fin (k 0 + 1) ⊕ Fin (k 1 + 1) where
  toFun s :=
    Fin.cases (motive := fun i => Fin (k i + 1) → Fin (k 0 + 1) ⊕ Fin (k 1 + 1))
      Sum.inl
      (fun i' j => Sum.inr (Fin.cast (by rw [Fin.eq_zero i']; rfl) j))
      s.1 s.2
  invFun := Sum.elim (fun j => ⟨0, j⟩) (fun j => ⟨1, j⟩)
  left_inv := by
    rintro ⟨i, j⟩
    fin_cases i <;> rfl
  right_inv := by
    rintro (j | j) <;> rfl

/--
@isnad1 id=eq.0h2v.s9.4c85d102f8e5 from=translated src=- shape=a761b1e1 vocab=00591611
-/
@[simp] theorem σequiv_symm_inl (k : Fin 2 → ℕ) (j : Fin (k 0 + 1)) :
    (σequiv k).symm (Sum.inl j) = ⟨0, j⟩ := rfl

/--
@isnad1 id=eq.0h2v.s9.3b96b40afb6f from=translated src=- shape=a761b1e1 vocab=2a349479
-/
@[simp] theorem σequiv_symm_inr (k : Fin 2 → ℕ) (j : Fin (k 1 + 1)) :
    (σequiv k).symm (Sum.inr j) = ⟨1, j⟩ := rfl

/--
@isnad1 id=eq.0h2v.s9.0b0bc68baff6 from=translated src=- shape=276b8919 vocab=441bd181
-/
@[simp] theorem σequiv_apply_zero (k : Fin 2 → ℕ) (j : Fin (k 0 + 1)) :
    σequiv k ⟨0, j⟩ = Sum.inl j := rfl

/--
@isnad1 id=eq.0h2v.s9.9fb3ba67b2ab from=translated src=- shape=276b8919 vocab=94bf1468
-/
theorem σequiv_apply_one (k : Fin 2 → ℕ) (j : Fin (k 1 + 1)) :
    σequiv k ⟨1, j⟩ = Sum.inr j := by
  apply (σequiv k).symm.injective
  rw [Equiv.symm_apply_apply, σequiv_symm_inr]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The vector reconstruction: given block-coordinate functions `a` (block 0) and `b` (block 1),
the assignment `s ↦ (Sum.elim a b) (σequiv s)` recovers the block-indexed assignment
`s ↦ v s.1 s.2` where `v 0 = a`, `v 1 = b`.
@isnad1 id=eq.2h5v.s9.9a167805c463 from=translated src=- shape=d2073d71 vocab=51488638
-/
theorem sumElim_σequiv (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R) (b : Fin (k 1 + 1) → Ri R)
    (v : (i : Fin 2) → (Fin (k i + 1) → Ri R)) (ha : v 0 = a) (hb : v 1 = b) :
    (fun s : (i : Fin 2) × Fin (k i + 1) => (Sum.elim a b) (σequiv k s)) = fun s => v s.1 s.2 := by
  funext s
  obtain ⟨i, j⟩ := s
  revert j
  refine Fin.cases ?_ (fun i' j => ?_) i
  · intro j
    rw [σequiv_apply_zero, Sum.elim_inl, ha]
  · obtain rfl : i' = 0 := Fin.eq_zero i'
    show Sum.elim a b (σequiv k ⟨1, j⟩) = v 1 j
    rw [σequiv_apply_one, Sum.elim_inr, hb]

/-! ### The split polynomial and the eval bridge. -/

variable {C : Type*} [CommRing C]

/-- **Eval bridge for `sumToIter`.** Evaluating the iterated polynomial `sumRingEquiv P` first in the
inner variables at `b` and then in the outer variables at `a` equals evaluating `P` at the combined
assignment `Sum.elim a b`.
@isnad1 id=eq.0h6v.s10.7e7d41604ed6 from=translated src=- shape=8099cb06 vocab=971a273c
-/
theorem eval_sumToIter {S₁ S₂ : Type*} (a : S₁ → C) (b : S₂ → C)
    (P : MvPolynomial (S₁ ⊕ S₂) C) :
    eval a (map (eval b) (sumRingEquiv C S₁ S₂ P)) = eval (Sum.elim a b) P := by
  induction P using MvPolynomial.induction_on with
  | C r => rw [sumRingEquiv_C, map_C, eval_C, eval_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, eval_add, hp, hq, eval_add]
  | mul_X p i hp =>
    cases i with
    | inl b₁ =>
      rw [map_mul, map_mul, eval_mul, hp, sumRingEquiv_X_inl, map_X, eval_X, eval_mul, eval_X,
        Sum.elim_inl]
    | inr c =>
      rw [map_mul, map_mul, eval_mul, hp, sumRingEquiv_X_inr, map_C, eval_C, eval_mul]
      simp only [eval_X, Sum.elim_inr]

/-- The split of a two-block polynomial `P` into an `X`-polynomial (block `0`) with `Y`-polynomial
(block `1`) coefficients: relabel the sigma variables to a sum, then iterate.-/
noncomputable def split (k : Fin 2 → ℕ)
    (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)) :
    MvPolynomial (Fin (k 0 + 1)) (MvPolynomial (Fin (k 1 + 1)) (Ri R)) :=
  sumRingEquiv (Ri R) (Fin (k 0 + 1)) (Fin (k 1 + 1)) (rename (σequiv k) P)

/-- **The eval-coords bridge.** Evaluating the split polynomial first in the inner (block-1) variables
at `v 1` and then in the outer (block-0) variables at `v 0` recovers `evalCoords P v`.
@isnad1 id=eq.0h4v.s12.eb01da3e74f3 from=translated src=- shape=b3f63239 vocab=6ddb1dbb
-/
theorem eval_split (k : Fin 2 → ℕ) (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R))
    (v : (i : Fin 2) → (Fin (k i + 1) → Ri R)) :
    eval (v 0) (map (eval (v 1)) (split k P)) = evalCoords P v := by
  rw [split, eval_sumToIter, eval_rename, evalCoords]
  congr 1
  rw [Function.comp_def]
  exact congrArg _ (sumElim_σequiv k (v 0) (v 1) v rfl rfl)

/-! ### Multihomogeneity translation. -/

/-! ### Renaming the elimination output into single-block (`Fin 1`) form. -/

/-- The single-block index equivalence `Fin (n+1) ≃ (i : Fin 1) × Fin (n+1)`.-/
def e1 (n : ℕ) : Fin (n + 1) ≃ ((_ : Fin 1) × Fin (n + 1)) where
  toFun j := ⟨0, j⟩
  invFun s := s.2
  left_inv _ := rfl
  right_inv := by rintro ⟨i, j⟩; obtain rfl : i = 0 := Subsingleton.elim _ _; rfl

/--
@isnad1 id=eq.0h2v.s8.9393299c24de from=translated src=- shape=396a7808 vocab=b1fbdca6
-/
@[simp] theorem e1_apply (n : ℕ) (j : Fin (n + 1)) : e1 n j = ⟨0, j⟩ := rfl

/-- `ProjVanishes` of the single-block renamed polynomial reduces to ordinary evaluation at the
representative of the (single) projective coordinate.
@isnad1 id=iff.0h4v.s13.5d855be0bc15 from=translated src=- shape=82192ecf vocab=ea13eb0f
-/
theorem projVanishes_rename_e1 {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) (Ri R))
    (y : (i : Fin 1) → complexProjectiveSpace R n) :
    ProjVanishes (k := fun _ : Fin 1 => n) (rename (e1 n) Q) y ↔ eval (y 0).rep Q = 0 := by
  rw [ProjVanishes, evalCoords, eval_rename]
  refine Iff.of_eq (congrArg (· = 0) ?_)
  refine congrArg (eval · Q) ?_
  funext j
  rfl

/-! ### Projective wiring. -/

/-- The two-block coordinate vector with block `0` equal to `a` and block `1` equal to `b`.-/
def blockVec (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R) (b : Fin (k 1 + 1) → Ri R) :
    (i : Fin 2) → (Fin (k i + 1) → Ri R) :=
  Fin.cases a (fun i' => (Fin.eq_zero i' ▸ b : Fin (k (Fin.succ i') + 1) → Ri R))

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/--
@isnad1 id=eq.0h4v.s7.e39db789186e from=translated src=- shape=22098457 vocab=a6bfe3cc
-/
@[simp] theorem blockVec_zero (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R)
    (b : Fin (k 1 + 1) → Ri R) : blockVec k a b 0 = a := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/--
@isnad1 id=eq.0h4v.s7.763ccb9a8be1 from=translated src=- shape=2ec603b5 vocab=a6bfe3cc
-/
@[simp] theorem blockVec_one (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R)
    (b : Fin (k 1 + 1) → Ri R) : blockVec k a b 1 = b := rfl

omit [IsRealClosed R] in
/-- Each block of a block vector built from nonzero vectors is nonzero.
@isnad1 id=ne.2h5v.s10.cf770b280433 from=translated src=- shape=2c19c1eb vocab=bd7b8865
-/
theorem blockVec_ne_zero (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R) (b : Fin (k 1 + 1) → Ri R)
    (i : Fin 2) (ha : a ≠ 0) (hb : b ≠ 0) : blockVec k a b i ≠ 0 := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · exact ha
  · obtain rfl : i' = 0 := Fin.eq_zero i'
    exact hb

/-- The split evaluation at `(a, b)` equals `evalCoords P` at the block vector `blockVec a b`.
@isnad1 id=eq.0h5v.s12.ad319964540d from=translated src=- shape=ff2b83e1 vocab=7da410aa
-/
theorem eval_split_blockVec {k : Fin 2 → ℕ}
    (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)) (a : Fin (k 0 + 1) → Ri R)
    (b : Fin (k 1 + 1) → Ri R) :
    eval a (map (eval b) (split k P)) = evalCoords P (blockVec k a b) := by
  rw [← eval_split k P (blockVec k a b), blockVec_zero, blockVec_one]

/-- `ProjVanishes P x` unfolds, via the split, to the two-stage evaluation of `split P`.
@isnad1 id=iff.0h4v.s13.87619f43126e from=translated src=- shape=c7e136fe vocab=950aba9b
-/
theorem projVanishes_iff_eval_split {k : Fin 2 → ℕ}
    (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R))
    (x : (i : Fin 2) → complexProjectiveSpace R (k i)) :
    ProjVanishes P x ↔
      eval (x 0).rep (map (eval (x 1).rep) (split k P)) = 0 := by
  rw [ProjVanishes, ← eval_split k P (fun i => (x i).rep)]

/-- **Rep-independence transfer for block 0.** Fixing the block-1 coordinate `y₁` (a line) and a
finite multihomogeneous family `Ps`, the existence of a block-0 line `x₀` whose representative makes
all `split`-evaluations vanish is equivalent to the existence of an arbitrary nonzero block-0 vector
`z` doing the same.
@isnad1 id=iff.1h4v.s14.08edf5c91c1a from=translated src=- shape=e4d9b695 vocab=d97d6b83
-/
theorem exists_line_iff_exists_nonzero {k : Fin 2 → ℕ}
    (Ps : Finset (MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)))
    (hPs : ∀ P ∈ Ps, ∃ dd : Fin 2 → ℕ, IsMultihomogeneous P dd)
    (y₁ : complexProjectiveSpace R (k 1)) :
    (∃ x₀ : complexProjectiveSpace R (k 0),
        ∀ P ∈ Ps, eval (x₀).rep (map (eval y₁.rep) (split k P)) = 0)
      ↔ (∃ z : Fin (k 0 + 1) → Ri R, z ≠ 0 ∧
          ∀ P ∈ Ps, eval z (map (eval y₁.rep) (split k P)) = 0) := by
  constructor
  · rintro ⟨x₀, hx₀⟩
    exact ⟨x₀.rep, x₀.rep_nonzero, hx₀⟩
  · rintro ⟨z, hz, hzvan⟩
    refine ⟨mkLine z hz, fun P hP => ?_⟩
    obtain ⟨dd, hdd⟩ := hPs P hP
    have hzP : eval z (map (eval y₁.rep) (split k P)) = 0 := hzvan P hP
    -- transfer the vanishing from `z` to `(mkLine z hz).rep` via rep-independence.
    rw [eval_split_blockVec]
    rw [eval_split_blockVec] at hzP
    -- the two block vectors agree on block 1 and span the same line on block 0.
    have hmk : ∀ i : Fin 2,
        mkLine (blockVec k (mkLine z hz).rep y₁.rep i)
          (blockVec_ne_zero k _ y₁.rep i (mkLine z hz).rep_nonzero y₁.rep_nonzero)
        = mkLine (blockVec k z y₁.rep i)
          (blockVec_ne_zero k z y₁.rep i hz y₁.rep_nonzero) := by
      refine Fin.cases ?_ (fun i' => ?_)
      · exact Projectivization.mk_rep (mkLine z hz)
      · obtain rfl : i' = 0 := Fin.eq_zero i'
        rfl
    rw [evalCoords_eq_zero_iff_of_mkLine_eq hdd _ _ hmk]
    exact hzP

/-- The two-block projective point with block `0` equal to `x₀` and block `1` equal to `y₁`.-/
def blockVecPt (k : Fin 2 → ℕ) (x₀ : complexProjectiveSpace R (k 0))
    (y₁ : complexProjectiveSpace R (k 1)) : (i : Fin 2) → complexProjectiveSpace R (k i) :=
  Fin.cases x₀ (fun i' => (Fin.eq_zero i' ▸ y₁ : complexProjectiveSpace R (k (Fin.succ i'))))

omit [LinearOrder R] [IsStrictOrderedRing R] in
/--
@isnad1 id=eq.0h4v.s6.049799fb51e1 from=translated src=- shape=907ed5a4 vocab=2245b441
-/
@[simp] theorem blockVecPt_zero (k : Fin 2 → ℕ) (x₀ : complexProjectiveSpace R (k 0))
    (y₁ : complexProjectiveSpace R (k 1)) : blockVecPt k x₀ y₁ 0 = x₀ := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
/--
@isnad1 id=eq.0h4v.s6.b20d82fbb5d8 from=translated src=- shape=7e3a5dc5 vocab=2245b441
-/
@[simp] theorem blockVecPt_one (k : Fin 2 → ℕ) (x₀ : complexProjectiveSpace R (k 0))
    (y₁ : complexProjectiveSpace R (k 1)) : blockVecPt k x₀ y₁ 1 = y₁ := rfl

end Theorem_4_103

open Theorem_4_103

end Azurite.BPR.Chapter4
