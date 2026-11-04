/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.HomotopyFamily
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.JacobianRank
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.Theorem_4_103

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.7, Proposition 4.106: the singular locus of the homotopy system is algebraic

For the homotopy system `S_{(λ:µ)} = (H_{1,λ,µ}, …, H_{k,λ,µ})` with `H_{i,λ,µ} = λ Pᵢ + µ Dᵢ`, the
set of pairs `(x, (λ:µ)) ∈ ℙ_k(C) × ℙ_1(C)` such that `x` is a *singular* projective zero of
`S_{(λ:µ)}` (a common zero whose projective Jacobian has rank `< k`) is an algebraic subset of the
product `ℙ_k(C) × ℙ_1(C)`. By Theorem 4.103 its projection `Δ` onto `ℙ_1(C)` (the discriminant
locus of the pencil) is therefore algebraic.

We model the product over the two-block index `kk = ![k, 1]` (block `0` = `ℙ_k(C)`, block `1` =
`ℙ_1(C)` carrying the pencil coordinates `λ = X⟨1,0⟩`, `µ = X⟨1,1⟩`). To avoid working with `pderiv`
inside the sigma ring, the Jacobian *entries* are encoded directly as multihomogeneous polynomials
`entryPoly` whose block-0 partials of `P` and `D` are renamed in, and the singular condition is the
simultaneous vanishing of the homotopy polynomials and of all maximal minors of the entry matrix.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

namespace SingularLocus

/-- The two-block multidegree index: block `0` is `ℙ_k(C)`, block `1` is `ℙ_1(C)`.-/
abbrev kk (k : ℕ) : Fin 2 → ℕ := ![k, 1]

/-- The sigma variable index for the two-block product `ℙ_k(C) × ℙ_1(C)`.-/
abbrev Sig (k : ℕ) : Type := (i : Fin 2) × Fin (kk k i + 1)

/-- The block-`0` variable embedding `Fin (k+1) → Sig`, `j ↦ ⟨0, j⟩`.-/
def emb0 (k : ℕ) : Fin (k + 1) → Sig k := fun j => ⟨0, j⟩

/--
@isnad1 id=injectiv.0h1v.s4.b13b2745d186 from=translated src=- shape=704cff23 vocab=8725f3f2
-/
theorem emb0_injective (k : ℕ) : Function.Injective (emb0 k) := by
  intro a b h
  simpa [emb0] using (Sigma.mk.inj_iff.mp h).2

/-- The common-zero polynomial `H_{i,λ,µ} = λ Pᵢ + µ Dᵢ` lifted into the sigma ring.-/
noncomputable def Hpoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin k) : MvPolynomial (Sig k) (Ri R) :=
  X (⟨1, 0⟩ : Sig k) * rename (emb0 k) (P i)
    + X (⟨1, 1⟩ : Sig k) * rename (emb0 k) (diagFactor (d i) i)

/-- The `(i, j)` Jacobian entry polynomial `λ ∂Pᵢ/∂Xⱼ + µ ∂Dᵢ/∂Xⱼ` lifted into the sigma ring.-/
noncomputable def entryPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin k) (j : Fin (k + 1)) : MvPolynomial (Sig k) (Ri R) :=
  X (⟨1, 0⟩ : Sig k) * rename (emb0 k) (pderiv j (P i))
    + X (⟨1, 1⟩ : Sig k) * rename (emb0 k) (pderiv j (diagFactor (d i) i))

/-- The maximal minor obtained by deleting block-`0` column `c` from the entry matrix.-/
noncomputable def minorPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (c : Fin (k + 1)) : MvPolynomial (Sig k) (Ri R) :=
  (Matrix.of fun i a : Fin k => entryPoly P d i (c.succAbove a)).det

/-- The defining family of the singular locus: the homotopy polynomials together with all maximal
minors of the Jacobian entry matrix.-/
noncomputable def Ps (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) :
    Finset (MvPolynomial (Sig k) (Ri R)) :=
  (Finset.univ.image (Hpoly P d)) ∪ (Finset.univ.image (fun c => minorPoly P d c))

/-! ### Generic multihomogeneity helpers (stated over an arbitrary block structure)

To keep elaboration from repeatedly unfolding `Sig k`/`kk` we state the multihomogeneity algebra
generically over an arbitrary block index `(i : Fin m) × Fin (κ i + 1)`. -/

section Generic

variable {A : Type*} [CommSemiring A] {m : ℕ} {κ : Fin m → ℕ}

/--
@isnad1 id=ismultih.0h4v.s7.0163f22bd681 from=translated src=- shape=c82084d7 vocab=430dbd1b
-/
theorem isMultihomogeneous_zero (d : Fin m → ℕ) :
    IsMultihomogeneous (0 : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) d := by
  intro i c hc
  simp [MvPolynomial.support_zero] at hc

/--
@isnad1 id=ismultih.2h6v.s7.5bf813f1816e from=translated src=- shape=c252a1a4 vocab=ed13319f
-/
theorem IsMultihomogeneous.of_support_subset
    {P Q : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A} {d : Fin m → ℕ}
    (h : Q.support ⊆ P.support) (hP : IsMultihomogeneous P d) : IsMultihomogeneous Q d :=
  fun i c hc => hP i c (h hc)

/--
@isnad1 id=ismultih.0h3v.s7.d597792d9117 from=translated src=- shape=ca786965 vocab=430dbd1b
-/
theorem isMultihomogeneous_one :
    IsMultihomogeneous (1 : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) (fun _ : Fin m => 0) := by
  classical
  intro i c hc
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hc
  obtain rfl : (0 : (i : Fin m) × Fin (κ i + 1) →₀ ℕ) = c := by
    by_contra h; rw [ite_eq_right h] at hc; exact hc rfl
  simp

/--
@isnad1 id=ismultih.1h7v.s7.d0d02edf8a5e from=translated src=- shape=fc513fb6 vocab=bfc888bd
-/
theorem IsMultihomogeneous.sum {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) (d : Fin m → ℕ)
    (h : ∀ i ∈ s, IsMultihomogeneous (f i) d) :
    IsMultihomogeneous (∑ i ∈ s, f i) d := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isMultihomogeneous_zero d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/--
@isnad1 id=ismultih.1h7v.s7.186a931e9857 from=translated src=- shape=ce468ea6 vocab=c668c4e7
-/
theorem IsMultihomogeneous.prod {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) (D : ι → (Fin m → ℕ))
    (h : ∀ i ∈ s, IsMultihomogeneous (f i) (D i)) :
    IsMultihomogeneous (∏ i ∈ s, f i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact isMultihomogeneous_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The determinant of a matrix of multihomogeneous entries, with the multidegree constant along
each row, is multihomogeneous of the summed multidegree.
@isnad1 id=ismultih.1h6v.s7.ee102bb4f2b5 from=translated src=- shape=76b1a774 vocab=61a4ae8b
-/
theorem isMultihomogeneous_det {B : Type*} [CommRing B] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial ((i : Fin m) × Fin (κ i + 1)) B))
    (D : Fin n → (Fin m → ℕ)) (hN : ∀ i a, IsMultihomogeneous (N i a) (D i)) :
    IsMultihomogeneous N.det (∑ i, D i) := by
  classical
  rw [Matrix.det_apply']
  apply IsMultihomogeneous.sum
  intro σ _
  -- the product `∏ i, N (σ i) i` is multihomog of `∑ i, D (σ i) = ∑ i, D i`
  have hprod : IsMultihomogeneous (∏ i, N (σ i) i) (∑ i, D (σ i)) :=
    IsMultihomogeneous.prod Finset.univ (fun i => N (σ i) i) (fun i => D (σ i))
      (fun i _ => hN (σ i) i)
  have hsum : (∑ i, D (σ i)) = ∑ i, D i := Equiv.sum_comp σ D
  rw [hsum] at hprod
  -- multiplying by the sign constant only shrinks support
  refine IsMultihomogeneous.of_support_subset (fun c hc => ?_) hprod
  have hsign : (↑↑(Equiv.Perm.sign σ) : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) B)
      = C (↑↑(Equiv.Perm.sign σ) : B) :=
    (map_intCast (C : B →+* MvPolynomial ((i : Fin m) × Fin (κ i + 1)) B) _).symm
  rw [MvPolynomial.mem_support_iff] at hc ⊢
  rw [hsign, MvPolynomial.coeff_C_mul] at hc
  exact fun h0 => hc (by rw [h0, mul_zero])

end Generic

/-! ### Multihomogeneity of the defining polynomials -/

/-! ### Evaluation bridges -/

set_option linter.unusedSectionVars false in
/-- Evaluating a renamed block-`0` polynomial at a sigma assignment reduces to evaluating the
original at the block-`0` representative.
@isnad1 id=eq.0h4v.s13.39ca960d99ba from=translated src=- shape=986789a2 vocab=122f0b5f
-/
theorem eval_rename_emb0 (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i))
    (Q : MvPolynomial (Fin (k + 1)) (Ri R)) :
    eval (fun s : Sig k => (xp s.1).rep s.2) (rename (emb0 k) Q)
      = eval (xp 0).rep Q := by
  rw [eval_rename]
  rfl

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h4v.s12.5cce236abeda from=translated src=- shape=126d01ad vocab=3e70c6c5
-/
theorem aeval_eq_eval (x : Fin (k + 1) → Ri R) (Q : MvPolynomial (Fin (k + 1)) (Ri R)) :
    aeval x Q = eval x Q :=
  DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval x) Q

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h6v.s13.bfaaab41838d from=translated src=- shape=1f68cb9b vocab=a9a238f8
-/
theorem evalCoords_Hpoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i)) (i : Fin k) :
    evalCoords (Hpoly P d i) (fun i => (xp i).rep)
      = aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) := by
  have hHP : homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i
      = C ((xp 1).rep 0) * P i + C ((xp 1).rep 1) * diagFactor (d i) i := rfl
  show MvPolynomial.eval (fun s : Sig k => (xp s.1).rep s.2) (Hpoly P d i)
      = aeval ((show complexProjectiveSpace R k from xp 0).rep)
          (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i)
  rw [Hpoly, hHP, aeval_eq_eval ((show complexProjectiveSpace R k from xp 0).rep)]
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  rw [eval_rename_emb0, eval_rename_emb0, eval_C, eval_C,
    show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 0⟩ : Sig k)) = (xp 1).rep 0 from
      eval_X _, show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 1⟩ : Sig k)) = (xp 1).rep 1 from
      eval_X _]
  rfl

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h7v.s11.2b55ede18a8c from=translated src=- shape=9236c314 vocab=a147e21a
-/
theorem evalCoords_entryPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i)) (i : Fin k) (j : Fin (k + 1)) :
    evalCoords (entryPoly P d i j) (fun i => (xp i).rep)
      = (projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1)) (xp 0)) i j := by
  have hpderiv : pderiv j (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i)
      = C ((xp 1).rep 0) * pderiv j (P i)
        + C ((xp 1).rep 1) * pderiv j (diagFactor (d i) i) := by
    rw [homotopyPoly, map_add, pderiv_C_mul, pderiv_C_mul]
  have hPJ : projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1))
        (show complexProjectiveSpace R k from xp 0) i j
      = aeval ((show complexProjectiveSpace R k from xp 0).rep)
          (pderiv j (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i)) := rfl
  show MvPolynomial.eval (fun s : Sig k => (xp s.1).rep s.2) (entryPoly P d i j)
      = projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1))
          (show complexProjectiveSpace R k from xp 0) i j
  rw [entryPoly, hPJ, hpderiv,
    aeval_eq_eval ((show complexProjectiveSpace R k from xp 0).rep)]
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  rw [eval_rename_emb0, eval_rename_emb0, eval_C, eval_C,
    show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 0⟩ : Sig k)) = (xp 1).rep 0 from
      eval_X _, show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 1⟩ : Sig k)) = (xp 1).rep 1 from
      eval_X _]
  rfl

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h6v.s11.8270f4590e81 from=translated src=- shape=6c4c9f86 vocab=68eb6d18
-/
theorem evalCoords_minorPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i)) (c : Fin (k + 1)) :
    evalCoords (minorPoly P d c) (fun i => (xp i).rep)
      = ((projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1)) (xp 0)).submatrix
          id c.succAbove).det := by
  rw [evalCoords, minorPoly]
  rw [RingHom.map_det (eval (fun s : Sig k => (xp s.1).rep s.2))]
  congr 1
  ext i a
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply,
    id_eq]
  have := evalCoords_entryPoly P d xp i (c.succAbove a)
  rw [evalCoords] at this
  exact this

end SingularLocus

open SingularLocus

/-- **BPR Proposition 4.106 (the singular locus).** The set of pairs `(x, (λ:µ)) ∈ ℙ_k(C) × ℙ_1(C)`
such that `x` is a *singular* projective zero of the homotopy system `S_{(λ:µ)}` (a common zero whose
projective Jacobian has rank `< k`).-/
def singularLocus (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) :
    Set ((i : Fin 2) → complexProjectiveSpace R ((![k, 1] : Fin 2 → ℕ) i)) :=
  {xp | (∀ i, aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) = 0)
        ∧ (projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1)) (xp 0)).rank < k}

/--
@isnad1 id=eq.1h4v.s8.e158268e76c0 from=translated src=- shape=bada456e vocab=ee1ffe43
-/
theorem singularLocus_eq_projZerOfFinset (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    singularLocus P d = projZerOfFinset (Ps P d) := by
  ext xp
  simp only [singularLocus, Set.mem_ofPred_eq, projZerOfFinset, Ps]
  constructor
  · rintro ⟨hzero, hrank⟩ Q hQ
    rw [Finset.mem_union] at hQ
    rcases hQ with hQ | hQ
    · -- `Q` is a homotopy polynomial
      rw [Finset.mem_image] at hQ
      obtain ⟨i, _, rfl⟩ := hQ
      rw [ProjVanishes, evalCoords_Hpoly]
      exact hzero i
    · -- `Q` is a maximal minor
      rw [Finset.mem_image] at hQ
      obtain ⟨c, _, rfl⟩ := hQ
      rw [ProjVanishes, evalCoords_minorPoly]
      have hP' : ∀ i, (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i).IsHomogeneous (d i) :=
        fun i => homotopyPoly_isHomogeneous P d hP _ _ i
      have hx : ∀ i, aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) = 0 := hzero
      exact (projJacobian_rank_lt_iff_forall_det_eq_zero hP' hx).mp hrank c
  · intro h
    have hP' : ∀ i, (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i).IsHomogeneous (d i) :=
      fun i => homotopyPoly_isHomogeneous P d hP _ _ i
    have hzero : ∀ i, aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) = 0 := by
      intro i
      have := h (Hpoly P d i)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      rwa [ProjVanishes, evalCoords_Hpoly P d xp i] at this
    refine ⟨hzero, ?_⟩
    rw [projJacobian_rank_lt_iff_forall_det_eq_zero hP' hzero]
    intro c
    have := h (minorPoly P d c)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩))
    rwa [ProjVanishes, evalCoords_minorPoly] at this

end Azurite.BPR.Chapter4
