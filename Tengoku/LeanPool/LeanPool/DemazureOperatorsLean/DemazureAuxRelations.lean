/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/
module

public import Tengoku.LeanPool.LeanPool.DemazureOperatorsLean.DemazureAux
public import Tengoku

/-!
# LeanPool.DemazureOperatorsLean.DemazureAuxRelations
-/

@[expose] public section

noncomputable section
namespace Demazure

-- Some computations are quite heavy, so we increase the number of heartbeats

open MvPolynomial

variable {n : ℕ} (n_pos : n > 0)

/- Composition relations for Demazure operators -/
-- Start by proving that the Demazure Operator applied two times is the zero operator
/--
@isnad1 id=eq.0h3v.s4.fe3d79d94f8a from=translated src=- shape=47feb9d9 vocab=552e4f55
-/
lemma demaux_order_two : ∀ (i : Fin n) (p : PolyFraction n),
  (DemAux i  ∘ DemAux i) p = zero := by
  intro i p
  rcases get_polyfraction_rep p with ⟨p', rfl⟩
  dsimp [DemAux]
  rw[lift_r]
  rw[lift_r]
  rw[zero]
  apply Quotient.sound
  rw[← equiv_r]
  simp[r, DemAux']
  ring

/-- Two indices are non-adjacent when the adjacent transpositions they determine are disjoint. -/
def NonAdjacent (i j : Fin n) : Prop :=
 (Fin.castSucc i : Fin (n + 1)) ≠ (Fin.castSucc j : Fin (n + 1)) ∧
  (Fin.castSucc i : Fin (n + 1)) ≠ (Fin.succ j : Fin (n + 1)) ∧
  (Fin.succ i : Fin (n + 1)) ≠ (Fin.castSucc j : Fin (n + 1)) ∧
  (Fin.succ i : Fin (n + 1)) ≠ (Fin.succ j : Fin (n + 1))

/--
@isnad1 id=eq.0h6v.s7.dcc9740f085a from=translated src=- shape=fa78b88a vocab=6df26f45
-/
lemma equiv_swap_mul_eq_comp {a b c d k : Fin n} :
(Equiv.swap a b * Equiv.swap c d) k = (Equiv.swap a b ∘ Equiv.swap c d) k := by
  rfl

/--
@isnad1 id=eq.0h6v.s7.b2ab855cde5b from=translated src=- shape=e32e9a9c vocab=05524e1c
-/
lemma renameEquiv_swap_ext {a b c d : Fin n} {R : Type} [CommSemiring R] :
    rename (Equiv.swap a b * Equiv.swap c d) =
      (rename (Equiv.swap a b ∘ Equiv.swap c d) :
        MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R) := by
  rfl

-- Now prove that demazure operators with non-adjacent indices commute
/--
@isnad1 id=eq.1h3v.s8.f00b3e2ac042 from=translated src=- shape=6e0b8e2e vocab=d7ea8211
-/
lemma transposition_commutes_non_adjacent (i j : Fin n) (h : NonAdjacent i j) :
  Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j) =
   Equiv.swap (Fin.castSucc j) (Fin.succ j) * Equiv.swap (Fin.castSucc i) (Fin.succ i) := by
    rcases h with ⟨h1, h2, h3, h4⟩
    have h_disjoint :
        Equiv.Perm.Disjoint (Equiv.swap i.castSucc i.succ)
          (Equiv.swap j.castSucc j.succ) := by
      intro k
      apply or_iff_not_imp_left.mpr
      intro h
      rcases Equiv.eq_or_eq_of_swap_apply_ne_self h with h | h
      · simpa [h] using Equiv.swap_apply_of_ne_of_ne h1 h2
      · simpa [h] using Equiv.swap_apply_of_ne_of_ne h3 h4
    rw[Equiv.Perm.Disjoint.commute h_disjoint]

/--
@isnad1 id=eq.1h3v.s9.23d0c49c24e6 from=translated src=- shape=87c5b607 vocab=7288ed02
-/
lemma transposition_commutes_non_adjacent' (i j : Fin n) (h : NonAdjacent i j) :
  Equiv.swap (Fin.castSucc i) (Fin.succ i) ∘ Equiv.swap (Fin.castSucc j) (Fin.succ j) =
   Equiv.swap (Fin.castSucc j) (Fin.succ j) ∘ Equiv.swap (Fin.castSucc i) (Fin.succ i) := by
  have h_mul := transposition_commutes_non_adjacent i j h
  funext k
  have h_comp : (Equiv.swap i.castSucc i.succ ∘ Equiv.swap j.castSucc j.succ) k =
      (Equiv.swap j.castSucc j.succ ∘ Equiv.swap i.castSucc i.succ) k := by
    simp only [← Equiv.Perm.coe_mul]
    exact congr_fun (congrArg Equiv.toFun h_mul) k
  exact h_comp

/--
@isnad1 id=eq.1h4v.s7.278a51b9337c from=translated src=- shape=fb62fe31 vocab=bace31e4
-/
lemma swap_variables_commutes_non_adjacent (i j : Fin n) (h : NonAdjacent i j)
    {p : MvPolynomial (Fin (n + 1)) ℂ} :
    SwapVariablesFun (Fin.castSucc i) (Fin.succ i)
        (SwapVariablesFun (Fin.castSucc j) (Fin.succ j) p) =
      SwapVariablesFun (Fin.castSucc j) (Fin.succ j)
        (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p) := by
    dsimp [SwapVariablesFun]
    simp[transposition_commutes_non_adjacent' i j h]

/--
@isnad1 id=eq.1h4v.s6.cb02c2f33af5 from=translated src=- shape=8b063eff vocab=a99b3394
-/
lemma demaux_commutes_non_adjacent (i j : Fin n) (h : NonAdjacent i j) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      (DemAux i ∘ DemAux j) (mk' p) = (DemAux j ∘ DemAux i) (mk' p) := by
  intro p
  dsimp [DemAux, mk']
  repeat rw[lift_r]
  apply mk_eq.mpr
  simp[DemAux']
  simp [swap_variables_commutes_non_adjacent i j h]
  rcases h with ⟨h1, h2, h3, h4⟩
  simp[h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm]
  ring

/-- Prove some relations between Demazure operators and multiplication by monomials, in the
adjacent and non-adjacent cases
@isnad1 id=eq.1h4v.s7.6a23370e9930 from=translated src=- shape=1b24652c vocab=f642c826
-/
lemma demaux_mul_monomial_non_adjacent (i j : Fin n) (h : NonAdjacent i j) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      DemAux i (mk' (p * X (Fin.castSucc j))) =
        (DemAux i (mk' p)) * (mk' (X (Fin.castSucc j))) := by
  intro p
  dsimp [DemAux, mul]
  apply mk_eq.mpr
  simp[DemAux', mul']
  rcases h with ⟨h1, h2, h3, h4⟩
  simp [h1.symm, h3.symm]
  ring

/--
@isnad1 id=eq.1h3v.s7.21bf916c558f from=translated src=- shape=1cd3fa6a vocab=b6852277
-/
lemma demaux_mul_monomial_adjacent (i : Fin n) (_h : i + 1 < n) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      (DemAux i (mk' (p * X (Fin.castSucc i)))) =
        (DemAux i (mk' p)) * (mk' (X (Fin.succ i))) + mk' p := by
  intro p
  dsimp [DemAux, mk']
  repeat rw[lift_r]
  apply mk_eq.mpr
  simp[DemAux', mul', add']
  ring

/--
@isnad1 id=eq.1h4v.s5.9ff5cba52529 from=translated src=- shape=4d8fe358 vocab=00fc2386
-/
lemma symm_invariant_swap_variables {i j : Fin n} {g : MvPolynomial (Fin n) ℂ}
   (h : MvPolynomial.IsSymmetric g) :
  SwapVariablesFun i j g = g := by
  dsimp [SwapVariablesFun]
  exact h (Equiv.swap i j)

/- Now we prove that symmetric polynomials act as scalars -/
/-- A quotient fraction represented by symmetric numerator and denominator polynomials. -/
def IsSymmetric (p : PolyFraction n) : Prop := ∃p' : PolyFraction' n,
 mk p' = p ∧ MvPolynomial.IsSymmetric p'.numerator ∧ MvPolynomial.IsSymmetric p'.denominator

/--
@isnad1 id=eq.1h4v.s5.54303fa8a097 from=translated src=- shape=f8adcc9c vocab=dfc3cdcf
-/
lemma demaux_mul_symm (i : Fin n) (g f : PolyFraction n) (h : IsSymmetric g) :
  DemAux i (g*f) = g*(DemAux i f) := by
  rcases h with ⟨g', ⟨rfl, g_num_symm, g_denom_symm⟩⟩
  rcases get_polyfraction_rep f with ⟨f', rfl⟩
  rw[mk_mul]
  dsimp [DemAux]
  repeat rw[lift_r]
  rw[← simp_mul']
  rw[← simp_mul]
  rw[mk_mul]
  rw[mk_eq]
  simp[DemAux']
  simp[symm_invariant_swap_variables g_num_symm, symm_invariant_swap_variables g_denom_symm]
  ring

-- Prove the relation between demazure operations with adjacent indices
/--
@isnad1 id=eq.3h3v.s10.17781fa27303 from=translated src=- shape=b60049aa vocab=1dca19a2
-/
lemma transposition_commutes_adjacent {i : Fin n} {j : Fin (n + 1)} (h0 : i < n + 1)
    (h1 : i + 1 < n + 1) (h2 : i + 2 < n + 1) :
    Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩
        (Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩
          (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩ j)) =
      Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩
        (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩
          (Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ j)) := by
  simp[Equiv.swap_apply_def]
  by_cases c0 : j = ⟨i, h0⟩
  · simp[c0]
  · by_cases c1 : j = ⟨i + 1, h1⟩
    · simp[c1]
    · by_cases c2 : j = ⟨i + 2, h2⟩
      · simp[c2]
      · simp[c0,c1,c2]

/--
@isnad1 id=eq.3h2v.s10.dcb29a83750c from=translated src=- shape=ed90b632 vocab=aa309214
-/
lemma transposition_commutes_adjacent' {i : Fin n} (h0 : i < n + 1)
    (h1 : i + 1 < n + 1) (h2 : i + 2 < n + 1) :
    (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩ ∘
          (Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩) ∘
        (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩) :
      Fin (n + 1) → Fin (n + 1)) =
      Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ ∘
        (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩) ∘
          (Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩) := by
  funext k
  exact transposition_commutes_adjacent h0 h1 h2

/--
@isnad1 id=eq.3h3v.s9.185400bb5e47 from=translated src=- shape=7d9157b7 vocab=78fc4512
-/
lemma swap_variables_commutes_adjacent {i : Fin n} {p : MvPolynomial (Fin (n + 1)) ℂ}
    (h0 : i < n + 1) (h1 : i + 1 < n + 1) (h2 : i + 2 < n + 1) :
    SwapVariablesFun ⟨i, h0⟩ ⟨i + 1, h1⟩
        (SwapVariablesFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩
          (SwapVariablesFun ⟨i, h0⟩ ⟨i + 1, h1⟩ p)) =
      SwapVariablesFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩
        (SwapVariablesFun ⟨i, h0⟩ ⟨i + 1, h1⟩
          (SwapVariablesFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ p)) := by
  simp [SwapVariablesFun, transposition_commutes_adjacent' h0 h1 h2]

/--
@isnad1 id=eq.0h1v.s5.a4348bf7fba5 from=translated src=- shape=14dae261 vocab=fc0e7020
-/
@[simp]
lemma omg {i : ℕ} : i + 1 + 1 = i + 2 := by
  ring

-- This takes a lot of time to compute
/--
@isnad1 id=eq.1h3v.s7.b872eea31d58 from=translated src=- shape=7ffcdc58 vocab=12b8afc1
-/
lemma demaux_commutes_adjacent (i : Fin n) (h : i + 1 < n) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      (DemAux i ∘ DemAux ⟨i+1, h⟩ ∘ DemAux i) (mk' p) =
        (DemAux ⟨i+1, h⟩ ∘ DemAux i ∘ DemAux ⟨i+1, h⟩) (mk' p) := by
  intro p
  dsimp [DemAux, mk']
  repeat rw [lift_r]
  simp [DemAux', Fin.castSucc, Fin.succ, Fin.castAdd, Fin.castLE]
  have h0 : i < n + 1 := by linarith
  have h1 : i + 1 < n + 1 := by linarith
  have h2 : i + 2 < n + 1 := by linarith
  simp [swap_variables_commutes_adjacent h0 h1 h2]
  ring

end Demazure

end
