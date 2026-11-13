import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTFellPair
import Tengoku.Seed.Algebra.Polynomial.RuleOfSigns
import Tengoku.Seed.Algebra.Polynomial.Taylor
import Tengoku.Seed.Topology.LocallyConstant.Basic
import Tengoku.Seed.Topology.Connected.TotallyDisconnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descartes continuity infrastructure for the Fell converse

The root-disjoint Fell step can be expressed as constancy of the number of
roots on either side of a fixed point along a real-rooted affine pencil.  The
lemmas here develop a coefficient-side route to that constancy.  The key
finite observation is that inserting additional nonzero signs into a
coefficient sign word cannot decrease its number of sign changes.
-/

open scoped Polynomial Topology

namespace CommutatorTheorem.BTFellDescartes

open Polynomial

/-- The nonzero coefficient signs, in descending degree order.-/
noncomputable def nonzeroCoeffSigns (p : ℝ[X]) : List SignType :=
  (p.coeffList.map SignType.sign).filter (· ≠ 0)

/-- Every nonzero coefficient sign of `p` occurs, in the same order, among
the nonzero coefficient signs of `q`.  This is the relation obtained by
perturbing coefficients that vanish in `p` while preserving all other
coefficient signs.-/
def CoeffSignRefines (p q : ℝ[X]) : Prop :=
  List.Sublist (nonzeroCoeffSigns p) (nonzeroCoeffSigns q)

theorem signVariations_eq_destutter_length_sub_one (p : ℝ[X]) :
    p.signVariations =
      ((nonzeroCoeffSigns p).destutter (· ≠ ·)).length - 1 := by
  rfl

/-- Inserting nonzero signs cannot decrease the number of sign changes.-/
theorem signVariations_le_of_coeffSignRefines {p q : ℝ[X]}
    (h : CoeffSignRefines p q) :
    p.signVariations ≤ q.signVariations := by
  rw [signVariations_eq_destutter_length_sub_one,
    signVariations_eq_destutter_length_sub_one]
  apply Nat.sub_le_sub_right
  apply List.IsChain.length_le_length_destutter_ne
  · exact (List.destutter_sublist _ _).trans h
  · exact List.isChain_destutter _ _

/-- The number of coefficient sign changes never exceeds the polynomial's
natural degree.  This is the elementary upper bound complementary to
Descartes' lower bound by the number of positive roots.-/
theorem signVariations_le_natDegree (p : ℝ[X]) :
    p.signVariations ≤ p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [signVariations_eq_destutter_length_sub_one]
  calc
    ((nonzeroCoeffSigns p).destutter (· ≠ ·)).length - 1 ≤
        (nonzeroCoeffSigns p).length - 1 :=
      Nat.sub_le_sub_right (List.destutter_sublist _ _).length_le 1
    _ ≤ p.coeffList.length - 1 := by
      apply Nat.sub_le_sub_right
      simpa [nonzeroCoeffSigns] using
        List.length_filter_le (fun s : SignType ↦ s ≠ 0)
          (p.coeffList.map SignType.sign)
    _ = p.natDegree := by
      simp [Polynomial.length_coeffList_eq_ite, hp]

/-- Entrywise description of the descending coefficient list.-/
theorem coeffList_getElem_eq_coeff_natDegree_sub
    {p : ℝ[X]} (hp : p ≠ 0) (i : ℕ) (hi : i < p.coeffList.length) :
    p.coeffList[i] = p.coeff (p.natDegree - i) := by
  simp [Polynomial.coeffList,
    withBotSucc_degree_eq_natDegree_add_one hp] at hi ⊢

/-- Multiplication by `X` appends a zero constant coefficient to the
descending coefficient list.-/
theorem coeffList_mul_X_eq_append_zero
    {p : ℝ[X]} (hp : p ≠ 0) :
    (p * X).coeffList = p.coeffList ++ [0] := by
  have hmul : p * X ≠ 0 := mul_ne_zero hp X_ne_zero
  have hdeg : (p * X).natDegree = p.natDegree + 1 := by
    simp [natDegree_mul hp X_ne_zero]
  apply List.ext_getElem
  · simp [Polynomial.length_coeffList_eq_ite, hp, hmul, hdeg]
  · intro i hi hi'
    by_cases hip : i < p.coeffList.length
    · rw [List.getElem_append_left hip]
      rw [coeffList_getElem_eq_coeff_natDegree_sub hmul,
        coeffList_getElem_eq_coeff_natDegree_sub hp, hdeg]
      have hiNat : i ≤ p.natDegree := by
        simpa [Polynomial.length_coeffList_eq_ite, hp] using hip
      have hindex : p.natDegree + 1 - i = p.natDegree - i + 1 := by
        omega
      rw [hindex, coeff_mul_X]
    · have hieq : i = p.coeffList.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hi'
        omega
      subst i
      simp [coeffList_getElem_eq_coeff_natDegree_sub hmul, hdeg,
        Polynomial.length_coeffList_eq_ite, hp]

/-- Appending the zero introduced by multiplication with `X` does not alter
the nonzero coefficient sign word.-/
theorem nonzeroCoeffSigns_mul_X {p : ℝ[X]} (hp : p ≠ 0) :
    nonzeroCoeffSigns (p * X) = nonzeroCoeffSigns p := by
  unfold nonzeroCoeffSigns
  rw [coeffList_mul_X_eq_append_zero hp, List.map_append,
    List.filter_append]
  simp

/-- Multiplication by `X` preserves coefficient sign variations.-/
theorem signVariations_mul_X {p : ℝ[X]} (hp : p ≠ 0) :
    (p * X).signVariations = p.signVariations := by
  simp only [signVariations_eq_destutter_length_sub_one,
    nonzeroCoeffSigns_mul_X hp]

/-- A pointwise sign-preservation relation on equal-length sign words.-/
def SignWordRefines (u v : List SignType) : Prop :=
  List.Forall₂ (fun a b ↦ a = 0 ∨ a = b) u v

/-- Removing zero entries from a sign word that is pointwise refined gives
a sublist of the refined nonzero word.-/
theorem filter_ne_zero_sublist_of_signWordRefines
    {u v : List SignType} (h : SignWordRefines u v) :
    List.Sublist (u.filter (· ≠ 0)) (v.filter (· ≠ 0)) := by
  induction h with
  | nil => simp
  | cons hab huv ih =>
      rename_i a b u v
      rcases hab with rfl | hab
      · by_cases hb : b = 0
        · simpa [hb] using ih
        · simpa [hb] using (ih.cons b)
      · subst b
        by_cases ha : a = 0
        · simpa [ha] using ih
        · simpa [ha] using ih.cons_cons a

end CommutatorTheorem.BTFellDescartes
