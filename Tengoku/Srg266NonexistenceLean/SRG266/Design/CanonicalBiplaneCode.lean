/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.CoherentKernelIsolate
import Tengoku.Srg266NonexistenceLean.SRG266.Design.TernaryStarRecovery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric

namespace CoherentK11System

variable {P : Type*} [DecidableEq P] (K : CoherentK11System P)

noncomputable def closedStar (p : P) (a : Fin 11) : Finset P :=
  insert p ((Edge11.star a).image fun e => ((K.coordinate p).symm e).val)

theorem root_mem_closedStar (p : P) (a : Fin 11) : p ∈ K.closedStar p a := by
  classical
  exact Finset.mem_insert_self _ _

theorem card_closedStar (p : P) (a : Fin 11) : (K.closedStar p a).card = 11 := by
  classical
  have hi : Function.Injective (fun e => ((K.coordinate p).symm e).val) :=
    Subtype.val_injective.comp (K.coordinate p).symm.injective
  have hn : p ∉ (Edge11.star a).image (fun e => ((K.coordinate p).symm e).val) := by
    rintro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    exact ((K.coordinate p).symm e).property he
  rw [closedStar, Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ hi, Edge11.card_star]

theorem coordinate_mem_closedStar (p : P) (q : {q : P // q ≠ p}) (a : Fin 11) :
    q.val ∈ K.closedStar p a ↔ a ∈ (K.coordinate p q).vertices := by
  classical
  simp only [closedStar, Finset.mem_insert, q.property, false_or]
  constructor
  · intro h
    obtain ⟨e, he, hval⟩ := Finset.mem_image.mp h
    have heq : e = K.coordinate p q := by
      apply (K.coordinate p).symm.injective
      simpa using (Subtype.ext hval : (K.coordinate p).symm e = q)
    subst e
    exact Edge11.mem_star.mp he
  · intro h
    refine Finset.mem_image.mpr ⟨K.coordinate p q, Edge11.mem_star.mpr h, ?_⟩
    simp

end CoherentK11System

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

def ternaryColumn (B : Fin 210) : Fin 56 → ZMod 3 :=
  fun p => (Q.matrix p B : ZMod 3)

def ternaryCode : Submodule (ZMod 3) (Fin 56 → ZMod 3) :=
  Submodule.span (ZMod 3) (Set.range Q.ternaryColumn)

theorem ternaryColumn_mem (B : Fin 210) : Q.ternaryColumn B ∈ Q.ternaryCode :=
  Submodule.subset_span ⟨B, rfl⟩

theorem ternaryColumn_apply (B : Fin 210) (p : Fin 56) :
    Q.ternaryColumn B p = if Q.matrix p B = 1 then 1 else 0 := by
  rcases Q.entry_cases p B with h | h <;> simp [ternaryColumn, h]

theorem ternaryColumn_dot_eq_zero (B D : Fin 210) :
    dotProduct (Q.ternaryColumn B) (Q.ternaryColumn D) = 0 := by
  have heq : dotProduct (Q.ternaryColumn B) (Q.ternaryColumn D) =
      ((∑ p, Q.matrix p B * Q.matrix p D : ℤ) : ZMod 3) := by
    simp [dotProduct, ternaryColumn]
  rw [heq]
  by_cases h : B = D
  · subst D
    simp_rw [Q.binary]
    have hb := Q.block_size B
    change ∑ p, Q.matrix p B = 12 at hb
    rw [hb]
    decide
  · have hi := Q.block_intersections h
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hi
    rcases hi with hi | hi <;> rw [hi] <;> decide

theorem ternaryCode_selfOrthogonal
    {u v : Fin 56 → ZMod 3} (hu : u ∈ Q.ternaryCode) (hv : v ∈ Q.ternaryCode) :
    dotProduct u v = 0 := by
  refine Submodule.span_induction₂
    (p := fun u v _ _ => dotProduct u v = 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · rintro _ _ ⟨B, rfl⟩ ⟨D, rfl⟩
    exact Q.ternaryColumn_dot_eq_zero B D
  · intro v _; exact zero_dotProduct v
  · intro u _; exact dotProduct_zero u
  · intro u v w _ _ _ hu hv; simp [add_dotProduct, hu, hv]
  · intro u v w _ _ _ hv hw; simp [dotProduct_add, hv, hw]
  · intro a u v _ _ h; simp [smul_dotProduct, h]
  · intro a u v _ _ h; simp [dotProduct_smul, h]

def pairGramWord (p q : Fin 56) : Fin 56 → ZMod 3 :=
  ∑ B ∈ Q.blocksThroughPair p q, Q.ternaryColumn B

theorem pairGramWord_mem (p q : Fin 56) : Q.pairGramWord p q ∈ Q.ternaryCode :=
  Submodule.sum_mem _ fun B _ => Q.ternaryColumn_mem B

theorem pairGramWord_apply (p q x : Fin 56) :
    Q.pairGramWord p q x = (Q.tripleMultiplicity p q x : ZMod 3) := by
  classical
  simp only [pairGramWord, Finset.sum_apply, Q.ternaryColumn_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  unfold tripleMultiplicity
  congr 1
  ext B
  simp [blocksThroughPair, blocksThroughTriple, and_assoc]

theorem pairGramWord_at_root (p : Fin 56) (q : {q : Fin 56 // q ≠ p}) :
    Q.pairGramWord p q p = 0 := by
  rw [Q.pairGramWord_apply]
  have heq : Q.tripleMultiplicity p q p = (Q.blocksThroughPair p q).card := by
    unfold tripleMultiplicity
    congr 1
    ext B
    simp [blocksThroughPair, blocksThroughTriple]
    tauto
  rw [heq, Q.card_blocksThroughPair q.property.symm]
  decide

theorem pairGramWord_add_vmeet (p : Fin 56)
    (q x : {q : Fin 56 // q ≠ p}) :
    Q.pairGramWord p q x +
      (Edge11.vmeet (Q.toCoherentK11System.coordinate p q)
        (Q.toCoherentK11System.coordinate p x) : ZMod 3) = 2 := by
  let q' := neEquivPunctured p q
  let x' := neEquivPunctured p x
  have h := (Q.derived45 p).pairMult_add_vmeet_edgeEquiv q' x'
  have hc := congrArg (fun n : ℕ => (n : ZMod 3)) h
  rw [Nat.cast_add, Nat.cast_add] at hc
  have hdiag : ((if q' = x' then 9 else 0 : ℕ) : ZMod 3) = 0 := by
    split <;> decide
  rw [hdiag, add_zero] at hc
  rw [Q.derived_pairMult_eq_tripleMultiplicity] at hc
  rw [Q.pairGramWord_apply]
  exact hc

def outsideOne (p : Fin 56) : Fin 56 → ZMod 3 :=
  fun x => if x = p then 0 else 1

noncomputable def localStarVector (p : Fin 56) (a : Fin 11) : Fin 56 → ZMod 3 :=
  fun x => if hx : x = p then 0
    else if a ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices then 1 else 0

theorem edgePairGram_identity (p : Fin 56) (a b : Fin 11) (hab : a ≠ b) :
    Q.pairGramWord p ((Q.toCoherentK11System.coordinate p).symm (Edge11.mk' hab)) =
      (2 : ZMod 3) • outsideOne p - Q.localStarVector p a - Q.localStarVector p b := by
  let q := (Q.toCoherentK11System.coordinate p).symm (Edge11.mk' hab)
  have hq : Q.toCoherentK11System.coordinate p q = Edge11.mk' hab :=
    (Q.toCoherentK11System.coordinate p).apply_symm_apply _
  ext x
  by_cases hx : x = p
  · subst x
    simp [Q.pairGramWord_at_root, outsideOne, localStarVector]
  · have h := Q.pairGramWord_add_vmeet p q ⟨x, hx⟩
    rw [hq] at h
    have hmeet : Edge11.vmeet (Edge11.mk' hab)
        (Q.toCoherentK11System.coordinate p ⟨x, hx⟩) =
        (if a ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices then 1 else 0) +
        (if b ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices then 1 else 0) := by
      rw [Edge11.vmeet, Edge11.vertices_mk', ← Finset.filter_mem_eq_inter,
        Finset.card_filter]
      rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
    rw [hmeet, Nat.cast_add] at h
    change Q.pairGramWord p q x = _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, outsideOne,
      localStarVector, dite_eq_right hx, ite_eq_right hx, mul_one]
    have ha : ((if a ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices
        then 1 else 0 : ℕ) : ZMod 3) =
        if a ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices then 1 else 0 := by
      split <;> rfl
    have hb : ((if b ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices
        then 1 else 0 : ℕ) : ZMod 3) =
        if b ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices then 1 else 0 := by
      split <;> rfl
    rw [ha, hb] at h
    linear_combination h

theorem complementedStar_mem_ternaryCode (p : Fin 56) (a : Fin 11) :
    outsideOne p - Q.localStarVector p a ∈ Q.ternaryCode := by
  obtain ⟨b, c, hba, hca, hbc⟩ := exists_two_ne a
  apply TernaryStarRecovery.complement_mem_of_three_columns
    Q.ternaryCode (outsideOne p) (Q.localStarVector p a)
      (Q.localStarVector p b) (Q.localStarVector p c)
  · rw [← Q.edgePairGram_identity p a b hba.symm]
    exact Q.pairGramWord_mem _ _
  · rw [← Q.edgePairGram_identity p a c hca.symm]
    exact Q.pairGramWord_mem _ _
  · rw [← Q.edgePairGram_identity p b c hbc]
    exact Q.pairGramWord_mem _ _

theorem complementVector_closedStar (p : Fin 56) (a : Fin 11) :
    TernaryStarRecovery.complementVector (Q.toCoherentK11System.closedStar p a) =
      outsideOne p - Q.localStarVector p a := by
  classical
  ext x
  by_cases hx : x = p
  · subst x
    simp [TernaryStarRecovery.complementVector, outsideOne, localStarVector,
      Q.toCoherentK11System.root_mem_closedStar]
  · have hm := Q.toCoherentK11System.coordinate_mem_closedStar p ⟨x, hx⟩ a
    simp only [TernaryStarRecovery.complementVector, outsideOne, localStarVector,
      Pi.sub_apply, ite_eq_right hx, dite_eq_right hx]
    change (if x ∈ Q.toCoherentK11System.closedStar p a then 0 else 1) =
      1 - (if a ∈ (Q.toCoherentK11System.coordinate p ⟨x, hx⟩).vertices then 1 else 0)
    simp only [hm]
    split <;> simp

theorem closedStar_overlap_mod_three (p q : Fin 56) (a b : Fin 11) :
    (((Q.toCoherentK11System.closedStar p a ∩
      Q.toCoherentK11System.closedStar q b).card : ℕ) : ZMod 3) = 2 := by
  apply TernaryStarRecovery.overlap_eq_two_mod_three
    _ _ (Q.toCoherentK11System.card_closedStar p a)
      (Q.toCoherentK11System.card_closedStar q b)
  rw [Q.complementVector_closedStar, Q.complementVector_closedStar]
  exact Q.ternaryCode_selfOrthogonal (Q.complementedStar_mem_ternaryCode p a)
    (Q.complementedStar_mem_ternaryCode q b)

end ConcreteQSD56
end SRG266.QuasiSymmetric
