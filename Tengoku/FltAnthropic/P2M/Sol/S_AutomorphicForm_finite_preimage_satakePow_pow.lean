import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_HeckeEigensystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_finite_preimage_satakePow_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_finite_preimage_satakePow_pow

set_option autoImplicit false

open AutomorphicForm

namespace SatakeFib

open Polynomial

/--
@isnad1 id=eq.0h6v.s7.1911c123192e from=translated src=- shape=db625ea9 vocab=f34d8d01
-/
theorem map_satakePow {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (s e : R) :
    φ (satakePow n s e) = satakePow n (φ s) (φ e) := by
  suffices h : ∀ n, φ (satakePow n s e) = satakePow n (φ s) (φ e) ∧
      φ (satakePow (n + 1) s e) = satakePow (n + 1) (φ s) (φ e) from (h n).1
  intro n
  induction n with
  | zero =>
    exact ⟨by rw [satakePow_zero, satakePow_zero, map_ofNat], by rw [satakePow_one, satakePow_one]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [satakePow_add_two, satakePow_add_two, map_sub, map_mul, map_mul, ih.1, ih.2]

noncomputable def satakePoly {R : Type*} [CommRing R] (n : ℕ) (b : R) : R[X] :=
  satakePow n X (C b)

/--
@isnad1 id=eq.0h4v.s5.b60828bcf53a from=translated src=- shape=7ff645d6 vocab=640782c9
-/
theorem eval_satakePoly {R : Type*} [CommRing R] (n : ℕ) (a b : R) :
    (satakePoly n b).eval a = satakePow n a b := by
  have h := map_satakePow (evalRingHom a) n (X : R[X]) (C b)
  rw [coe_evalRingHom, eval_X, eval_C] at h
  exact h

/--
@isnad1 id=and.0h3v.s6.02f79459bc1b from=translated src=- shape=f7ba6bb8 vocab=22c3a6f5
-/
theorem monic_satakePoly {R : Type*} [CommRing R] [Nontrivial R] (b : R) :
    ∀ n, (satakePoly n b).natDegree ≤ n ∧ (satakePoly (n + 1) b).Monic ∧
      (satakePoly (n + 1) b).natDegree = n + 1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show (satakePow 0 X (C b) : R[X]).natDegree ≤ 0
      rw [satakePow_zero]
      exact (natDegree_ofNat (R := R) 2).le
    · show (satakePow 1 X (C b) : R[X]).Monic
      rw [satakePow_one]; exact monic_X
    · show (satakePow 1 X (C b) : R[X]).natDegree = 0 + 1
      rw [satakePow_one, natDegree_X]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hmul : (X * satakePoly (n + 1) b).Monic := monic_X.mul h1
    have hdeg : (X * satakePoly (n + 1) b).natDegree = n + 2 := by
      rw [monic_X.natDegree_mul h1, natDegree_X, h2]; ring
    have hlt : (C b * satakePoly n b).natDegree < (X * satakePoly (n + 1) b).natDegree := by
      rw [hdeg]; exact (natDegree_C_mul_le b _).trans_lt (by omega)
    have e : satakePoly (n + 1 + 1) b = X * satakePoly (n + 1) b - C b * satakePoly n b :=
      satakePow_add_two n X (C b)
    refine ⟨h2.le, ?_, ?_⟩
    · rw [e]; exact hmul.sub_of_left (degree_lt_degree hlt)
    · rw [e, natDegree_sub_eq_left_of_natDegree_lt hlt, hdeg]

/--
@isnad1 id=finite.1h4v.s5.ef6bf0980ed2 from=translated src=- shape=347e2bea vocab=582ab5ad
-/
theorem finite_setOf_satakePow_eq {R : Type*} [CommRing R] [IsDomain R] (f : ℕ) (hf : f ≠ 0) (b c : R) :
    {a : R | satakePow f a b = c}.Finite := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨-, hmon, hdeg⟩ := monic_satakePoly b n
  have hlt : (C c).natDegree < (satakePoly (n + 1) b).natDegree := by
    rw [natDegree_C, hdeg]; omega
  have hne : satakePoly (n + 1) b - C c ≠ 0 := by
    intro h0
    have := natDegree_sub_eq_left_of_natDegree_lt hlt
    rw [h0, natDegree_zero, hdeg] at this
    omega
  refine (finite_setOfPred_isRoot hne).subset fun a ha => ?_
  show (satakePoly (n + 1) b - C c).IsRoot a
  rw [IsRoot, eval_sub, eval_C, eval_satakePoly, sub_eq_zero]
  exact ha

/--
@isnad1 id=finite.1h3v.s5.71dc78d2c6c9 from=translated src=- shape=9d57c45e vocab=808f6036
-/
theorem finite_setOf_pow_eq {R : Type*} [CommRing R] [IsDomain R] (f : ℕ) (hf : f ≠ 0) (c : R) :
    {b : R | b ^ f = c}.Finite := by
  have hlt : (C c).degree < ((X : R[X]) ^ f).degree := by
    rw [degree_X_pow]
    exact degree_C_le.trans_lt (by exact_mod_cast Nat.pos_of_ne_zero hf)
  have hne : (X : R[X]) ^ f - C c ≠ 0 := ((monic_X_pow f).sub_of_left hlt).ne_zero
  refine (finite_setOfPred_isRoot hne).subset fun b hb => ?_
  show ((X : R[X]) ^ f - C c).IsRoot b
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]
  exact hb

end SatakeFib

/--
@isnad1 id=finite.1h3v.s6.d6adcbffe288 from=translated src=- shape=1b778e0d vocab=b7a3cb34
-/
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    (f : ℕ) (hf : f ≠ 0) (c : R × R) :
    ((fun p : R × R => (satakePow f p.1 p.2, p.2 ^ f)) ⁻¹' {c}).Finite := by
  have hB := SatakeFib.finite_setOf_pow_eq f hf c.2
  have hA : (⋃ b ∈ {b : R | b ^ f = c.2}, {a : R | satakePow f a b = c.1}).Finite :=
    hB.biUnion fun b _ => SatakeFib.finite_setOf_satakePow_eq f hf b c.1
  refine (hA.prod hB).subset fun p hp => ?_
  have hp' : (satakePow f p.1 p.2, p.2 ^ f) = c := hp
  have h1 : satakePow f p.1 p.2 = c.1 := congrArg Prod.fst hp'
  have h2 : p.2 ^ f = c.2 := congrArg Prod.snd hp'
  exact ⟨Set.mem_biUnion (x := p.2) h2 h1, h2⟩
