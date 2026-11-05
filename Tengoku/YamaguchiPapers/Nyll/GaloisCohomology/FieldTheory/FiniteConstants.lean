/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Tengoku.Seed.FieldTheory.AlgebraicClosure
import Tengoku.Seed.GroupTheory.Torsion
import Tengoku.Seed.Algebra.Polynomial.Monic
import Tengoku.Seed.Data.Fintype.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite algebraic constant fields

A finite relative algebraic closure contains all roots of unity. It also
supplies an element outside the image of every map `x ↦ x ^ n - x`, for `n > 1`.
-/

namespace FieldTheory

universe u v
variable (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]

/-- Every root of unity lies in the relative algebraic closure.
@isnad1 id=mem.1h3v.s6.891a64c6b64b from=translated src=- shape=25e68022 vocab=dd10e3ab
-/
theorem torsionUnit_mem_algebraicClosure (z : Kˣ) (hz : IsOfFinOrder z) :
    (z : K) ∈ algebraicClosure F K := by
  apply mem_algebraicClosure_iff'.mpr
  apply IsIntegral.of_pow hz.orderOf_pos
  have hpow : (z : K) ^ orderOf z = 1 := by
    exact congrArg Units.val (pow_orderOf_eq_one z)
  rw [hpow]
  exact isIntegral_one

/-- A finite field of constants makes the full torsion subgroup of units finite.
@isnad1 id=finite.0h2v.s7.8e29deeec568 from=translated src=- shape=e9e48a71 vocab=f0a52d3b
-/
theorem finite_torsion_units_of_finite_algebraicClosure
    [Finite (algebraicClosure F K)] : Finite (CommGroup.torsion Kˣ) := by
  let f : CommGroup.torsion Kˣ → algebraicClosure F K := fun z =>
    ⟨(z.1 : K), torsionUnit_mem_algebraicClosure F K z.1 z.property⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact Units.ext (congrArg Subtype.val h)

/-- In particular, every prime-primary root group is finite.
@isnad1 id=finite.0h3v.s7.66579846ab57 from=translated src=- shape=a2c511fe vocab=2e277e48
-/
theorem finite_primaryComponent_of_finite_algebraicClosure
    [Finite (algebraicClosure F K)] (p : ℕ) [Fact p.Prime] :
    Finite (CommGroup.primaryComponent Kˣ p) := by
  have : Finite (CommGroup.torsion Kˣ) :=
    finite_torsion_units_of_finite_algebraicClosure F K
  have hle : CommGroup.primaryComponent Kˣ p ≤ CommGroup.torsion Kˣ := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, hn⟩
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

/-- If the algebraic constant field is finite, `x ↦ x ^ n - x` is not onto
for any exponent greater than one. This includes the Artin--Schreier map.
@isnad1 id=ex.1h3v.s6.ac8f330f6d1c from=translated src=- shape=ad897404 vocab=b2682c9c
-/
theorem exists_not_pow_sub_of_finite_algebraicClosure
    [Finite (algebraicClosure F K)] (n : ℕ) (hn : 1 < n) :
    ∃ a : K, ∀ x : K, x ^ n - x ≠ a := by
  classical
  let C := algebraicClosure F K
  have hnot : ¬ Function.Surjective (fun x : C => x ^ n - x) := by
    intro hs
    have hi := (Finite.injective_iff_surjective).mpr hs
    have h01 : (0 : C) = 1 := hi (by simp only [zero_pow (Nat.ne_zero_of_lt hn),
      one_pow, sub_self])
    exact zero_ne_one h01
  obtain ⟨a, ha⟩ := not_forall.mp hnot
  refine ⟨(a : K), ?_⟩
  intro x hx
  have hxC : IsIntegral C x := by
    refine ⟨Polynomial.X ^ n - (Polynomial.X + Polynomial.C a), ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X_add_C]
      exact WithBot.coe_lt_coe.mpr hn
    · change Polynomial.aeval x (Polynomial.X ^ n - (Polynomial.X + Polynomial.C a)) = 0
      simp only [map_sub, map_pow, Polynomial.aeval_X, map_add,
        Polynomial.aeval_C]
      exact sub_eq_zero.mpr ((sub_eq_iff_eq_add.mp hx).trans (add_comm _ _))
  have hxF : IsIntegral F x := isIntegral_trans x hxC
  let y : C := ⟨x, mem_algebraicClosure_iff'.mpr hxF⟩
  apply ha
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hx

end FieldTheory
