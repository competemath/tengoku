/-
# `Perm` in low arity, as explicit vectors

The partial compositions of the non-symmetric operad `Perm` that the low-weight deformation
complexes need, written out as vectors: arity two into arity two, arity three into arity two, and
arity two into arity three, at every slot. The rule is the one of `Operad.Perm`: outside the
inserted block a coordinate is scaled by the total of the inserted vector, inside it the slot's
coordinate scales the inserted one.

Also: the vectors with coordinate sum zero form an ideal of `Perm` (`sumZero`), because the total
of a composite is the product of the totals.
-/
import Tengoku.LeanOperads.Operad.Perm
import Tengoku.LeanOperads.Operad.Ideal
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/landonfox00/lean-operads@09ccda4a2b04, `Operad/PermLow.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

-- Some coordinates are closed by `simp` alone, others need `ring`; one combinator covers all.

namespace Operad

namespace Perm

variable {R : Type u} [CommRing R]

section Vectors

variable (x y : Perm R 2) (z : Perm R 3)

/--
@isnad1 id=eq.0h3v.s8.dea456814561 from=translated src=- shape=e9bec836 vocab=d0c95266
-/
lemma compFin_2_2_zero : compFin (R := R) (P := Perm R) (0 : Fin 2) x y
    = ![x 0 * y 0, x 0 * y 1, x 1 * (y 0 + y 1)] := by
  funext j
  rw [show (0 : Fin 2) = ⟨0, by omega⟩ from rfl, compFin_eq_comp 0 1 (P := Perm R) x y,
    reindex_apply, comp_eq]
  fin_cases j <;> simp [permComp, Fin.sum_univ_two] <;> ring

/--
@isnad1 id=eq.0h3v.s8.650ab42c6f1a from=translated src=- shape=a9bf350d vocab=d0c95266
-/
lemma compFin_2_2_one : compFin (R := R) (P := Perm R) (1 : Fin 2) x y
    = ![x 0 * (y 0 + y 1), x 1 * y 0, x 1 * y 1] := by
  funext j
  rw [show (1 : Fin 2) = ⟨1, by omega⟩ from rfl, compFin_eq_comp 1 0 (P := Perm R) x y,
    reindex_apply, comp_eq]
  fin_cases j <;> simp [permComp, Fin.sum_univ_two] <;> ring

/--
@isnad1 id=eq.0h3v.s8.2199e9869b72 from=translated src=- shape=f4efd2ba vocab=d0c95266
-/
lemma compFin_2_3_zero : compFin (R := R) (P := Perm R) (0 : Fin 2) x z
    = ![x 0 * z 0, x 0 * z 1, x 0 * z 2, x 1 * (z 0 + z 1 + z 2)] := by
  funext j
  rw [show (0 : Fin 2) = ⟨0, by omega⟩ from rfl, compFin_eq_comp 0 1 (P := Perm R) x z,
    reindex_apply, comp_eq]
  fin_cases j <;> simp [permComp, Fin.sum_univ_three] <;> ring

/--
@isnad1 id=eq.0h3v.s8.9cfd142db817 from=translated src=- shape=885b0e74 vocab=d0c95266
-/
lemma compFin_2_3_one : compFin (R := R) (P := Perm R) (1 : Fin 2) x z
    = ![x 0 * (z 0 + z 1 + z 2), x 1 * z 0, x 1 * z 1, x 1 * z 2] := by
  funext j
  rw [show (1 : Fin 2) = ⟨1, by omega⟩ from rfl, compFin_eq_comp 1 0 (P := Perm R) x z,
    reindex_apply, comp_eq]
  fin_cases j <;> simp [permComp, Fin.sum_univ_three] <;> ring

/--
@isnad1 id=eq.0h3v.s8.fafda93a6ffe from=translated src=- shape=2edeaa92 vocab=d0c95266
-/
lemma compFin_3_2_zero : compFin (R := R) (P := Perm R) (0 : Fin 3) z x
    = ![z 0 * x 0, z 0 * x 1, z 1 * (x 0 + x 1), z 2 * (x 0 + x 1)] := by
  funext j
  rw [show (0 : Fin 3) = ⟨0, by omega⟩ from rfl, compFin_eq_comp 0 2 (P := Perm R) z x,
    reindex_apply, comp_eq]
  fin_cases j <;> simp [permComp, Fin.sum_univ_two] <;> ring

/--
@isnad1 id=eq.0h3v.s8.0e35474e22b0 from=translated src=- shape=b173a910 vocab=d0c95266
-/
lemma compFin_3_2_one : compFin (R := R) (P := Perm R) (1 : Fin 3) z x
    = ![z 0 * (x 0 + x 1), z 1 * x 0, z 1 * x 1, z 2 * (x 0 + x 1)] := by
  funext j
  rw [show (1 : Fin 3) = ⟨1, by omega⟩ from rfl, compFin_eq_comp 1 1 (P := Perm R) z x,
    reindex_apply, comp_eq]
  fin_cases j <;> simp [permComp, Fin.sum_univ_two] <;> ring

/--
@isnad1 id=eq.0h3v.s8.9fbfb1b82375 from=translated src=- shape=01702365 vocab=d0c95266
-/
lemma compFin_3_2_two : compFin (R := R) (P := Perm R) (2 : Fin 3) z x
    = ![z 0 * (x 0 + x 1), z 1 * (x 0 + x 1), z 2 * x 0, z 2 * x 1] := by
  funext j
  rw [show (2 : Fin 3) = ⟨2, by omega⟩ from rfl, compFin_eq_comp 2 0 (P := Perm R) z x,
    reindex_apply, comp_eq]
  fin_cases j <;> simp [permComp, Fin.sum_univ_two] <;> ring

end Vectors

/-- **The vectors with coordinate sum zero form an ideal of `Perm`.**-/
def sumZero : OperadIdeal R (Perm R) where
  carrier n :=
    { carrier := {x | ∑ j, x j = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at hx hy ⊢
        rw [hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hx ⊢
        rw [← Finset.mul_sum, hx, mul_zero] }
  comp_mem_left a b n x hx y := by
    show ∑ j, permComp a b x y j = 0
    rw [sum_permComp, show ∑ i, x i = 0 from hx, zero_mul]
  comp_mem_right a b n x y hy := by
    show ∑ j, permComp a b x y j = 0
    rw [sum_permComp, show ∑ t, y t = 0 from hy, mul_zero]

/--
@isnad1 id=iff.0h3v.s8.23b4f028205c from=translated src=- shape=d4691ae7 vocab=22f3b439
-/
lemma mem_sumZero {n : ℕ} (x : Perm R n) : x ∈ (sumZero (R := R)).carrier n ↔ ∑ j, x j = 0 :=
  Iff.rfl

end Perm

end Operad
