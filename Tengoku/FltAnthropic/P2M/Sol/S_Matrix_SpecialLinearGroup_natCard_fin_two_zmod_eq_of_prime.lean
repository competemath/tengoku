import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime

set_option autoImplicit false

namespace SL2Card

open Matrix

variable (p : ℕ) [Fact p.Prime]

local notation "F" => ZMod p

/--
@isnad1 id=eq.0h1v.s8.8edd7b2635ce from=translated src=- shape=b81b288f vocab=a646cb88
-/
theorem range_toGL_eq_ker_det :
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range =
      (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    rw [MonoidHom.mem_ker]
    exact Matrix.SpecialLinearGroup.coeToGL_det s
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have := congrArg Units.val hg
      simpa using this
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) F), hdet⟩, ?_⟩
    apply Units.ext
    rfl

/--
@isnad1 id=surjecti.0h1v.s8.d3141bfa8973 from=translated src=- shape=63d11d85 vocab=0db7c2b8
-/
theorem det_surjective : Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ) := by
  intro u
  let A : Matrix (Fin 2) (Fin 2) F := Matrix.diagonal ![(u : F), 1]
  have hA : Matrix.det A = (u : F) := by
    simp [A, Matrix.det_diagonal, Fin.prod_univ_two]
  have hA0 : Matrix.det A ≠ 0 := by rw [hA]; exact u.ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0, ?_⟩
  apply Units.ext
  show Matrix.det ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = u
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hA]

/--
@isnad1 id=eq.0h1v.s6.a06e67ade29b from=translated src=- shape=2718adb9 vocab=ac632517
-/
theorem card_GL_two : Nat.card (GL (Fin 2) F) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [Matrix.card_GL_field 2, Fin.prod_univ_two, ZMod.card p]
  simp

end SL2Card

open SL2Card in
/--
@isnad1 id=eq.0h1v.s6.eacc1eca767e from=translated src=- shape=06881b32 vocab=d6a68308
-/
theorem solution (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set detH : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ := Matrix.GeneralLinearGroup.det with hdetH

  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup detH.ker

  have h2 : Nat.card (GL (Fin 2) (ZMod p) ⧸ detH.ker) = p - 1 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange detH).toEquiv,
      MonoidHom.range_eq_top.mpr (det_surjective p), Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]

  have h3 : Nat.card detH.ker = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [hdetH, ← range_toGL_eq_ker_det p]
    exact (Nat.card_congr (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv).symm
  rw [card_GL_two p, h2, h3] at h1

  have h4 : p ^ 2 - p = p * (p - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  rw [h4] at h1
  have hp1 : 0 < p - 1 := by omega

  have h5 : (p - 1) * (p * (p ^ 2 - 1)) = (p - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    calc (p - 1) * (p * (p ^ 2 - 1)) = (p ^ 2 - 1) * (p * (p - 1)) := by ring
      _ = (p - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := h1
  exact (Nat.eq_of_mul_eq_mul_left hp1 h5).symm
