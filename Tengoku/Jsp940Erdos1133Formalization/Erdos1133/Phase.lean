import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.TrigZeroCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A constant phase makes the centered circle-node product real-valued. -/

noncomputable section
open scoped BigOperators ComplexConjugate Real
open Set Finset
open Erdos1152.V5

namespace Erdos1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/--
@isnad1 id=eq.0h2v.s7.0b1fa504b3af from=translated src=- shape=0a97e520 vocab=79f88071
-/
theorem conj_character (j : ℤ) (x : FourierCircle) :
    conj (character j x) = character (-j) x := by
  exact fourier_neg.symm

/--
@isnad1 id=eq.0h2v.s7.2ec2fbbaa5ff from=translated src=- shape=e7c439a8 vocab=a78f3994
-/
theorem character_neg_one_pow (k : ℕ) (x : FourierCircle) :
    character (-1) x ^ k = character (-(k : ℤ)) x := by
  rw [← conj_character, ← map_pow, character_one_pow, conj_character]

/--
@isnad1 id=eq.0h2v.s8.a4890eb7884c from=translated src=- shape=50279ccf vocab=65a4b402
-/
theorem conj_character_sub (x y : FourierCircle) :
    conj (character 1 x - character 1 y) =
      (-1 : ℂ) * character (-1) x * character (-1) y *
        (character 1 x - character 1 y) := by
  have hx : character (-1) x * character 1 x = 1 := by
    rw [← character_add]; norm_num
  have hy : character (-1) y * character 1 y = 1 := by
    rw [← character_add]; norm_num
  rw [map_sub, conj_character, conj_character]
  calc
    character (-1) x - character (-1) y =
      character (-1) x * (character (-1) y * character 1 y) -
        character (-1) y * (character (-1) x * character 1 x) := by rw [hx, hy]; ring
    _ = _ := by ring

/--
@isnad1 id=eq.1h3v.s8.655e14062c71 from=translated src=- shape=f50345e3 vocab=0295b736
-/
theorem circleNodeProduct_conj (N : ℕ) (Γ : Finset FourierCircle)
    (hΓ : Γ.card = 2 * N) (x : FourierCircle) :
    conj (circleNodeProduct N Γ x) =
      (∏ γ ∈ Γ, character (-1) γ) * circleNodeProduct N Γ x := by
  classical
  have hp : (∏ γ ∈ Γ, conj (character 1 x - character 1 γ)) =
      ((-1 : ℂ) * character (-1) x) ^ Γ.card *
        (∏ γ ∈ Γ, character (-1) γ) *
        ∏ γ ∈ Γ, (character 1 x - character 1 γ) := by
    simp_rw [conj_character_sub]
    simp only [Finset.prod_mul_distrib, Finset.prod_const]
    ring
  rw [circleNodeProduct_apply, map_mul, map_prod, conj_character, neg_neg, hp,
    hΓ, mul_pow, character_neg_one_pow]
  have he : (-1 : ℂ) ^ (2 * N) = 1 := by simp [pow_mul]
  rw [he, one_mul]
  calc
    _ = (character (N : ℤ) x * character (-((2 * N : ℕ) : ℤ)) x) *
        (∏ γ ∈ Γ, character (-1) γ) *
        ∏ γ ∈ Γ, (character 1 x - character 1 γ) := by ring
    _ = _ := by
      rw [← character_add,
        show (N : ℤ) + -((2 * N : ℕ) : ℤ) = -(N : ℤ) by omega]
      ring

/-- Any function satisfying a fixed unit conjugation relation admits a nonzero
constant phase making all its values real. No angle representatives are needed.
@isnad1 id=ex.2h3v.s7.7975be2a26a8 from=translated src=- shape=d2883551 vocab=4af4a6bf
-/
theorem exists_real_phase_of_conj {α : Type*} (F : α → ℂ) (A : ℂ)
    (hA : conj A * A = 1) (hF : ∀ x, conj (F x) = A * F x) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x, (c * F x).im = 0 := by
  by_cases hneg : A = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    intro x
    apply Complex.conj_eq_iff_im.mp
    rw [map_mul, Complex.conj_I, hF, hneg]
    ring
  · refine ⟨1 + A, ?_, ?_⟩
    · intro hz
      apply hneg
      have := congrArg (fun z : ℂ => z - 1) hz
      simpa using this
    · intro x
      apply Complex.conj_eq_iff_im.mp
      rw [map_mul, map_add, map_one, hF]
      calc
        (1 + conj A) * (A * F x) = (A + conj A * A) * F x := by ring
        _ = (1 + A) * F x := by rw [hA]; ring

/-- The actual centered node product with an even number of nodes is real after
one constant nonzero phase correction.
@isnad1 id=ex.1h2v.s6.d1d403ff35d8 from=translated src=- shape=a934bda5 vocab=f42246dd
-/
theorem circleNodeProduct_exists_real_phase (N : ℕ) (Γ : Finset FourierCircle)
    (hΓ : Γ.card = 2 * N) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x : FourierCircle,
      (c * circleNodeProduct N Γ x).im = 0 := by
  apply exists_real_phase_of_conj (circleNodeProduct N Γ)
    (∏ γ ∈ Γ, character (-1) γ)
  · rw [map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro γ hγ
    rw [conj_character, ← character_add]
    norm_num
  · exact circleNodeProduct_conj N Γ hΓ

end Erdos1133
