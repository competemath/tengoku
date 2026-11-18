import Tengoku.Seed.LinearAlgebra.Matrix.SpecialLinearGroup
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Data.Nat.Prime.Basic
import Tengoku.Seed.Algebra.Group.Commutator
import Tengoku.Seed.GroupTheory.Commutator.Basic
import Tengoku.Seed.GroupTheory.Abelianization.Defs
import Tengoku.Seed.GroupTheory.IsPerfect
import Tengoku.Seed.GroupTheory.Subgroup.Centralizer
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Algebra.IsPrimePow
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Group
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ihara_isPerfect_SL2_ZMod_prime_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ihara_isPerfect_SL2_ZMod_prime_pow

open Matrix

open scoped MatrixGroups
open scoped commutatorElement

namespace SolImpl

section Helpers
variable {G : Type*} [Group G]

end Helpers

section Unipotents
variable (m : ℕ)

def upperE (x : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, x; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def lowerE (x : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

variable {m}

@[scoped simp]
theorem upperE_coe (x : ZMod m) :
    ((upperE m x : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, x; 0, 1] := rfl

@[scoped simp]
theorem lowerE_coe (x : ZMod m) :
    ((lowerE m x : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, 0; x, 1] := rfl

theorem lowerE_mul (x y : ZMod m) : lowerE m x * lowerE m y = lowerE m (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerE_coe, lowerE_coe, lowerE_coe, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

@[scoped simp]
theorem lowerE_zero : lowerE m 0 = 1 := by
  apply Subtype.ext; rw [lowerE_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem lowerE_natCast (k : ℕ) : lowerE m (k : ZMod m) = lowerE m 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← ih, lowerE_mul, Nat.cast_succ]

theorem lowerE_eq_pow [NeZero m] (x : ZMod m) : lowerE m x = lowerE m 1 ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact lowerE_natCast x.val

variable (m) in

def rotB : SL(2, ZMod m) := upperE m 1 * lowerE m (-1) * upperE m 1

theorem rotB_coe :
    ((rotB m : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![0, 1; -1, 0] := by
  rw [rotB, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, upperE_coe,
    lowerE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rotB_mul_upperE (x : ZMod m) : rotB m * upperE m x = lowerE m (-x) * rotB m := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, rotB_coe,
    upperE_coe, lowerE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rotB_pow_four : rotB m ^ 4 = 1 := by
  have hsq : ((rotB m * rotB m : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) =
      !![-1, 0; 0, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, rotB_coe, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h4 : rotB m ^ 4 = (rotB m * rotB m) * (rotB m * rotB m) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  apply Subtype.ext
  rw [h4, Matrix.SpecialLinearGroup.coe_mul, hsq, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end Unipotents

section Generation
variable {m : ℕ}

theorem eq_unipotent_word_of_bottomLeft_inv (X : SL(2, ZMod m)) (v : ZMod m)
    (hv : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 * v = 1) :
    X = upperE m (((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) * v) *
          lowerE m ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0) *
          upperE m (((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * v) := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 *
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 -
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 *
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 = 1 := by
    have h := X.2; rwa [Matrix.det_fin_two] at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    upperE_coe, lowerE_coe, upperE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  symm; ext i j; fin_cases i <;> fin_cases j
  · simp; linear_combination ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) * hv
  · simp
    linear_combination v * hdet +
      ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 +
        ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) *
        ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * v) * hv
  · simp
  · simp; linear_combination ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * hv

theorem mem_closure_unipotents_of_isUnit_bottomLeft (X : SL(2, ZMod m))
    (h : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0)) :
    X ∈ Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) := by
  obtain ⟨u, hu⟩ := h
  have hv : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 * (↑u⁻¹ : ZMod m) = 1 := by
    rw [← hu]; exact u.mul_inv
  rw [eq_unipotent_word_of_bottomLeft_inv X (↑u⁻¹ : ZMod m) hv]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)

theorem isUnit_of_castHom_ne_zero {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (x : ZMod (p ^ k))
    (h : ZMod.castHom (dvd_pow_self p hk) (ZMod p) x ≠ 0) : IsUnit x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd; apply h
  have hx : x = ((x.val : ℕ) : ZMod (p ^ k)) := (ZMod.natCast_zmod_val x).symm
  rw [hx, map_natCast, ZMod.natCast_eq_zero_iff]; exact hdvd

theorem isUnit_or_isUnit_of_det (hm : IsPrimePow m) {a b c d : ZMod m}
    (h : a * d - b * c = 1) : IsUnit a ∨ IsUnit c := by
  obtain ⟨p, k, hpp, hkpos, rfl⟩ := hm
  have hp : p.Prime := Nat.prime_iff.mpr hpp
  have hk : k ≠ 0 := hkpos.ne'
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  by_contra hcon; rw [not_or] at hcon
  have ha : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a = 0 := by
    by_contra h0; exact hcon.1 (isUnit_of_castHom_ne_zero hp hk a h0)
  have hc : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra h0; exact hcon.2 (isUnit_of_castHom_ne_zero hp hk c h0)
  have h1 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) (a * d - b * c) = 1 := by
    rw [h, map_one]
  rw [map_sub, map_mul, map_mul, ha, hc, zero_mul, mul_zero, sub_zero] at h1
  exact one_ne_zero h1.symm

theorem isUnit_add_of_isUnit_of_not_isUnit (hm : IsPrimePow m) {a c : ZMod m}
    (ha : IsUnit a) (hc : ¬IsUnit c) : IsUnit (a + c) := by
  obtain ⟨p, k, hpp, hkpos, rfl⟩ := hm
  have hp : p.Prime := Nat.prime_iff.mpr hpp
  have hk : k ≠ 0 := hkpos.ne'
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hc0 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra h0; exact hc (isUnit_of_castHom_ne_zero hp hk c h0)
  have ha0 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a ≠ 0 := by
    intro h0
    have hmap := ha.map (ZMod.castHom (dvd_pow_self p hk) (ZMod p))
    rw [h0] at hmap; exact not_isUnit_zero hmap
  apply isUnit_of_castHom_ne_zero hp hk
  rw [map_add, hc0, add_zero]; exact ha0

theorem closure_unipotents_eq_top (hm : IsPrimePow m) :
    Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) = ⊤ := by
  rw [eq_top_iff]; intro X _
  by_cases hc : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0)
  · exact mem_closure_unipotents_of_isUnit_bottomLeft X hc
  · have hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 *
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 -
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 *
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 = 1 := by
      have h := X.2; rwa [Matrix.det_fin_two] at h
    have ha : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0) :=
      (isUnit_or_isUnit_of_det hm hdet).resolve_right hc
    have hentry : ((lowerE m 1 * X : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 =
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 +
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, lowerE_coe, Matrix.mul_apply, Fin.sum_univ_two]
      simp
    have hsum : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 +
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0) :=
      isUnit_add_of_isUnit_of_not_isUnit hm ha hc
    have h2 : lowerE m 1 * X ∈
        Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) := by
      apply mem_closure_unipotents_of_isUnit_bottomLeft
      rw [hentry]; exact hsum
    have h3 : X = lowerE m (-1) * (lowerE m 1 * X) := by
      rw [← mul_assoc, lowerE_mul, neg_add_cancel, lowerE_zero, one_mul]
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)) h2

end Generation

section AbelianizationBound

variable (m : ℕ) in

def alphaA : Abelianization (SL(2, ZMod m)) := Abelianization.of (lowerE m 1)

variable {m : ℕ}

theorem abelianization_of_surjective :
    Function.Surjective
      (Abelianization.of : SL(2, ZMod m) → Abelianization (SL(2, ZMod m))) :=
  fun x => QuotientGroup.induction_on x fun g => ⟨g, rfl⟩

theorem of_lowerE_natCast (k : ℕ) :
    Abelianization.of (lowerE m (k : ZMod m)) = alphaA m ^ k := by
  rw [lowerE_natCast, map_pow, alphaA]

theorem of_lowerE [NeZero m] (x : ZMod m) :
    Abelianization.of (lowerE m x) = alphaA m ^ x.val := by
  rw [lowerE_eq_pow, map_pow, alphaA]

theorem of_upperE (x : ZMod m) :
    Abelianization.of (upperE m x) = Abelianization.of (lowerE m (-x)) := by
  have h := congrArg Abelianization.of (rotB_mul_upperE (m := m) x)
  rw [map_mul, map_mul] at h
  rw [mul_comm (Abelianization.of (lowerE m (-x))) (Abelianization.of (rotB m))] at h
  exact mul_left_cancel h

theorem mem_zpowers_alphaA (hm : IsPrimePow m) (y : Abelianization (SL(2, ZMod m))) :
    y ∈ Subgroup.zpowers (alphaA m) := by
  haveI : NeZero m := ⟨by have := hm.two_le; omega⟩
  have h1 : Subgroup.closure (Abelianization.of ''
      (Set.range (upperE m) ∪ Set.range (lowerE m))) = ⊤ := by
    rw [← MonoidHom.map_closure, closure_unipotents_eq_top hm]
    exact Subgroup.map_top_of_surjective _ abelianization_of_surjective
  have h2 : Subgroup.closure (Abelianization.of ''
      (Set.range (upperE m) ∪ Set.range (lowerE m))) ≤ Subgroup.zpowers (alphaA m) := by
    rw [Subgroup.closure_le]
    rintro z ⟨w, hw, rfl⟩
    rcases hw with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [SetLike.mem_coe, of_upperE, of_lowerE]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [SetLike.mem_coe, of_lowerE]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  exact h2 (by rw [h1]; exact Subgroup.mem_top y)

theorem alphaA_pow_self : alphaA m ^ m = 1 := by
  rw [← of_lowerE_natCast, ZMod.natCast_self, lowerE_zero, map_one]

theorem of_lowerE_neg_one : Abelianization.of (lowerE m (-1)) = (alphaA m)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, alphaA, ← map_mul, lowerE_mul, neg_add_cancel, lowerE_zero, map_one]

theorem of_rotB : Abelianization.of (rotB m) = (alphaA m)⁻¹ ^ 3 := by
  have hupper : Abelianization.of (upperE m 1) = (alphaA m)⁻¹ := by
    rw [of_upperE, of_lowerE_neg_one]
  rw [rotB, map_mul, map_mul, hupper, of_lowerE_neg_one]; group

theorem alphaA_pow_twelve : alphaA m ^ 12 = 1 := by
  have h := congrArg Abelianization.of (rotB_pow_four (m := m))
  rw [map_pow, map_one, of_rotB, ← pow_mul] at h
  rw [show (3 * 4 : ℕ) = 12 from rfl] at h
  rwa [inv_pow, inv_eq_one] at h

theorem orderOf_alphaA_dvd_self : orderOf (alphaA m) ∣ m :=
  orderOf_dvd_of_pow_eq_one alphaA_pow_self

theorem orderOf_alphaA_dvd_twelve : orderOf (alphaA m) ∣ 12 :=
  orderOf_dvd_of_pow_eq_one alphaA_pow_twelve

end AbelianizationBound

section RowOne
variable {m : ℕ}

theorem alphaA_eq_one_of_coprime (hco : Nat.Coprime m 12) : alphaA m = 1 := by
  have h := Nat.dvd_gcd (orderOf_alphaA_dvd_self (m := m)) (orderOf_alphaA_dvd_twelve (m := m))
  rw [Nat.Coprime] at hco
  rw [hco, Nat.dvd_one, orderOf_eq_one_iff] at h; exact h

theorem subsingleton_abelianization_of_coprime (hm : IsPrimePow m) (hco : Nat.Coprime m 12) :
    Subsingleton (Abelianization (SL(2, ZMod m))) := by
  constructor; intro a b
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_alphaA hm a)
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_alphaA hm b)
  rw [← hj, ← hl, alphaA_eq_one_of_coprime hco, _root_.one_zpow, _root_.one_zpow]

theorem isPerfect_SL2_ZMod_of_coprime (hm : IsPrimePow m) (hco : Nat.Coprime m 12) :
    Group.IsPerfect (SL(2, ZMod m)) := by
  haveI := subsingleton_abelianization_of_coprime hm hco
  constructor
  rw [← Abelianization.ker_of (SL(2, ZMod m))]
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
  exact Subsingleton.elim _ _

theorem not_dvd_twelve_of_five_le {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) : ¬q ∣ 12 := by
  intro hdvd
  have h12 : q ∣ 4 * 3 := by rw [show (4 * 3 : ℕ) = 12 from rfl]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h12 with h | h
  · have h2 : q ∣ 2 :=
      hq.dvd_of_dvd_pow (n := 2) (by rw [show (2 ^ 2 : ℕ) = 4 from rfl]; exact h)
    have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

theorem isPerfect_SL2_ZMod_prime_pow {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) {n : ℕ}
    (hn : n ≠ 0) : Group.IsPerfect (SL(2, ZMod (q ^ n))) := by
  apply isPerfect_SL2_ZMod_of_coprime ⟨q, n, hq.prime, Nat.pos_of_ne_zero hn, rfl⟩
  exact Nat.Coprime.pow_left n
    ((Nat.Prime.coprime_iff_not_dvd hq).mpr (not_dvd_twelve_of_five_le hq h5))

end RowOne

end SolImpl
open scoped _root_.P2MW.S_Ihara_isPerfect_SL2_ZMod_prime_pow.SolImpl

open scoped MatrixGroups in
theorem solution {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) {n : ℕ}
    (hn : n ≠ 0) : Group.IsPerfect (SL(2, ZMod (q ^ n))) :=
  SolImpl.isPerfect_SL2_ZMod_prime_pow hq h5 hn
