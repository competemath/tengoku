import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Algebra.BigOperators.Intervals
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero.lean`: wrote out 9 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 7 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve
export _root_.ModularCurve (qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeff_jq_neg_one coeff_jq_of_lt qTwist qTwist_coeff coeffEmb coeffEmb_coeff)
open _root_.ModularCurve
namespace PhiGen
export _root_.ModularCurve.PhiGen (conj conj_zero conj_succ phiProd TPoleOrderLE JSimplePole)
open _root_.ModularCurve.PhiGen

section CoeffEmbJq

variable (K : Type*) [Field K] [Algebra ℚ K]

private theorem coeff_coeffEmb_jq_of_lt {k : ℤ} (hk : k < -1) : (coeffEmb K jq).coeff k = 0 := by
  rw [coeffEmb_coeff, coeff_jq_of_lt hk, map_zero]

end CoeffEmbJq

namespace TPoleOrderLE
private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.mono {K : Type*} [Field K] {f : LaurentSeries K} {m n : ℕ}
    (hf : TPoleOrderLE f m) (hmn : m ≤ n) : TPoleOrderLE f n :=
  fun k hk => hf k (by omega)

end TPoleOrderLE
export _root_.ModularCurve.PhiGen (TPoleOrderLE.mono)
private theorem tPoleOrderLE_zero {K : Type*} [Field K] (n : ℕ) :
    TPoleOrderLE (0 : LaurentSeries K) n :=
  fun _ _ => rfl

private theorem tPoleOrderLE_one {K : Type*} [Field K] :
    TPoleOrderLE (1 : LaurentSeries K) 0 := by
  intro m hm
  rw [HahnSeries.coeff_one, ite_eq_right (by omega)]

namespace TPoleOrderLE
private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.neg {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) : TPoleOrderLE (-f) n := by
  intro m hm
  rw [HahnSeries.coeff_neg, hf m hm, neg_zero]

end TPoleOrderLE
export _root_.ModularCurve.PhiGen (TPoleOrderLE.neg)
private theorem TPoleOrderLE.add {K : Type*} [Field K] {f g : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) (hg : TPoleOrderLE g n) : TPoleOrderLE (f + g) n := by
  intro m hm
  rw [HahnSeries.coeff_add, hf m hm, hg m hm, add_zero]

namespace TPoleOrderLE
private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.mul {K : Type*} [Field K] {f g : LaurentSeries K} {m n : ℕ}
    (hf : TPoleOrderLE f m) (hg : TPoleOrderLE g n) : TPoleOrderLE (f * g) (m + n) := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 < -(m : ℤ)
  · rw [hf ij.1 hi, zero_mul]
  · refine mul_eq_zero_of_right _ (hg ij.2 ?_)
    push_cast at hk
    omega

end TPoleOrderLE
export _root_.ModularCurve.PhiGen (TPoleOrderLE.mul)
namespace TPoleOrderLE
private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.qTwist {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) (u : Kˣ) : TPoleOrderLE (ModularCurve.qTwist u f) n := by
  intro m hm
  rw [qTwist_coeff, hf m hm, mul_zero]

end TPoleOrderLE
export _root_.ModularCurve.PhiGen (TPoleOrderLE.qTwist)
namespace TPoleOrderLE
private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.qExpand {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) (N : ℕ) [NeZero N] :
    TPoleOrderLE (ModularCurve.qExpand K N f) (N * n) := by
  intro m hm
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    refine hf c ?_
    have hN : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    push_cast at hm
    nlinarith
  · exact qExpand_coeff_of_not_dvd N f hdvd

end TPoleOrderLE
export _root_.ModularCurve.PhiGen (TPoleOrderLE.qExpand)
private theorem tPoleOrderLE_of_jSimplePole {K : Type*} [Field K] (J : LaurentSeries K)
    (hJ : JSimplePole J) : TPoleOrderLE J 1 := by
  intro m hm
  exact hJ m (by push_cast at hm; omega)

private def conjPoleBound (ℓ : ℕ) : Fin (ℓ + 1) → ℕ :=
  fun i => if i = 0 then ℓ * ℓ else 1

private theorem tPoleOrderLE_conj_zero {K : Type*} [Field K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {J : LaurentSeries K}
    {conj : Fin (ℓ + 1) → LaurentSeries K} (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hJ : JSimplePole J) : TPoleOrderLE (conj 0) (ℓ * ℓ) := by
  rw [hconj0]
  have h := (tPoleOrderLE_of_jSimplePole J hJ).qExpand (ℓ * ℓ)
  simpa using h

private theorem tPoleOrderLE_conj_succ {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : JSimplePole J) (b : Fin ℓ) : TPoleOrderLE (conj b.succ) 1 := by
  rw [hconjS b]
  exact (tPoleOrderLE_of_jSimplePole J hJ).qTwist _

private theorem tPoleOrderLE_coeff_X_sub_C {K : Type*} [Field K] {a : LaurentSeries K}
    {n : ℕ} (ha : TPoleOrderLE a n) (k : ℕ) :
    TPoleOrderLE ((Polynomial.X - Polynomial.C a).coeff k) n := by
  match k with
  | 0 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    exact ha.neg
  | 1 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      ite_eq_right (one_ne_zero), sub_zero]
    exact tPoleOrderLE_one.mono (Nat.zero_le _)
  | (k + 2) =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    exact tPoleOrderLE_zero _

private theorem phiProd_def {K : Type*} [Field K] (ℓ : ℕ)
    (conj : Fin (ℓ + 1) → LaurentSeries K) :
    phiProd ℓ conj = ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i)) := rfl

/--
@isnad1 id=tpoleord.1h5v.s9.2e8ebfabb6a7 from=translated src=- shape=5263d009 vocab=aaae1ce7
-/
theorem tPoleOrderLE_coeff_prod_X_sub_C_card {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (a : ι → LaurentSeries K) (ha : ∀ i ∈ s, TPoleOrderLE (a i) 1) :
    ∀ k : ℕ, TPoleOrderLE ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (s.card - k) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using tPoleOrderLE_one
    · rw [Finset.prod_empty, Polynomial.coeff_one, ite_eq_right (by omega)]
      exact tPoleOrderLE_zero _
  | cons a₀ s ha₀ ih =>
    intro k
    have hmem : ∀ i ∈ s, TPoleOrderLE (a i) 1 :=
      fun i hi => ha i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.card_cons]
    match k with
    | 0 =>

      rw [Polynomial.mul_coeff_zero]
      exact ((tPoleOrderLE_coeff_X_sub_C (ha a₀ (Finset.mem_cons_self a₀ s)) 0).mul
        (ih hmem 0)).mono (by omega)
    | (k + 1) =>

      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
        sub_eq_add_neg]
      refine TPoleOrderLE.add ?_ (TPoleOrderLE.neg ?_)
      ·
        exact (ih hmem k).mono (by omega)
      ·

        by_cases hks : k + 1 ≤ s.card
        · exact ((ha a₀ (Finset.mem_cons_self a₀ s)).mul (ih hmem (k + 1))).mono
            (by omega)
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
          · exact tPoleOrderLE_zero _
          · rw [Polynomial.natDegree_prod_of_monic _ _
              (fun i _ => Polynomial.monic_X_sub_C (a i))]
            simp only [Polynomial.natDegree_X_sub_C, ← Finset.card_eq_sum_ones]
            omega

/--
@isnad1 id=tpoleord.4h6v.s9.6a9810ec9dea from=translated src=- shape=2ccc7d7c vocab=848ecdaa
-/
theorem tPoleOrderLE_phiProd_coeff_of_ne_zero {K : Type*} [Field K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {J : LaurentSeries K}
    {conj : Fin (ℓ + 1) → LaurentSeries K} (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : JSimplePole J) (k : ℕ) (hk : k ≠ 0) :
    TPoleOrderLE ((phiProd ℓ conj).coeff k) (ℓ * ℓ + ℓ - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  have hsq : 4 ≤ ℓ * ℓ := Nat.mul_le_mul hℓ2 hℓ2

  rw [phiProd_def, Fin.prod_univ_succ, sub_mul, Polynomial.coeff_sub,
    Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, sub_eq_add_neg]

  have hR : ∀ j : ℕ, TPoleOrderLE
      ((∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj b.succ))).coeff j)
      (Finset.univ.card - j) :=
    tPoleOrderLE_coeff_prod_X_sub_C_card Finset.univ _
      (fun b _ => tPoleOrderLE_conj_succ hconjS hJ b)
  rw [Finset.card_univ, Fintype.card_fin] at hR
  refine TPoleOrderLE.add ?_ (TPoleOrderLE.neg ?_)
  ·
    exact (hR k).mono (by omega)
  ·
    exact ((tPoleOrderLE_conj_zero hconj0 hJ).mul (hR (k + 1))).mono (by omega)

/--
@isnad1 id=jsimplep.0h1v.s7.014cd2a160d9 from=translated src=- shape=4510e609 vocab=18cd294f
-/
theorem jSimplePole_jqK_carrier {K : Type*} [Field K] [Algebra ℚ K] :
    JSimplePole (coeffEmb K jq) :=
  fun _ hm => coeff_coeffEmb_jq_of_lt K hm

private theorem tPoleOrderLE_phiProd_conj_of_ne_zero {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) :
    TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ - 1) :=
  tPoleOrderLE_phiProd_coeff_of_ne_zero (conj_zero ℓ ζ) (conj_succ ℓ ζ)
    (jSimplePole_jqK_carrier (K := K)) k hk

end PhiGen
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero.ModularCurve.PhiGen in

/--
@isnad1 id=tpoleord.1h4v.s6.842079489649 from=translated src=- shape=bce6892d vocab=0ea4e850
-/
theorem solution {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) : TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ - 1) :=
  ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero ℓ ζ k hk

