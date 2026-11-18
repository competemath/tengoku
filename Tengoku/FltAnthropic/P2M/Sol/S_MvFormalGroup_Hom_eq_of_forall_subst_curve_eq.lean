import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq

set_option autoImplicit false

universe u

namespace HomExtSol

open MvPowerSeries Finsupp

variable {R : Type u} [CommRing R] {d : ℕ}

def deg (β : Fin d →₀ ℕ) : ℕ := ∑ j, β j
def wt (K : ℕ) (β : Fin d →₀ ℕ) : ℕ := ∑ j, β j * K ^ (j : ℕ)

/--
@isnad1 id=le.0h3v.s5.62daae61ef38 from=translated src=- shape=1fd2705e vocab=cdd0dc98
-/
theorem le_deg (β : Fin d →₀ ℕ) (j : Fin d) : β j ≤ deg β :=
  Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem eq_of_wt_eq {K : ℕ} {α β : Fin d →₀ ℕ} (hα : ∀ j, α j < K) (hβ : ∀ j, β j < K)
    (h : wt K α = wt K β) : α = β := by
  have hinj := (finFunctionFinEquiv (m := K) (n := d)).injective
  have e : finFunctionFinEquiv (fun j => (⟨α j, hα j⟩ : Fin K)) = finFunctionFinEquiv (fun j => (⟨β j, hβ j⟩ : Fin K)) := by
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    exact h
  have := hinj e
  ext j
  have := congrFun this j
  simpa using this

/--
@isnad1 id=lt.1h3v.s5.156fee5ae3eb from=translated src=- shape=22af9382 vocab=5dd8f732
-/
theorem wt_lt_pow {K : ℕ} {α : Fin d →₀ ℕ} (hK : deg α < K) : wt K α < K ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [wt]
  · calc wt K α ≤ ∑ j, α j * K ^ (d - 1) := by
          unfold wt
          refine Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ ?_
          exact Nat.pow_le_pow_right (by omega) (by omega)
      _ = deg α * K ^ (d - 1) := by rw [deg, Finset.sum_mul]
      _ < K * K ^ (d - 1) := Nat.mul_lt_mul_of_lt_of_le hK le_rfl (Nat.pow_pos (by omega))
      _ = K ^ d := by rw [← pow_succ']; congr 1; omega

/--
@isnad1 id=eq.0h3v.s7.bf0f7f03c7a4 from=translated src=- shape=907d0e8a vocab=bd27cc0e
-/
theorem weight_eq (K : ℕ) (β : Fin d →₀ ℕ) :
    (∑ j : Fin d, (K ^ d + K ^ (j : ℕ)) * β j) = K ^ d * deg β + wt K β := by
  simp only [add_mul, Finset.sum_add_distrib, deg, wt, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_zero_of_forall_subst_X_pow (D : MvPowerSeries (Fin d) R)
    (h : ∀ n : Fin d → ℕ, (∀ j, 0 < n j) →
      subst (fun j => (X () : MvPowerSeries Unit R) ^ (n j)) D = 0) : D = 0 := by
  classical
  by_contra hD

  have hex : ∃ m, ∃ β : Fin d →₀ ℕ, coeff β D ≠ 0 ∧ deg β = m := by
    obtain ⟨β, hβ⟩ : ∃ β, coeff β D ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hD (MvPowerSeries.ext fun β => by rw [hall β, map_zero])
    exact ⟨_, β, hβ, rfl⟩
  let m := Nat.find hex
  obtain ⟨α, hα, hαm⟩ := Nat.find_spec hex
  have hmin : ∀ β : Fin d →₀ ℕ, coeff β D ≠ 0 → m ≤ deg β := fun β hβ =>
    Nat.find_min' hex ⟨β, hβ, rfl⟩

  set K := m + 1 with hK
  let n : Fin d → ℕ := fun j => K ^ d + K ^ (j : ℕ)
  have hn : ∀ j, 0 < n j := fun j => Nat.add_pos_left (Nat.pow_pos (by omega)) _
  have hγ : HasSubst (fun j => (X () : MvPowerSeries Unit R) ^ (n j)) :=
    hasSubst_of_constantCoeff_zero fun j => by
      rw [map_pow, constantCoeff_X, zero_pow (hn j).ne']

  set M : ℕ := K ^ d * m + wt K α with hM
  have key : ∀ β : Fin d →₀ ℕ, coeff β D ≠ 0 → (∑ j : Fin d, (K ^ d + K ^ (j : ℕ)) * β j) = M → β = α := by
    intro β hβ hw
    rw [weight_eq] at hw
    have hdeg : deg β = m := by
      have h1 := hmin β hβ
      by_contra hne
      have h2 : m + 1 ≤ deg β := by omega
      have : K ^ d * (m + 1) ≤ K ^ d * deg β := Nat.mul_le_mul_left _ h2
      have hlt := wt_lt_pow (K := K) (α := α) (by rw [hαm]; omega)
      rw [mul_add, mul_one] at this
      omega
    rw [hdeg] at hw
    have hwt : wt K β = wt K α := by omega
    exact eq_of_wt_eq (fun j => by have := le_deg β j; omega) (fun j => by have := le_deg α j; omega) hwt
  have hcoeff : coeff (single () M) (subst (fun j => (X () : MvPowerSeries Unit R) ^ (n j)) D) = coeff α D := by
    rw [coeff_subst hγ]
    have hterm : ∀ β : Fin d →₀ ℕ,
        coeff β D • coeff (single () M) (β.prod fun j e => ((X () : MvPowerSeries Unit R) ^ n j) ^ e) =
          if β = α then coeff α D else 0 := by
      intro β
      rw [Finsupp.prod_pow]
      simp_rw [← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum, coeff_X_pow]
      by_cases hβ : coeff β D = 0
      · by_cases hβα : β = α
        · subst hβα; simp [hβ]
        · simp [hβ, hβα]
      · by_cases hw : (∑ j, n j * β j) = M
        · have := key β hβ hw
          subst this
          simp [hw]
        · have hne : β ≠ α := by
            rintro rfl
            apply hw
            rw [weight_eq, hαm]
          rw [ite_eq_right, ite_eq_right hne, smul_zero]
          intro hs
          exact hw ((Finsupp.single_injective ()) hs).symm
    simp_rw [hterm]
    rw [finsum_eq_single _ α (fun β hβ => ite_eq_right hβ), ite_eq_left rfl]
  rw [h n hn, map_zero] at hcoeff
  exact hα hcoeff.symm

end HomExtSol

open HomExtSol in
/--
@isnad1 id=eq.1h7v.s7.eed82c32b085 from=translated src=- shape=d7f5042d vocab=52e42105
-/
theorem solution
    {R : Type u} [CommRing R] {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R)
    (φ ψ : Φ.Hom Φ')
    (h : ∀ γ : Fin d → PowerSeries R, (∀ j, PowerSeries.constantCoeff (γ j) = 0) →
      ∀ k, MvPowerSeries.subst γ (φ.toPowerSeries k) = MvPowerSeries.subst γ (ψ.toPowerSeries k)) :
    φ = ψ := by
  ext k : 2

  have hD : φ.toPowerSeries k - ψ.toPowerSeries k = 0 := by
    refine eq_zero_of_forall_subst_X_pow _ fun n hn => ?_
    have hγ : MvPowerSeries.HasSubst (fun j => (MvPowerSeries.X () : MvPowerSeries Unit R) ^ (n j)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by
        rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (hn j).ne']
    have := h (fun j => (PowerSeries.X : PowerSeries R) ^ (n j)) (fun j => by
      rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (hn j).ne']) k
    rw [← MvPowerSeries.coe_substAlgHom hγ, map_sub, sub_eq_zero, MvPowerSeries.coe_substAlgHom hγ]
    exact this
  exact sub_eq_zero.mp hD
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
