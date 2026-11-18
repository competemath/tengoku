import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul

set_option autoImplicit false

open Finset

namespace Ws18BDist

def Bt (N t : ℤ) : ℤ := 6 * t ^ 2 - 6 * N * t + N ^ 2

/--
@isnad1 id=eq.0h4v.s8.a67b63e333eb from=translated src=- shape=16cb167f vocab=14fd3ef3
-/
theorem sum_range_Bt_aux (N p₀ g : ℤ) (M : ℕ) :
    ∑ j ∈ range M, Bt N (p₀ + g * j) =
      M * (6 * p₀ ^ 2 - 6 * N * p₀ + N ^ 2) + (6 * p₀ * g - 3 * N * g) * (M * (M - 1)) +
        g ^ 2 * ((M - 1) * M * (2 * M - 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [sum_range_succ, ih, Bt]
      push_cast
      ring

/--
@isnad1 id=eq.0h3v.s7.8723322940ac from=translated src=- shape=2fcca40e vocab=14fd3ef3
-/
theorem sum_range_Bt (p₀ g : ℤ) (M : ℕ) :
    ∑ j ∈ range M, Bt (g * M) (p₀ + g * j) = M * (6 * p₀ ^ 2 - 6 * g * p₀ + g ^ 2) := by
  rw [sum_range_Bt_aux]
  ring

/--
@isnad1 id=eq.0h3v.s6.8c23dbe2950d from=translated src=- shape=dde25a74 vocab=eeb057bd
-/
theorem sum_zmod_eq_sum_range {β : Type*} [AddCommMonoid β] (N : ℕ) [NeZero N] (Φ : ZMod N → β) :
    ∑ s : ZMod N, Φ s = ∑ i ∈ range N, Φ (i : ZMod N) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))).symm⟩
  rw [← Fin.sum_univ_eq_sum_range (fun i => Φ (i : ZMod (n + 1)))]
  refine Fintype.sum_congr _ _ fun s => ?_
  exact congrArg Φ (ZMod.natCast_zmod_val s).symm

/--
@isnad1 id=eq.1h5v.s5.80de3a2abdaf from=translated src=- shape=47750788 vocab=5c386ba3
-/
theorem periodic_shift {β : Type*} (M : ℕ) (h : ℕ → β) (hper : ∀ n, h (n + M) = h n) (k n : ℕ) :
    h (k * M + n) = h n := by
  induction k with
  | zero => simp
  | succ k ihk => rw [Nat.succ_mul, show k * M + M + n = (k * M + n) + M by ring, hper, ihk]

/--
@isnad1 id=eq.1h4v.s6.3492c76b5b93 from=translated src=- shape=3ff08300 vocab=3329ec0b
-/
theorem sum_range_mul_of_periodic {β : Type*} [AddCommMonoid β] (M g : ℕ) (h : ℕ → β)
    (hper : ∀ n, h (n + M) = h n) : ∑ n ∈ range (g * M), h n = g • ∑ n ∈ range M, h n := by
  induction g with
  | zero => simp
  | succ g ih =>
      rw [Nat.succ_mul, sum_range_add, ih, succ_nsmul]
      congr 1
      exact sum_congr rfl fun n _ => periodic_shift M h hper g n

/--
@isnad1 id=eq.3h4v.s6.b62c0512966d from=translated src=- shape=f01f908b vocab=e8145711
-/
theorem emod_progression (p₀ g k : ℤ) (M : ℕ) (hp₀ : 0 ≤ p₀) (hp₀g : p₀ < g) (hM : 0 < M) :
    (p₀ + g * k) % (g * M) = p₀ + g * (k % M) := by
  have hg : 0 < g := lt_of_le_of_lt hp₀ hp₀g
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hk : k = M * (k / M) + k % M := (Int.mul_ediv_add_emod k M).symm
  have hsplit : p₀ + g * k = (p₀ + g * (k % M)) + (g * M) * (k / M) := by
    conv_lhs => rw [hk]
    ring
  rw [hsplit, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt
  · have := Int.emod_nonneg k (ne_of_gt hM')
    positivity
  · have h1 : k % M ≤ M - 1 := by have := Int.emod_lt_of_pos k hM'; omega
    calc p₀ + g * (k % M) ≤ p₀ + g * (M - 1) := by gcongr
      _ < g + g * (M - 1) := by linarith
      _ = g * M := by ring

/--
@isnad1 id=eq.2h4v.s6.3e86e784e52e from=translated src=- shape=c41d0c87 vocab=e384a49f
-/
theorem sum_range_affine_unit (M : ℕ) (hM : 0 < M) (c u : ℤ) (hu : IsCoprime u M) (φ : ℤ → ℤ) :
    ∑ n ∈ range M, φ ((c + n * u) % M) = ∑ n ∈ range M, φ n := by
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩

  have hL : ∀ n : ℕ, φ ((c + n * u) % M) = (fun σ : ZMod M => φ (σ.val : ℤ)) ((c : ZMod M) + (n : ZMod M) * (u : ZMod M)) := by
    intro n
    simp only
    congr 1
    rw [show ((c : ZMod M) + (n : ZMod M) * (u : ZMod M)) = ((c + n * u : ℤ) : ZMod M) by push_cast; ring,
      ZMod.val_intCast]
  have hR : ∀ n ∈ range M, φ n = (fun σ : ZMod M => φ (σ.val : ℤ)) (n : ZMod M) := by
    intro n hn
    simp only
    rw [ZMod.val_natCast_of_lt (mem_range.mp hn)]

  have hunit : IsUnit (u : ZMod M) := by
    obtain ⟨a, b, hab⟩ := hu
    refine isUnit_iff_exists_inv.mpr ⟨(a : ZMod M), ?_⟩
    have := congrArg (fun z : ℤ => (z : ZMod M)) hab
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero, mul_comm] at this
    exact this
  let e : ZMod M ≃ ZMod M := (hunit.unit.mulRight).trans (Equiv.addLeft (c : ZMod M))
  set ψ : ZMod M → ℤ := fun σ => φ (σ.val : ℤ) with hψ
  calc ∑ n ∈ range M, φ ((c + n * u) % M)
      = ∑ n ∈ range M, ψ ((c : ZMod M) + (n : ZMod M) * (u : ZMod M)) := sum_congr rfl fun n _ => hL n
    _ = ∑ σ : ZMod M, ψ ((c : ZMod M) + σ * (u : ZMod M)) :=
        (sum_zmod_eq_sum_range M (fun σ => ψ ((c : ZMod M) + σ * (u : ZMod M)))).symm
    _ = ∑ σ : ZMod M, ψ σ := Fintype.sum_equiv e _ _ fun σ => by simp [e]
    _ = ∑ n ∈ range M, ψ (n : ZMod M) := sum_zmod_eq_sum_range M ψ
    _ = ∑ n ∈ range M, φ n := sum_congr rfl fun n hn => (hR n hn).symm

/--
@isnad1 id=eq.5h6v.s7.a8a05defb55b from=translated src=- shape=59f0bb33 vocab=0d95b73e
-/
theorem sum_zmod_comp_val_affine (N g M : ℕ) [NeZero N] (hN : N = g * M) (hg : 0 < g) (hM : 0 < M)
    (p r : ℤ) (hgr : (g : ℤ) ∣ r) (hcop : IsCoprime (r / g) (M : ℤ)) (F : ℤ → ℤ) :
    ∑ s : ZMod N, F ((((p : ZMod N) + s * (r : ZMod N)).val : ℤ)) =
      g * ∑ n ∈ range M, F (p % g + g * n) := by
  obtain ⟨r', hr'⟩ := hgr
  have hr'eq : r / g = r' := by rw [hr', Int.mul_ediv_cancel_left _ (by exact_mod_cast hg.ne')]
  rw [hr'eq] at hcop

  rw [sum_zmod_eq_sum_range N]
  set h : ℕ → ℤ := fun n => F ((((p : ZMod N) + (n : ZMod N) * (r : ZMod N)).val : ℤ)) with hh
  have hper : ∀ n : ℕ, h (n + M) = h n := by
    intro n
    simp only [hh]
    congr 3
    push_cast
    have hMr : (M : ZMod N) * (r : ZMod N) = 0 := by
      rw [hr', show ((g * r' : ℤ) : ZMod N) = (g : ZMod N) * (r' : ZMod N) by push_cast; ring, ← mul_assoc,
        show (M : ZMod N) * (g : ZMod N) = ((g * M : ℕ) : ZMod N) by push_cast; ring, ← hN, ZMod.natCast_self,
        zero_mul]
    rw [add_mul, hMr, add_zero]
  rw [show range N = range (g * M) by rw [hN], sum_range_mul_of_periodic M g h hper, nsmul_eq_mul]
  congr 1

  have hp : p = g * (p / g) + p % g := (Int.mul_ediv_add_emod p g).symm
  have hval : ∀ n : ℕ, h n = F (p % g + g * ((p / g + n * r') % M)) := by
    intro n
    simp only [hh]
    rw [show ((p : ZMod N) + (n : ZMod N) * (r : ZMod N)) = ((p + n * r : ℤ) : ZMod N) by push_cast; ring,
      ZMod.val_intCast, hN]
    push_cast
    have : p + n * r = p % g + g * (p / g + n * r') := by rw [hr']; linear_combination hp
    rw [this, emod_progression _ _ _ M (Int.emod_nonneg p (by exact_mod_cast hg.ne'))
      (Int.emod_lt_of_pos p (by exact_mod_cast hg)) hM]
  rw [sum_congr rfl fun n _ => hval n]
  exact sum_range_affine_unit M hM (p / g) r' hcop (fun k => F (p % g + g * k))

/--
@isnad1 id=and.1h2v.s6.3b4fdf285d91 from=translated src=- shape=3b998191 vocab=0ea912d0
-/
theorem gcd_bookkeeping (N : ℕ) (hN : N ≠ 0) (r : ℤ) :
    ((Int.gcd r N : ℤ) ∣ r) ∧ (Int.gcd r N ∣ N) ∧ 0 < Int.gcd r N ∧
      IsCoprime (r / Int.gcd r N) ((N / Int.gcd r N : ℕ) : ℤ) := by
  set g := Int.gcd r N with hgdef
  have h1 : (g : ℤ) ∣ r := Int.gcd_dvd_left _ _
  have h2' : (g : ℤ) ∣ (N : ℤ) := Int.gcd_dvd_right _ _
  have h2 : g ∣ N := by exact_mod_cast h2'
  have hgpos : 0 < g := Int.gcd_pos_iff.mpr (Or.inr (by exact_mod_cast hN))
  refine ⟨h1, h2, hgpos, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hdiv : ((N / g : ℕ) : ℤ) = (N : ℤ) / g := by
    rw [Int.natCast_div]
  rw [hdiv]
  exact Int.gcd_div_gcd_div_gcd hgpos

/--
@isnad1 id=eq.0h3v.s8.2cd3fe1d710c from=translated src=- shape=4858b926 vocab=6947a0be
-/
theorem sum_zmod_Bt (N : ℕ) [NeZero N] (p r : ℤ) :
    ∑ s : ZMod N, Bt N ((((p : ZMod N) + s * (r : ZMod N)).val : ℤ)) =
      N * (6 * (p % Int.gcd r N) ^ 2 - 6 * (Int.gcd r N) * (p % Int.gcd r N) + (Int.gcd r N) ^ 2) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨hgr, hgN, hgpos, hcop⟩ := gcd_bookkeeping N hN r
  set g := Int.gcd r N with hgdef
  obtain ⟨M, hM⟩ := hgN
  have hMpos : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by rw [hM, mul_zero]))
  have hNg : N / g = M := by rw [hM, Nat.mul_div_cancel_left _ hgpos]
  rw [hNg] at hcop
  rw [sum_zmod_comp_val_affine N g M hM hgpos hMpos p r hgr hcop (Bt N)]
  rw [show (N : ℤ) = (g : ℤ) * (M : ℤ) by rw [hM]; push_cast; ring, sum_range_Bt]
  ring

end Ws18BDist

open Ws18BDist in
/--
@isnad1 id=eq.0h3v.s8.510233f96498 from=translated src=- shape=e53561b4 vocab=0fff5314
-/
theorem solution (N : ℕ) [NeZero N] (p r : ℤ) :
    ∑ s : ZMod N,
        (6 * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) ^ 2
          - 6 * (N : ℤ) * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) + (N : ℤ) ^ 2) =
      (N : ℤ) * (6 * (p % (Int.gcd r N : ℤ)) ^ 2
        - 6 * (Int.gcd r N : ℤ) * (p % (Int.gcd r N : ℤ)) + (Int.gcd r N : ℤ) ^ 2) := by
  calc _ = ∑ s : ZMod N, Bt N ((((p : ZMod N) + s * (r : ZMod N)).val : ℤ)) :=
        Finset.sum_congr rfl fun s _ => by simp only [Bt]
    _ = _ := (sum_zmod_Bt N p r).trans (by ring)
