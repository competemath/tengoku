import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet
set_option autoImplicit false

namespace ModularCurve
namespace ChainDirichlet

def chainRec (r : ℕ → ℤ) (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => t
  | (d + 2) => 2 * chainRec r t (d + 1) - chainRec r t d - r (d + 1)

/--
@isnad1 id=eq.0h2v.s4.2ed59c612b81 from=translated src=- shape=528031ea vocab=34a4f0ec
-/
theorem chainRec_zero (r : ℕ → ℤ) (t : ℤ) : chainRec r t 0 = 0 := rfl
/--
@isnad1 id=eq.0h2v.s4.40284cbaff67 from=translated src=- shape=4a809523 vocab=34a4f0ec
-/
theorem chainRec_one (r : ℕ → ℤ) (t : ℤ) : chainRec r t 1 = t := rfl
/--
@isnad1 id=eq.0h3v.s6.39f15d87a8c2 from=translated src=- shape=6d6deb1b vocab=a764a009
-/
theorem chainRec_succ_succ (r : ℕ → ℤ) (t : ℤ) (d : ℕ) :
    chainRec r t (d + 2) = 2 * chainRec r t (d + 1) - chainRec r t d - r (d + 1) := rfl

/--
@isnad1 id=eq.1h3v.s6.bee8c76f40b9 from=translated src=- shape=ee0c8fe3 vocab=df05f0ab
-/
theorem chainRec_laplace (r : ℕ → ℤ) (t : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    chainRec r t (d - 1) - 2 * chainRec r t d + chainRec r t (d + 1) = - r d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, show e + 1 + 1 = e + 2 from rfl, chainRec_succ_succ]
  ring

/--
@isnad1 id=eq.0h3v.s5.b6dcf874ffc1 from=translated src=- shape=425a6353 vocab=a7cbedc5
-/
theorem chainRec_eq (r : ℕ → ℤ) (t : ℤ) (d : ℕ) : chainRec r t d = d * t + chainRec r 0 d := by
  induction d using Nat.twoStepInduction with
  | zero => simp [chainRec_zero]
  | one => simp [chainRec_one]
  | more d ih0 ih1 =>
    rw [chainRec_succ_succ, chainRec_succ_succ, ih0, ih1]
    push_cast
    ring

def corr (r : ℕ → ℤ) (ν : ℤ) : ℕ → ℤ := fun d => if d = 1 then r d - ν else r d

/--
@isnad1 id=eq.0h3v.s5.57cb5d66c0f2 from=translated src=- shape=5448c533 vocab=4cb391bd
-/
theorem chainRec_corr (r : ℕ → ℤ) (ν : ℤ) (d : ℕ) :
    chainRec (corr r ν) 0 d = chainRec r 0 d + ((d - 1 : ℕ) : ℤ) * ν := by
  induction d using Nat.twoStepInduction with
  | zero => simp [chainRec_zero]
  | one => simp [chainRec_one]
  | more d ih0 ih1 =>
    rw [chainRec_succ_succ, chainRec_succ_succ, ih0, ih1]
    rcases Nat.eq_zero_or_pos d with rfl | hdp
    · simp [chainRec_zero, chainRec_one, corr]; ring
    · have hc : corr r ν (d + 1) = r (d + 1) := by
        unfold corr; rw [ite_eq_right (by omega)]
      rw [hc]
      have h1 : ((d + 1 - 1 : ℕ) : ℤ) = d := by omega
      have h2 : ((d - 1 : ℕ) : ℤ) = d - 1 := by omega
      have h3 : ((d + 2 - 1 : ℕ) : ℤ) = d + 1 := by omega
      rw [h1, h2, h3]
      ring

/--
@isnad1 id=eq.1h2v.s5.408491fc5120 from=translated src=- shape=48c0db7e vocab=c38440ab
-/
theorem chainRec_corr_self_eq_zero (r : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    chainRec (corr r (chainRec r 0 n)) (-(chainRec r 0 n)) n = 0 := by
  rw [chainRec_eq, chainRec_corr]
  have : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [this]; ring

end ModularCurve.ChainDirichlet

open ModularCurve.ChainDirichlet in

/--
@isnad1 id=ex.1h3v.s7.2527cd17f30c from=translated src=- shape=8b843df6 vocab=65bc3136
-/
theorem solution {ι : Type*} [Finite ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i)
    (r : ι → ℕ → ℤ) :
    ∃ (ν : ι → ℤ) (c : ι → ℕ → ℤ),
      (∀ i, n i = 1 → ν i = 0) ∧ (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = 0) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i →
        c i (d - 1) - 2 * c i d + c i (d + 1) = -(if d = 1 then r i d - ν i else r i d) := by
  classical
  let ν : ι → ℤ := fun i => if n i = 1 then 0 else chainRec (r i) 0 (n i)
  let c : ι → ℕ → ℤ := fun i d => if n i ≤ d then 0 else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d
  refine ⟨ν, c, ?_, ?_, ?_, ?_⟩
  · intro i hi
    show (if n i = 1 then (0 : ℤ) else chainRec (r i) 0 (n i)) = 0
    rw [ite_eq_left hi]
  · intro i
    have : ¬ n i ≤ 0 := by have := hn i; omega
    show (if n i ≤ 0 then (0 : ℤ) else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) 0) = 0
    rw [ite_eq_right this, chainRec_zero]
  · intro i d hd
    show (if n i ≤ d then (0 : ℤ) else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d) = 0
    rw [ite_eq_left hd]
  · intro i d hd1 hd2
    have hni : ¬ n i = 1 := by omega
    have hνi : ν i = chainRec (r i) 0 (n i) := by
      show (if n i = 1 then (0 : ℤ) else chainRec (r i) 0 (n i)) = _
      rw [ite_eq_right hni]
    have hc : ∀ e, c i e = if n i ≤ e then 0 else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) e :=
      fun e => rfl
    have hcorr : corr (r i) (ν i) d = (if d = 1 then r i d - ν i else r i d) := rfl
    have key := chainRec_laplace (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d hd1
    have hend : chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) (n i) = 0 := by
      rw [hνi]; exact chainRec_corr_self_eq_zero (r i) (n i) (hn i)
    rw [hc (d - 1), hc d, hc (d + 1), ite_eq_right (by omega), ite_eq_right (by omega), ← hcorr]
    by_cases h2 : n i ≤ d + 1
    · have heq : d + 1 = n i := by omega
      rw [ite_eq_left h2, ← key, heq, hend]
    · rw [ite_eq_right h2, ← key]
