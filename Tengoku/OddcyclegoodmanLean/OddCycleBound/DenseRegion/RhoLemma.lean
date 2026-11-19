import Tengoku.Seed.Algebra.Ring.GeomSum
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace OddCycleBound.DenseRegion

noncomputable def rho (n m : ℕ) (u : ℝ) : ℝ :=
  (m / n : ℝ) * (u ^ n + (1 - u) ^ n) - u ^ (n - 1)

/--
@isnad1 id=eq.0h3v.s8.3148ca15c2d8 from=translated src=- shape=e983ab88 vocab=01a05bbf
-/
lemma rho_rearrange1 (t m : ℕ) (u : ℝ) :
    rho (2 * t + 1) m u
      = (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) * ((1 - u) ^ (2 * t) - u ^ (2 * t))
        + ((m : ℝ) / (2 * (t : ℝ) + 1) - 1) * u ^ (2 * t) := by
  unfold rho
  rw [show (2 * t + 1) - 1 = 2 * t from by omega]
  push_cast
  rw [pow_succ u (2 * t), pow_succ (1 - u) (2 * t)]
  ring

/--
@isnad1 id=le.2h3v.s6.69b94846977e from=translated src=- shape=aaec747f vocab=da00e0c9
-/
lemma rho_window_left (t m : ℕ) (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ) (hu : u ≤ 1 / 2) :
    0 ≤ rho (2 * t + 1) m u := by
  rw [rho_rearrange1]
  have hc : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hpow : u ^ (2 * t) ≤ (1 - u) ^ (2 * t) :=
    calc u ^ (2 * t) = (u ^ 2) ^ t := by rw [pow_mul]
      _ ≤ ((1 - u) ^ 2) ^ t := pow_le_pow_left₀ (sq_nonneg u) (by nlinarith [hu]) t
      _ = (1 - u) ^ (2 * t) := by rw [pow_mul]
  have hterm1 : 0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) * ((1 - u) ^ (2 * t) - u ^ (2 * t)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hterm2 : 0 ≤ ((m : ℝ) / (2 * (t : ℝ) + 1) - 1) * u ^ (2 * t) :=
    mul_nonneg (by linarith) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) t)
  linarith

/--
@isnad1 id=eq.0h3v.s7.f8efa3888f35 from=translated src=- shape=12dde872 vocab=01a05bbf
-/
lemma rho_rearrange2 (t m : ℕ) (u : ℝ) :
    rho (2 * t + 1) m u
      = (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1)
        + u ^ (2 * t) * ((m : ℝ) / (2 * (t : ℝ) + 1) * u - 1) := by
  unfold rho
  rw [show (2 * t + 1) - 1 = 2 * t from by omega]
  push_cast
  rw [pow_succ u (2 * t)]
  ring

/--
@isnad1 id=le.2h3v.s7.285428f97449 from=translated src=- shape=c8d830ef vocab=ce0edb44
-/
lemma rho_window_right (t m : ℕ) (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ)
    (hu : (2 * (t : ℝ) + 1) ≤ (m : ℝ) * u) : 0 ≤ rho (2 * t + 1) m u := by
  have hn1 : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have hmn : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by rw [le_div_iff₀ hn1]; linarith
  rcases le_total u 1 with hle1 | hge1
  · rw [rho_rearrange2]
    have hB2 : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * u := by
      rw [show (m : ℝ) / (2 * (t : ℝ) + 1) * u = (m : ℝ) * u / (2 * (t : ℝ) + 1) from by ring,
        le_div_iff₀ hn1, one_mul]; linarith
    have hA : 0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1) :=
      mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
    have hB : 0 ≤ u ^ (2 * t) * ((m : ℝ) / (2 * (t : ℝ) + 1) * u - 1) :=
      mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) t) (by linarith)
    linarith
  · have hgeom := geom_sum₂_mul u (u - 1) (2 * t + 1)
    rw [show u - (u - 1) = 1 from by ring, mul_one] at hgeom
    have hterm_nonneg : ∀ i ∈ Finset.range (2 * t + 1),
        (0 : ℝ) ≤ u ^ i * (u - 1) ^ (2 * t + 1 - 1 - i) :=
      fun i _ => mul_nonneg (pow_nonneg (by linarith) i) (pow_nonneg (by linarith) _)
    have hsum_ge : u ^ (2 * t) ≤ ∑ i ∈ Finset.range (2 * t + 1), u ^ i * (u - 1) ^ (2 * t + 1 - 1 - i) := by
      have h2t : 2 * t ∈ Finset.range (2 * t + 1) := Finset.mem_range.2 (by omega)
      have := Finset.single_le_sum hterm_nonneg h2t
      simpa [show 2 * t + 1 - 1 - 2 * t = 0 from by omega] using this
    have hD : u ^ (2 * t) ≤ u ^ (2 * t + 1) - (u - 1) ^ (2 * t + 1) := hgeom ▸ hsum_ge
    have hu2t : (0 : ℝ) ≤ u ^ (2 * t) := by rw [pow_mul]; positivity
    have hDpos : (0 : ℝ) ≤ u ^ (2 * t + 1) - (u - 1) ^ (2 * t + 1) := le_trans hu2t hD
    have h1u : (1 - u) ^ (2 * t + 1) = -((u - 1) ^ (2 * t + 1)) := by
      rw [show (1 : ℝ) - u = -(u - 1) from by ring, Odd.neg_pow ⟨t, by ring⟩]
    unfold rho
    rw [show (2 * t + 1) - 1 = 2 * t from by omega, h1u]
    push_cast
    nlinarith [hmn, hD, mul_nonneg (sub_nonneg.mpr hmn) hDpos]

/--
@isnad1 id=le.1h3v.s6.a7edb4dbb913 from=translated src=- shape=b8c022fc vocab=ce0edb44
-/
lemma rho_empty (t m : ℕ) (hm : 2 * (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ) :
    0 ≤ rho (2 * t + 1) m u := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  rcases le_total u (1 / 2) with hle | hge
  · exact rho_window_left t m (by linarith) u hle
  · refine rho_window_right t m (by linarith) u ?_
    have hmpos : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hprod := mul_le_mul hm hge (by norm_num) hmpos
    linarith

end OddCycleBound.DenseRegion
