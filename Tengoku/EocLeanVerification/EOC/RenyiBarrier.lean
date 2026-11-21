import Tengoku
import Tengoku.EocLeanVerification.EOC.IntervalSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The prefix-sharing (Rényi-2) barrier θ_M

Formal pieces of the barrier for prefix-only / adversarial-continuation arguments:

1. **Geometric Rényi identity.** For the geometric law `P(d) = p q^d` (`q = 1 - p`) the collision
   probability is `∑ (p q^d)^2 = p^2/(1 - q^2)`; with `p = 1/α` its `-log₂` is
   `2 log₂ α + log₂(1 - (1 - 1/α)^2)`
   (= `H_R`, and `θ_M = H_R/α`).
2. **Prefix-sharing collisions.** For a prefix map `pre`, the number of prefix-sharing pairs is
   `∑_c #fibre(c)^2`, and `(#T)^2 ≤ #(image pre) · #{prefix-sharing pairs}`
   (Cauchy–Schwarz / Rényi).
3. **Phase-alignment sharpness.** If continuation sums are only known to satisfy `‖G_S‖ ≤ g_S`,
   the Minkowski/triangle bound `‖∑ F_S G_S‖ ≤ ∑ g_S ‖F_S‖` is attained by unimodular phases
   `G_S = g_S c_S` (for every `λ` separately), so no argument using only `‖G_S‖ ≤ g_S` can beat
   `∑_λ (∑_S g_S ‖F_S(λ)‖)^2`.
4. **Cauchy–Schwarz over λ** for the aligned sum.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

open Finset Complex

namespace EOC
namespace RenyiBarrier

/-! ## 1. Geometric Rényi identity -/

/-- `∑_d (p q^d)^2 = p^2/(1 - q^2)` for the geometric law with `0 < p < 1`, `q = 1 - p`.
@isnad1 id=hassum.2h1v.s7.5c867a7486e0 from=translated src=- shape=cdcc061c vocab=613fcf37
-/
theorem hasSum_geometric_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasSum (fun d : ℕ => (p * (1 - p) ^ d) ^ 2) (p ^ 2 / (1 - (1 - p) ^ 2)) := by
  have hq0 : 0 ≤ (1 - p) ^ 2 := sq_nonneg _
  have hq1 : (1 - p) ^ 2 < 1 := by nlinarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (p ^ 2)
  have hfun : (fun d : ℕ => (p * (1 - p) ^ d) ^ 2) = fun d => p ^ 2 * ((1 - p) ^ 2) ^ d := by
    funext d; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm d 2]
  rw [hfun, div_eq_mul_inv]
  exact h

/--
@isnad1 id=eq.2h1v.s7.5c0d98a1744a from=translated src=- shape=e55b428c vocab=b1a3ae7e
-/
theorem tsum_geometric_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' d : ℕ, (p * (1 - p) ^ d) ^ 2 = p ^ 2 / (1 - (1 - p) ^ 2) :=
  (hasSum_geometric_sq hp0 hp1).tsum_eq

/-- Closed form of the Rényi-2 entropy of the critical geometric law `p = 1/α`:
`-log₂ (p^2/(1-q^2)) = 2 log₂ α + log₂ (1 - (1 - 1/α)^2)`.
@isnad1 id=eq.1h1v.s7.26f48488b9aa from=translated src=- shape=60ca8440 vocab=4e3b4c1a
-/
theorem renyi_closed_form {α : ℝ} (hα : 1 < α) :
    -Real.logb 2 ((1 / α) ^ 2 / (1 - (1 - 1 / α) ^ 2)) =
      2 * Real.logb 2 α + Real.logb 2 (1 - (1 - 1 / α) ^ 2) := by
  have hα0 : 0 < α := by linarith
  have hp0 : 0 < 1 / α := by positivity
  have hp1 : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα
  have hden : 0 < 1 - (1 - 1 / α) ^ 2 := by nlinarith
  rw [Real.logb_div (by positivity) hden.ne', Real.logb_pow, one_div, Real.logb_inv]
  push_cast
  ring

/-- The Rényi-2 entropy of the critical geometric law, as a sum: `H_R = -log₂ ∑_d P(d)^2`.
@isnad1 id=eq.1h1v.s7.6ae42706bb63 from=translated src=- shape=b98de66f vocab=19476372
-/
theorem renyi_of_geometric {α : ℝ} (hα : 1 < α) :
    -Real.logb 2 (∑' d : ℕ, (1 / α * (1 - 1 / α) ^ d) ^ 2) =
      2 * Real.logb 2 α + Real.logb 2 (1 - (1 - 1 / α) ^ 2) := by
  have hα0 : 0 < α := by linarith
  rw [tsum_geometric_sq (by positivity) (by rw [div_lt_one hα0]; exact hα)]
  exact renyi_closed_form hα

/-! ## 2. Prefix-sharing collisions -/

variable {ι κ : Type*} [DecidableEq κ]

/-- The prefix-sharing pairs of `T` under `pre`.-/
def sharePairs (T : Finset ι) (pre : ι → κ) : Finset (ι × ι) :=
  (T ×ˢ T).filter fun x => pre x.1 = pre x.2

/-- The fibre of `pre` over `c` inside `T`.-/
def fibre (T : Finset ι) (pre : ι → κ) (c : κ) : Finset ι := T.filter fun P => pre P = c

/-- **Exact collision identity**: `#{(P,Q) : pre P = pre Q} = ∑_c #fibre(c)^2`.
@isnad1 id=eq.0h4v.s6.b596d42c6d09 from=translated src=- shape=9db6d7ea vocab=b8baba61
-/
theorem card_sharePairs (T : Finset ι) (pre : ι → κ) :
    (sharePairs T pre).card = ∑ c ∈ T.image pre, (fibre T pre c).card ^ 2 := by
  rw [card_eq_sum_card_fiberwise (f := fun x : ι × ι => pre x.1) (t := T.image pre)]
  · refine sum_congr rfl fun c _ => ?_
    have : (sharePairs T pre).filter (fun x => pre x.1 = c) = fibre T pre c ×ˢ fibre T pre c := by
      ext ⟨P, Q⟩
      simp only [sharePairs, fibre, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨hP, hQ⟩, h⟩, hc⟩; exact ⟨⟨hP, hc⟩, hQ, h ▸ hc⟩
      · rintro ⟨⟨hP, hc⟩, hQ, hc'⟩; exact ⟨⟨⟨hP, hQ⟩, hc.trans hc'.symm⟩, hc⟩
    rw [this, card_product, sq]
  · intro x hx
    have hx' := (mem_filter.mp hx).1
    exact mem_image_of_mem pre (mem_product.mp hx').1

/-- Sum of fibre sizes is `#T`.
@isnad1 id=eq.0h4v.s5.e5f99750a1f1 from=translated src=- shape=cac35eac vocab=6ee3678d
-/
theorem sum_card_fibre (T : Finset ι) (pre : ι → κ) :
    ∑ c ∈ T.image pre, (fibre T pre c).card = T.card :=
  (card_eq_sum_card_fiberwise (f := pre) (fun _ hx => mem_image_of_mem pre hx)).symm

/-- **Rényi / Cauchy–Schwarz lower bound**: `(#T)^2 ≤ #(image pre) · #{prefix-sharing pairs}`.
With `≈ 2^{hN}` prefixes of length `N` this gives the prefix-sharing density; with the actual
(non-uniform) fibre sizes the exact count is `∑_c #fibre(c)^2` (`card_sharePairs`).
@isnad1 id=le.0h4v.s5.57555e992010 from=translated src=- shape=f6e8caed vocab=0a3f19cb
-/
theorem sq_card_le_image_mul_sharePairs (T : Finset ι) (pre : ι → κ) :
    T.card ^ 2 ≤ (T.image pre).card * (sharePairs T pre).card := by
  rw [card_sharePairs, ← sum_card_fibre T pre]
  exact sq_sum_le_card_mul_sum_sq

/-! ## 3. Phase-alignment sharpness -/

/-- The aligning phase: `conj z / ‖z‖`, or `1` if `z = 0`.-/
noncomputable def alignPhase (z : ℂ) : ℂ := if z = 0 then 1 else (starRingEnd ℂ) z / (‖z‖ : ℂ)

/--
@isnad1 id=eq.0h1v.s3.72c92aaec605 from=translated src=- shape=fcff7bf0 vocab=afb29daa
-/
theorem norm_alignPhase (z : ℂ) : ‖alignPhase z‖ = 1 := by
  unfold alignPhase
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr h)

/--
@isnad1 id=eq.0h1v.s4.91dc9914f3e9 from=translated src=- shape=8192d573 vocab=95c57d8d
-/
theorem mul_alignPhase (z : ℂ) : z * alignPhase z = (‖z‖ : ℂ) := by
  unfold alignPhase
  split_ifs with h
  · simp [h]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring

/-- **Triangle / Minkowski bound**: if `‖G_S‖ ≤ g_S` then `‖∑ F_S G_S‖ ≤ ∑ g_S ‖F_S‖`.
@isnad1 id=le.1h5v.s6.80f037ad0e4e from=translated src=- shape=e2a9dcdc vocab=94175f8e
-/
theorem norm_sum_le_of_bound {σ : Type*} (U : Finset σ) (F G : σ → ℂ) (g : σ → ℝ)
    (hG : ∀ S ∈ U, ‖G S‖ ≤ g S) :
    ‖∑ S ∈ U, F S * G S‖ ≤ ∑ S ∈ U, g S * ‖F S‖ := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun S hS => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hG S hS) (norm_nonneg _)

/-- **Alignment attains the bound** (one frequency): with `G_S = g_S · c_S`, `c_S` unimodular,
`‖∑ F_S G_S‖ = ∑ g_S ‖F_S‖`.
@isnad1 id=ex.1h4v.s6.f66144e7ffdb from=translated src=- shape=65ff3e5f vocab=1ad44d2d
-/
theorem aligned_attains_one {σ : Type*} (U : Finset σ) (F : σ → ℂ) (g : σ → ℝ)
    (hg : ∀ S ∈ U, 0 ≤ g S) :
    ∃ c : σ → ℂ, (∀ S, ‖c S‖ = 1) ∧
      ‖∑ S ∈ U, F S * ((g S : ℂ) * c S)‖ = ∑ S ∈ U, g S * ‖F S‖ := by
  refine ⟨fun S => alignPhase (F S), fun S => norm_alignPhase _, ?_⟩
  have hsum : ∑ S ∈ U, F S * ((g S : ℂ) * alignPhase (F S)) = ((∑ S ∈ U, g S * ‖F S‖ : ℝ) : ℂ) := by
    push_cast
    refine sum_congr rfl fun S _ => ?_
    rw [mul_left_comm, mul_alignPhase]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg fun S hS => mul_nonneg (hg S hS) (norm_nonneg _))]

/-- **`aligned_attains`** (all frequencies): for every frequency family `F λ S` and sizes `g_S ≥ 0`
there are unimodular phases `c λ S` such that the continuations `G λ S = g_S c λ S`
(which satisfy `‖G λ S‖ = g_S`) realize
`∑_λ ‖∑_S F λ S · G λ S‖^2 = ∑_λ (∑_S g_S ‖F λ S‖)^2`.
Hence no bound that uses only `‖G_S‖ ≤ g_S` can improve on `∑_λ (∑_S g_S ‖F_S(λ)‖)^2`.
@isnad1 id=ex.1h6v.s7.d5405d742bbc from=translated src=- shape=0a30f49c vocab=19cfcf05
-/
theorem aligned_attains {σ τ : Type*} (I : Finset τ) (U : Finset σ) (F : τ → σ → ℂ) (g : σ → ℝ)
    (hg : ∀ S ∈ U, 0 ≤ g S) :
    ∃ c : τ → σ → ℂ, (∀ l S, ‖c l S‖ = 1) ∧
      ∑ l ∈ I, ‖∑ S ∈ U, F l S * ((g S : ℂ) * c l S)‖ ^ 2 =
        ∑ l ∈ I, (∑ S ∈ U, g S * ‖F l S‖) ^ 2 := by
  refine ⟨fun l S => alignPhase (F l S), fun l S => norm_alignPhase _, ?_⟩
  refine sum_congr rfl fun l _ => ?_
  have hsum : ∑ S ∈ U, F l S * ((g S : ℂ) * alignPhase (F l S)) =
      ((∑ S ∈ U, g S * ‖F l S‖ : ℝ) : ℂ) := by
    push_cast
    refine sum_congr rfl fun S _ => ?_
    rw [mul_left_comm, mul_alignPhase]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg fun S hS => mul_nonneg (hg S hS) (norm_nonneg _))]

/-- **Sharpness of the Minkowski form**: the supremum over all admissible continuations
(`‖G λ S‖ ≤ g_S`) of `∑_λ ‖∑_S F G‖^2` equals `∑_λ (∑_S g_S ‖F λ S‖)^2`: the upper bound holds
for every admissible `G`, and `aligned_attains` realizes it.
@isnad1 id=le.1h7v.s7.c4d7285256ae from=translated src=- shape=7090822c vocab=dfe3821b
-/
theorem sum_sq_le_aligned {σ τ : Type*} (I : Finset τ) (U : Finset σ) (F G : τ → σ → ℂ)
    (g : σ → ℝ) (hG : ∀ l ∈ I, ∀ S ∈ U, ‖G l S‖ ≤ g S) :
    ∑ l ∈ I, ‖∑ S ∈ U, F l S * G l S‖ ^ 2 ≤ ∑ l ∈ I, (∑ S ∈ U, g S * ‖F l S‖) ^ 2 :=
  sum_le_sum fun l hl => pow_le_pow_left₀ (norm_nonneg _)
    (norm_sum_le_of_bound U (F l) (G l) g (hG l hl)) 2

/-! ## 4. Cauchy–Schwarz over λ for the aligned sum -/

/-- `(∑_λ ∑_S g_S ‖F λ S‖)^2 ≤ #I · ∑_λ (∑_S g_S ‖F λ S‖)^2`: under alignment the shell energy is at
least `(1/#I)(∑_λ ∑_S g_S ‖F λ S‖)^2`.
@isnad1 id=le.0h6v.s7.211fa52ba226 from=translated src=- shape=f7d3afe8 vocab=2d6580db
-/
theorem aligned_lower_bound {σ τ : Type*} (I : Finset τ) (U : Finset σ) (F : τ → σ → ℂ)
    (g : σ → ℝ) :
    (∑ l ∈ I, ∑ S ∈ U, g S * ‖F l S‖) ^ 2 ≤ I.card * ∑ l ∈ I, (∑ S ∈ U, g S * ‖F l S‖) ^ 2 :=
  sq_sum_le_card_mul_sum_sq

/-- Combined barrier: there are admissible continuations (`‖G λ S‖ = g_S`) for which the shell
energy is at least `(1/#I)(∑_λ ∑_S g_S ‖F λ S‖)^2`.
@isnad1 id=ex.1h6v.s7.fbf7c1a35625 from=translated src=- shape=32bd3e0c vocab=3039e82e
-/
theorem barrier {σ τ : Type*} (I : Finset τ) (U : Finset σ) (F : τ → σ → ℂ) (g : σ → ℝ)
    (hg : ∀ S ∈ U, 0 ≤ g S) :
    ∃ c : τ → σ → ℂ, (∀ l S, ‖c l S‖ = 1) ∧
      (∑ l ∈ I, ∑ S ∈ U, g S * ‖F l S‖) ^ 2 ≤
        I.card * ∑ l ∈ I, ‖∑ S ∈ U, F l S * ((g S : ℂ) * c l S)‖ ^ 2 := by
  obtain ⟨c, hc, heq⟩ := aligned_attains I U F g hg
  exact ⟨c, hc, heq ▸ aligned_lower_bound I U F g⟩

end RenyiBarrier
end EOC
