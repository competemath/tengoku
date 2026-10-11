/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Tengoku.LeanPool.LeanPool.Chudnovsky.Basic
import Tengoku.LeanPool.LeanPool.Chudnovsky.Estimates
import Tengoku.LeanPool.LeanPool.Chudnovsky.Kummer
import Tengoku.LeanPool.LeanPool.Chudnovsky.Ramanujan

/-!
# The Main Theorem (Milla, ch. 9)

The paper's ch. 9: the differential-equation form `thm42` and the
**Main Theorem** `hauptformel`,
```
1/(2π·Im τ) · √(J(τ)/(J(τ)−1))
  = ∑ n, ((1−s₂(τ))/6 + n) · (6n)!/((3n)!(n!)³) · (1728·J(τ))⁻ⁿ    (Im τ > 1.25)
```
where `√` is the principal branch (here: `Complex.cpow (1/2)`).

The intermediate propositions `thm35` (quasiperiod/period derivative relation) and
`thmglg10` (`η₁ − (3g₃/2g₂)s₂ = π/Im τ`) are stated in lattice language in the paper;
here the whole ch. 9 computation is carried out in modular language, replacing the
quasiperiod calculus by Ramanujan's derivative identities (`Ramanujan.lean`) applied
to Kummer's identity `E₄ = ₂F₁(1/12,5/12;1;1/J)⁴` (`Kummer.lean`): see the section
"The proof of `thm42`" below.

The branch of the square root is resolved *pointwise* in `thm42`:
`J/(J−1) = (G⁶/E₆)²` with `Re(G⁶/E₆) > 0` everywhere on `Region` (by explicit
estimates), and the principal square root of `w²` is `w` on the right half-plane
(`Complex.sq_cpow_two_inv`).  The connectedness workhorse `sq_eq_on_preconnected_eq`
originally planned for this step (PLAN A8) is kept for reference/reuse.
-/

@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries Nat

open scoped Real

/-- `Gsq z = (₂F₁(1/12, 5/12; 1; z))²`, the square of Kummer's solution
(the function `G` in the proof of the Main Theorem). -/
def Gsq (z : ℂ) : ℂ := (₂F₁ (1 / 12 : ℂ) (5 / 12) 1 z) ^ 2

/-- The summand of the Main Theorem's series:
`((1−s₂(τ))/6 + n) · (6n)!/((3n)!(n!)³) · (1728·J(τ))⁻ⁿ`. -/
def mainSummand (τ : ℍ) (n : ℕ) : ℂ :=
  ((1 - s₂ τ) / 6 + n) * (((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)) /
    (1728 * J τ) ^ n

/-- The coefficients `(6n)!/((3n)!(n!)³1728ⁿ)` are weakly decreasing, in product form. -/
private theorem factorial_ratio_succ (n : ℕ) :
    (6 * (n + 1))! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)
      ≤ (6 * n)! * ((3 * (n + 1))! * ((n + 1)!) ^ 3 * 1728 ^ (n + 1)) := by
  have e6 : (6 * (n + 1))! =
      ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1))
        * (6 * n)! := by
    rw [Nat.mul_succ]
    simp only [Nat.factorial_succ]
    ring
  have e3 : (3 * (n + 1))! = ((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (3 * n)! := by
    rw [Nat.mul_succ]
    simp only [Nat.factorial_succ]
    ring
  have e1 : ((n + 1)!) ^ 3 = (n + 1) ^ 3 * (n !) ^ 3 := by
    rw [Nat.factorial_succ, mul_pow]
  have hPQ : (6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
      ≤ 1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3) := by
    have key : (6 * n + 1) * (6 * n + 3) * (6 * n + 5) ≤ (6 * n + 6) ^ 3 := by
      rw [pow_succ, pow_two]
      gcongr <;> omega
    calc (6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
        = 24 * (n + 1) * (3 * n + 2) * (3 * n + 1)
            * ((6 * n + 1) * (6 * n + 3) * (6 * n + 5)) := by ring
      _ ≤ 24 * (n + 1) * (3 * n + 2) * (3 * n + 1) * (6 * n + 6) ^ 3 :=
            Nat.mul_le_mul le_rfl key
      _ = 1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3) := by ring
  calc (6 * (n + 1))! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)
      = ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1))
          * ((6 * n)! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)) := by rw [e6]; ring
    _ ≤ (1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3))
          * ((6 * n)! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)) := Nat.mul_le_mul hPQ le_rfl
    _ = (6 * n)! * ((3 * (n + 1))! * ((n + 1)!) ^ 3 * 1728 ^ (n + 1)) := by
        rw [e3, e1, pow_succ]; ring

/-- The factorial quotient `(6n)!/((3n)!(n!)³)` is bounded by `1728ⁿ`. -/
theorem factorial_ratio_le (n : ℕ) :
    (6 * n)! ≤ 1728 ^ n * ((3 * n)! * (n !) ^ 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply (mul_le_mul_iff_of_pos_right
      (by positivity : 0 < (3 * n)! * (n !) ^ 3 * 1728 ^ n)).mp
    calc (6 * (n + 1))! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)
        ≤ (6 * n)! * ((3 * (n + 1))! * ((n + 1)!) ^ 3 * 1728 ^ (n + 1)) :=
          factorial_ratio_succ n
      _ ≤ (1728 ^ n * ((3 * n)! * (n !) ^ 3))
          * ((3 * (n + 1))! * ((n + 1)!) ^ 3 * 1728 ^ (n + 1)) := Nat.mul_le_mul_right _ ih
      _ = (1728 ^ (n + 1) * ((3 * (n + 1))! * ((n + 1)!) ^ 3))
          * ((3 * n)! * (n !) ^ 3 * 1728 ^ n) := by ring

/-- The Main Theorem's series converges absolutely on the region `Im τ > 1.25`
(ratio test: `(6n)!/((3n)!(n!)³) ≤ 1728ⁿ` and `‖1728·J‖ > 1728` on the region). -/
theorem summable_mainSummand {τ : ℍ} (hτ : τ ∈ Region) :
    Summable (mainSummand τ) := by
  set M : ℝ := ‖(1728 : ℂ) * J τ‖ with hMdef
  have hqpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hqb : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hM : (1728 : ℝ) < M := by
    have h1 : (1728 : ℝ) < 0.737 / ‖q τ‖ := by
      rw [lt_div_iff₀ hqpos]; nlinarith [hqb, hqpos]
    exact lt_trans h1 (theonaeherJ_lower hτ)
  have hMpos : 0 < M := lt_trans (by norm_num) hM
  set r : ℝ := 1728 / M with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hMpos]; exact hM
  set C : ℝ := ‖(1 - s₂ τ) / 6‖ with hCdef
  -- The majorant `(C + n)·rⁿ` is summable (geometric ⊕ `n·rⁿ`).
  have hgeom0 : Summable (fun n : ℕ => C * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hgeom1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    simpa using h
  have hg : Summable (fun n : ℕ => (C + n) * r ^ n) := by
    have he : (fun n : ℕ => (C + (n : ℝ)) * r ^ n)
        = fun n : ℕ => C * r ^ n + (n : ℝ) * r ^ n := by ext n; ring
    rw [he]; exact hgeom0.add hgeom1
  refine Summable.of_norm_bounded hg ?_
  intro n
  have hden_pos : (0 : ℝ) < ((3 * n)! : ℝ) * ((n ! : ℝ)) ^ 3 := by positivity
  have hB : ‖((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)‖ ≤ (1728 : ℝ) ^ n := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_natCast, div_le_iff₀ hden_pos]
    calc ((6 * n)! : ℝ) ≤ ((1728 ^ n * ((3 * n)! * (n !) ^ 3) : ℕ) : ℝ) := by
            exact_mod_cast factorial_ratio_le n
      _ = 1728 ^ n * (((3 * n)! : ℝ) * ((n ! : ℝ)) ^ 3) := by push_cast; ring
  have hA : ‖(1 - s₂ τ) / 6 + (n : ℂ)‖ ≤ C + n := by
    calc ‖(1 - s₂ τ) / 6 + (n : ℂ)‖ ≤ ‖(1 - s₂ τ) / 6‖ + ‖(n : ℂ)‖ := norm_add_le _ _
      _ = C + n := by rw [Complex.norm_natCast, hCdef]
  unfold mainSummand
  rw [norm_div, norm_mul, norm_pow, ← hMdef]
  calc ‖(1 - s₂ τ) / 6 + (n : ℂ)‖
        * ‖((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)‖ / M ^ n
      ≤ (C + n) * 1728 ^ n / M ^ n := by gcongr
    _ = (C + n) * r ^ n := by rw [hrdef]; ring

/-- The branch-resolution workhorse (PLAN A8): two continuous functions on a
preconnected set whose squares agree, the second nonvanishing, agreeing at one
point, agree everywhere. -/
theorem sq_eq_on_preconnected_eq {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {f g : X → ℂ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hfg : ∀ x ∈ s, f x ^ 2 = g x ^ 2) (hg0 : ∀ x ∈ s, g x ≠ 0)
    {x₀ : X} (hx₀ : x₀ ∈ s) (h₀ : f x₀ = g x₀) :
    ∀ x ∈ s, f x = g x := by
  have hpc : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hfc : Continuous fun x : s => f x :=
    hf.comp_continuous continuous_subtype_val fun x => x.2
  have hgc : Continuous fun x : s => g x :=
    hg.comp_continuous continuous_subtype_val fun x => x.2
  -- The "equal" set `A` and the "opposite" set `B` inside the subtype `s`.
  set A : Set s := {x | f x = g x} with hA
  set B : Set s := {x | f x = -g x} with hB
  have hBclosed : IsClosed B := by
    have h : IsClosed {x : s | (fun x : s => f x + g x) x = 0} :=
      isClosed_eq (hfc.add hgc) continuous_const
    convert h using 2 with x
    simp [eq_neg_iff_add_eq_zero]
  -- `A ∪ B = univ` since `(f - g)(f + g) = f² - g² = 0`.
  have hcover : A ∪ B = Set.univ := by
    ext x
    simp only [Set.mem_union, hA, hB, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have hprod : (f x - g x) * (f x + g x) = 0 := by
      have h := hfg x x.2; linear_combination h
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  -- `A` and `B` are disjoint: `f x = g x` and `f x = -g x` force `g x = 0`.
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_iff]
    rintro x ⟨hxA, hxB⟩
    simp only [hA, hB, Set.mem_ofPred_eq] at hxA hxB
    exact absurd (by linear_combination (hxB - hxA) / (2 : ℂ)) (hg0 x x.2)
  -- Hence `Aᶜ = B`, so `A` is clopen; being nonempty (`x₀`) it is everything.
  have hAc : Aᶜ = B := by
    ext x
    constructor
    · intro hx
      exact ((hcover ▸ Set.mem_univ x : x ∈ A ∪ B)).resolve_left hx
    · intro hxB hxA
      exact Set.disjoint_iff.mp hdisj ⟨hxA, hxB⟩
  have hAclopen : IsClopen A :=
    ⟨isClosed_eq hfc hgc, isClosed_compl_iff.mp (hAc ▸ hBclosed)⟩
  have hAuniv : A = Set.univ :=
    hAclopen.eq_univ ⟨⟨x₀, hx₀⟩, h₀⟩
  intro x hx
  have : (⟨x, hx⟩ : s) ∈ A := hAuniv ▸ Set.mem_univ _
  simpa [hA] using this

/-- The region `Im τ > 1.25` is preconnected. -/
theorem isPreconnected_Region : IsPreconnected (Region : Set ℍ) := by
  rw [← (UpperHalfPlane.isEmbedding_coe.toIsInducing).isPreconnected_image]
  have himg : ((↑) : ℍ → ℂ) '' Region = {z : ℂ | (5 : ℝ) / 4 < z.im} := by
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      rw [UpperHalfPlane.coe_im]; exact hτ
    · intro hz
      exact ⟨⟨z, lt_trans (by norm_num) hz⟩, hz, rfl⟩
  rw [himg]
  exact (convex_halfSpace_im_gt (5 / 4)).isPreconnected

/-! ### The reduction `hauptformel` ← `thm42`

Milla's derivation of the Main Theorem from `thm42` is the term-by-term differentiation
of the series `darst` (`hyp2F1_sq_eq_tsum`): with `cₙ = (6n)!/((3n)!(n!)³·1728ⁿ)` and
`w = 1/J` (so `‖w‖ < 1` on the region),
`(1−s₂)/6·G(w) + w·G′(w) = ∑ ((1−s₂)/6 + n)·cₙ·wⁿ = ∑ mainSummand`. -/

/-- The coefficient `(6n)!/((3n)!(n!)³·1728ⁿ)` of the power series of `Gsq`. -/
private def mainCoeff (n : ℕ) : ℂ :=
  ((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n !: ℕ) : ℂ) ^ 3 * 1728 ^ n)

/-! ### The proof of `thm42`

Following the modular-forms reformulation of the paper's ch. 9 computation: with
`G = ₂F₁(1/12,5/12;1;1/J)` (so `E₄ = G⁴` by Kummer's Thm. `omegastrich`), Ramanujan's
identity `D E₄ = (E₂E₄−E₆)/3` and the derivative `D J = −J·E₆/E₄` (from `D E₄`, `D E₆`)
combine via the chain rule to `E₂ = E₆/E₄ + 12G³G′E₆/(E₄²J)`.  Substituting this and
`E₄ = G⁴` into the right-hand side of `thm42` collapses it to `G⁶/(2πE₆·Im τ)`; and the
left-hand side equals the same value because `J/(J−1) = E₄³/E₆² = (G⁶/E₆)²` and the
principal square root of `w²` is `w` whenever `Re w > 0` — which holds here by the
explicit estimates `‖G²−1‖ ≤ 0.15` (from the `Gsq` power series, `‖1/J‖ < 1/1.096`)
and `‖E₆−1‖ ≤ 0.199` (from `Estimates.lean`).  This replaces the paper's
continuity/connectedness branch argument by a pointwise right-half-plane one. -/

end Chudnovsky
