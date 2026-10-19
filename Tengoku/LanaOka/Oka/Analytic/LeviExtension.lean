/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytic.LeviHankel
import Tengoku.LanaOka.Oka.Analytic.LeviMoments
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extension of meromorphic functions across sets of codimension two

Let `B` be a finite-dimensional complex normed space, `D ⊆ B` a connected open set and
`S ⊆ B × ℂ`. Let `f` be *meromorphic* on `(D × {‖t‖ ≤ r}) \ S` in the sense that near every point
it is a quotient `u / w` of holomorphic functions with `w` not vanishing on any open set
(`IsLocallyQuotientAt`), and suppose that `f` is holomorphic on `D × {r₁ < ‖t‖ < R}` for some
`r₁ < r < R`, and that the points `b ∈ D` whose closed disc `{b} × {‖t‖ ≤ r}` meets `S` form a
set with empty interior. Then there is a holomorphic function `c` on `D × {‖t‖ < r}`, which does
not vanish on any open set, such that `c * f` extends holomorphically to `D × {‖t‖ < r}`
(`exists_mul_eq_of_prod`). The function `c` is a polynomial in `t` with holomorphic coefficients.

This is the theorem of E. E. Levi on meromorphic extension to Hartogs figures, in the form used by
Grauert and Remmert for the extension across analytic sets of codimension two.

## Proof

The moments `μ k b = ∮_{‖s‖ = r} s ^ k f (b, s) ds` are holomorphic on `D`. For `b` in a dense
open subset of `D` the function `f (b, ·)` is meromorphic on the closed disc of radius `r`, so a
polynomial `p` kills its poles and all moments of `p * f (b, ·)` vanish: the sequence `μ · b`
satisfies a linear recurrence. By Baire's theorem and the identity theorem there is a Hankel minor
of `(μ (i + j))` with columns `0, …, d - 1` not vanishing identically, while all minors of size
`d + 1` with columns `0, …, d` vanish identically (`exists_hankelMinor_ne_zero_forall_eq_zero`).
Expanding the corresponding determinant with last row `(t ^ j)_j` gives
`c (b, t) = ∑ j, c_j (b) t ^ j` such that all moments of `c (b, ·) f (b, ·)` vanish for *every*
`b ∈ D`. Hence the Cauchy integral `F` of `c f` over the circles `‖s‖ = r`, which is holomorphic
on `D × {‖t‖ < r}`, equals `c f` near these circles
(`Laurent.cauchyIntegral_eq_of_forall_moment_eq_zero`), and on the slices on which `f` is
meromorphic the identity theorem gives `F = c f` away from the poles. By density, `F = c f` at
every point outside `S` at which `f` is continuous. The leading coefficient of `c` is the chosen
Hankel minor, so `c` does not vanish identically.

## Main definitions

- `IsLocallyQuotientAt f z`: near `z`, `f` is the quotient of two holomorphic functions whose
  denominator does not vanish on any open set.
- `HasDenominatorAt S f a`: near `a` there is a holomorphic `c`, not vanishing on any open set,
  such that `c * f` extends holomorphically across `S`.

## Main results

- `exists_isOpen_forall_meromorphicAt_slice`: the slices on which `f` is meromorphic contain a
  dense open set.
- `exists_mul_eq_of_prod`: **Levi's extension theorem** in product coordinates.
- `IsLocallyQuotientAt.hasDenominatorAt`, `HasDenominatorAt.of_continuousLinearEquiv`,
  `IsLocallyQuotientAt.comp_continuousLinearEquiv`: basic properties.
- `exists_common_denominator`: a common denominator for finitely many functions.
-/

open Set Filter Metric Complex Polynomial
open scoped Real Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Near `z`, `f` is the quotient `u / w` of two holomorphic functions, where the zero set of `w`
has empty interior. No condition is imposed on the values of `f` at the zeros of `w`. -/
def IsLocallyQuotientAt (f : E → ℂ) (z : E) : Prop :=
  ∃ N ∈ 𝓝 z, ∃ u w : E → ℂ, DifferentiableOn ℂ u N ∧ DifferentiableOn ℂ w N ∧
    interior (N ∩ w ⁻¹' {0}) = ∅ ∧ ∀ y ∈ N, w y ≠ 0 → f y = u y / w y

namespace IsLocallyQuotientAt

variable {f : E → ℂ} {z : E}

/-- A local quotient representation of `f` on a ball. -/
lemma exists_ball (h : IsLocallyQuotientAt f z) :
    ∃ η > 0, ∃ u w : E → ℂ, DifferentiableOn ℂ u (ball z η) ∧
      DifferentiableOn ℂ w (ball z η) ∧ interior (ball z η ∩ w ⁻¹' {0}) = ∅ ∧
      ∀ y ∈ ball z η, w y ≠ 0 → f y = u y / w y := by
  obtain ⟨N, hN, u, w, hu, hw, hw0, hf⟩ := h
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp hN
  exact ⟨η, hη, u, w, hu.mono hsub, hw.mono hsub,
    subset_empty_iff.mp (hw0 ▸ interior_mono (inter_subset_inter_left _ hsub)),
    fun y hy ↦ hf y (hsub hy)⟩

end IsLocallyQuotientAt

/-- Finitely many positive numbers have a common positive lower bound. -/
lemma Finset.exists_pos_forall_le {ι : Type*} (T : Finset ι) {η : ι → ℝ}
    (hη : ∀ i ∈ T, 0 < η i) : ∃ δ > 0, ∀ i ∈ T, δ ≤ η i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a T ha ih =>
    obtain ⟨δ, hδ, hδT⟩ := ih fun i hi ↦ hη i (Finset.mem_insert_of_mem hi)
    refine ⟨min (η a) δ, lt_min (hη a (Finset.mem_insert_self a T)) hδ, fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hδT i hi)

/-- The moments of `(∑ i, a i * s ^ e i) * g s` are the corresponding combinations of the moments
of `g`. -/
lemma circleIntegral_pow_mul_sum_mul {g : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hg : ContinuousOn g (sphere 0 r)) {ι : Type*} (T : Finset ι) (a : ι → ℂ) (e : ι → ℕ)
    (k : ℕ) :
    ∮ s in C(0, r), s ^ k * ((∑ i ∈ T, a i * s ^ e i) * g s) =
      ∑ i ∈ T, a i * ∮ s in C(0, r), s ^ (k + e i) * g s := by
  have h : (fun s ↦ s ^ k * ((∑ i ∈ T, a i * s ^ e i) * g s)) =
      fun s ↦ ∑ i ∈ T, a i * (s ^ (k + e i) * g s) := by
    funext s
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h, circleIntegral.integral_fun_sum (f := fun i s ↦ a i * (s ^ (k + e i) * g s))
    fun i _ ↦ ContinuousOn.circleIntegrable hr
    (continuousOn_const.mul ((continuous_pow _).continuousOn.mul hg))]
  exact Finset.sum_congr rfl fun i _ ↦ circleIntegral.integral_const_mul _ _ _ _

section Prod

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- If `f` is locally a quotient near every point of the closed disc `{b₁} × {‖t‖ ≤ r}`, then
every open neighbourhood of `b₁` contains a nonempty open set of points `b` such that `f (b, ·)`
is meromorphic on the closed disc of radius `r`. -/
theorem exists_isOpen_forall_meromorphicAt_slice_of_forall {f : B × ℂ → ℂ} {r : ℝ} {b₁ : B}
    (hq : ∀ t ∈ closedBall (0 : ℂ) r, IsLocallyQuotientAt f (b₁, t)) {V : Set B}
    (hV : IsOpen V) (hb₁ : b₁ ∈ V) :
    ∃ O, IsOpen O ∧ O.Nonempty ∧ O ⊆ V ∧
      ∀ b ∈ O, ∀ t ∈ closedBall (0 : ℂ) r, MeromorphicAt (fun s ↦ f (b, s)) t := by
  classical
  choose! η hη u w hu hw hw0 hf using fun t (ht : t ∈ closedBall (0 : ℂ) r) ↦
    (hq t ht).exists_ball
  obtain ⟨T, hTr, hcover⟩ := (isCompact_closedBall (0 : ℂ) r).elim_nhds_subcover
    (fun t ↦ ball t (η t / 2)) fun t ht ↦ ball_mem_nhds t (half_pos (hη t ht))
  obtain ⟨δ, hδ, hδT⟩ := T.exists_pos_forall_le (η := fun t ↦ η t / 2)
    fun t ht ↦ half_pos (hη t (hTr t ht))
  -- the product of the small balls lies in the ball on which the representation holds
  have hmem : ∀ t ∈ T, ∀ b ∈ ball b₁ δ, ∀ s ∈ ball t (η t / 2), (b, s) ∈ ball (b₁, t) (η t) :=
    fun t ht b hb s hs ↦ by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨(mem_ball.mp hb).trans_le ((hδT t ht).trans (half_le_self (hη t (hTr t ht)).le)),
        (mem_ball.mp hs).trans (half_lt_self (hη t (hTr t ht)))⟩
  -- the points over which the denominators do not vanish identically on the slices
  have hstep : ∀ t ∈ T, ∀ O : Set B, IsOpen O → O.Nonempty → O ⊆ ball b₁ δ →
      (O ∩ {b | ∃ s ∈ ball t (η t / 2), w t (b, s) ≠ 0}).Nonempty ∧
        IsOpen (O ∩ {b | ∃ s ∈ ball t (η t / 2), w t (b, s) ≠ 0}) := by
    intro t ht O hO hOne hOsub
    refine ⟨?_, ?_⟩
    · by_contra hempty
      rw [not_nonempty_iff_eq_empty] at hempty
      have hsub : O ×ˢ ball t (η t / 2) ⊆ ball (b₁, t) (η t) ∩ w t ⁻¹' {0} := by
        rintro ⟨b, s⟩ ⟨hb, hs⟩
        refine ⟨hmem t ht b (hOsub hb) s hs, ?_⟩
        by_contra hne
        exact (eq_empty_iff_forall_notMem.mp hempty) b ⟨hb, s, hs, hne⟩
      obtain ⟨b, hb⟩ := hOne
      have := interior_maximal hsub (hO.prod isOpen_ball)
        (show (b, t) ∈ O ×ˢ ball t (η t / 2) from ⟨hb, mem_ball_self (half_pos (hη t (hTr t ht)))⟩)
      rw [hw0 t (hTr t ht)] at this
      exact this
    · have : O ∩ {b | ∃ s ∈ ball t (η t / 2), w t (b, s) ≠ 0} =
          ⋃ s ∈ ball t (η t / 2), O ∩ (fun b ↦ w t (b, s)) ⁻¹' {0}ᶜ := by
        ext b
        simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_compl_iff,
          mem_singleton_iff, exists_prop]
        exact ⟨fun ⟨hb, s, hs, h⟩ ↦ ⟨s, hs, hb, h⟩, fun ⟨s, hs, hb, h⟩ ↦ ⟨hb, s, hs, h⟩⟩
      rw [this]
      refine isOpen_biUnion fun s hs ↦ ContinuousOn.isOpen_inter_preimage ?_ hO
        isOpen_compl_singleton
      exact (hw t (hTr t ht)).continuousOn.comp (by fun_prop)
        fun b hb ↦ hmem t ht b (hOsub hb) s hs
  have hind : ∀ T' ⊆ T, ∃ O, IsOpen O ∧ O.Nonempty ∧ O ⊆ V ∩ ball b₁ δ ∧
      ∀ t ∈ T', ∀ b ∈ O, ∃ s ∈ ball t (η t / 2), w t (b, s) ≠ 0 := by
    intro T' hT'
    induction T' using Finset.induction_on with
    | empty => exact ⟨V ∩ ball b₁ δ, hV.inter isOpen_ball, ⟨b₁, hb₁, mem_ball_self hδ⟩,
        subset_rfl, by simp⟩
    | insert a T' ha ih =>
      obtain ⟨O, hO, hOne, hOsub, hOT⟩ := ih ((Finset.subset_insert a T').trans hT')
      obtain ⟨hne, hopen⟩ := hstep a (hT' (Finset.mem_insert_self a T')) O hO hOne
        (hOsub.trans inter_subset_right)
      refine ⟨_, hopen, hne, inter_subset_left.trans hOsub, fun t ht b hb ↦ ?_⟩
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hb.2
      · exact hOT t ht b hb.1
  obtain ⟨O, hO, hOne, hOsub, hOT⟩ := hind T subset_rfl
  refine ⟨O, hO, hOne, hOsub.trans inter_subset_left, fun b hb t' ht' ↦ ?_⟩
  obtain ⟨t, ht, ht't⟩ : ∃ t ∈ T, t' ∈ ball t (η t / 2) := by
    simpa using hcover ht'
  have htr := hTr t ht
  have hbδ := (hOsub hb).2
  -- the slices of the numerator and the denominator are analytic on a disc about `t`
  have hsl : ∀ g : B × ℂ → ℂ, DifferentiableOn ℂ g (ball (b₁, t) (η t)) →
      AnalyticOnNhd ℂ (fun s ↦ g (b, s)) (ball t (η t / 2)) := fun g hg ↦
    (hg.comp (by fun_prop) fun s hs ↦ hmem t ht b hbδ s hs).analyticOnNhd isOpen_ball
  have hwa := hsl (w t) (hw t htr)
  have hne : ∀ᶠ s in 𝓝[≠] t', w t (b, s) ≠ 0 := by
    refine ((hwa t' ht't).eventually_eq_zero_or_eventually_ne_zero).resolve_left fun h0 ↦ ?_
    obtain ⟨s, hs, hws⟩ := hOT t ht b hb
    exact hws (hwa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball t _).isPreconnected ht't h0 hs)
  refine (((hsl (u t) (hu t htr)) t' ht't).meromorphicAt.div (hwa t' ht't).meromorphicAt).congr ?_
  filter_upwards [hne, nhdsWithin_le_nhds (isOpen_ball.mem_nhds ht't)] with s hs hsb
  exact (hf t htr (b, s) (hmem t ht b hbδ s hsb) hs).symm

/-- If the points `b ∈ D` whose closed disc `{b} × {‖t‖ ≤ r}` meets `S` form a set with empty
interior and `f` is locally a quotient outside `S`, then every open set meeting `D` contains a
nonempty open subset of `D` over which the slices of `f` are meromorphic on the closed disc. -/
theorem exists_isOpen_forall_meromorphicAt_slice {D : Set B} (hD : IsOpen D) {S : Set (B × ℂ)}
    {f : B × ℂ → ℂ} {r : ℝ} (hbad : interior {b ∈ D | ∃ t : ℂ, ‖t‖ ≤ r ∧ (b, t) ∈ S} = ∅)
    (hmer : ∀ b ∈ D, ∀ t : ℂ, ‖t‖ ≤ r → (b, t) ∉ S → IsLocallyQuotientAt f (b, t))
    {V : Set B} (hV : IsOpen V) (hVD : (V ∩ D).Nonempty) :
    ∃ O, IsOpen O ∧ O.Nonempty ∧ O ⊆ V ∩ D ∧
      ∀ b ∈ O, ∀ t ∈ closedBall (0 : ℂ) r, MeromorphicAt (fun s ↦ f (b, s)) t := by
  obtain ⟨b₁, hb₁, hb₁S⟩ : ∃ b ∈ V ∩ D, ∀ t : ℂ, ‖t‖ ≤ r → (b, t) ∉ S := by
    by_contra! h
    obtain ⟨b, hb⟩ := hVD
    have hsub : V ∩ D ⊆ {b ∈ D | ∃ t : ℂ, ‖t‖ ≤ r ∧ (b, t) ∈ S} :=
      fun b' hb' ↦ ⟨hb'.2, h b' hb'⟩
    have := interior_maximal hsub (hV.inter hD) hb
    rwa [hbad] at this
  exact exists_isOpen_forall_meromorphicAt_slice_of_forall
    (fun t ht ↦ hmer b₁ hb₁.2 t (mem_closedBall_zero_iff.mp ht) (hb₁S t
      (mem_closedBall_zero_iff.mp ht))) (hV.inter hD) hb₁

variable [FiniteDimensional ℂ B]

/-- **Levi's extension theorem** in product coordinates. Let `D ⊆ B` be open and connected,
`r₁ < r < R`, and `S ⊆ B × ℂ` such that the points `b ∈ D` whose closed disc
`{b} × {‖t‖ ≤ r}` meets `S` form a set with empty interior. Let `f` be locally a quotient of
holomorphic functions at every point of `D × {‖t‖ ≤ r}` outside `S`, and holomorphic on
`D × {r₁ < ‖t‖ < R}`. Then there are holomorphic functions `c` and `F` on `D × {‖t‖ < r}` such
that the zero set of `c` has empty interior and `F = c * f` at every point outside `S` at which
`f` is continuous. -/
theorem exists_mul_eq_of_prod {D : Set B} (hD : IsOpen D) (hDc : IsPreconnected D)
    (hDne : D.Nonempty) {S : Set (B × ℂ)} {f : B × ℂ → ℂ} {r₁ r R : ℝ} (hr : 0 < r)
    (hr₁ : r₁ < r) (hrR : r < R)
    (hbad : interior {b ∈ D | ∃ t : ℂ, ‖t‖ ≤ r ∧ (b, t) ∈ S} = ∅)
    (hmer : ∀ b ∈ D, ∀ t : ℂ, ‖t‖ ≤ r → (b, t) ∉ S → IsLocallyQuotientAt f (b, t))
    (hann : DifferentiableOn ℂ f (D ×ˢ {t : ℂ | r₁ < ‖t‖ ∧ ‖t‖ < R})) :
    ∃ c F : B × ℂ → ℂ, DifferentiableOn ℂ c (D ×ˢ ball 0 r) ∧
      DifferentiableOn ℂ F (D ×ˢ ball 0 r) ∧ interior ((D ×ˢ ball 0 r) ∩ c ⁻¹' {0}) = ∅ ∧
      ∀ z ∈ D ×ˢ ball (0 : ℂ) r, z ∉ S → ContinuousAt f z → F z = c z * f z := by
  classical
  set A : Set ℂ := {t : ℂ | r₁ < ‖t‖ ∧ ‖t‖ < R}
  have hR : 0 < R := hr.trans hrR
  have hAeq : Laurent.annulus r₁ (ENNReal.ofReal R) = A := by
    ext t
    simp only [Laurent.mem_annulus, Laurent.enorm_lt_iff_ofReal_lt,
      ENNReal.ofReal_lt_ofReal_iff hR, A, mem_ofPred_eq]
  have hρ : Laurent.IsRadius r₁ (ENNReal.ofReal R) r :=
    ⟨hr, hr₁, (ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR⟩
  have hsphA : sphere (0 : ℂ) r ⊆ A := fun s hs ↦ by
    rw [mem_sphere_zero_iff_norm] at hs
    exact ⟨hs ▸ hr₁, hs ▸ hrR⟩
  have hslice : ∀ b ∈ D, DifferentiableOn ℂ (fun s ↦ f (b, s)) A := fun b hb ↦
    hann.comp (by fun_prop) fun s hs ↦ ⟨hb, hs⟩
  -- the moments
  set μ : ℕ → B → ℂ := fun k b ↦ ∮ s in C(0, r), s ^ k * f (b, s)
  have hμ : ∀ k, DifferentiableOn ℂ (μ k) D := fun k ↦ by
    refine differentiableOn_circleIntegral hD hr (G := fun b s ↦ s ^ k * f (b, s))
      (fun s hs ↦ ?_) ?_
    · exact (hann.comp (by fun_prop) fun b hb ↦ ⟨hb, hsphA hs⟩).const_mul _
    · exact (continuous_snd.pow k).continuousOn.mul (hann.continuousOn.comp
        (by fun_prop) fun p hp ↦ ⟨(mem_prod.mp hp).1, hsphA (mem_prod.mp hp).2⟩)
  -- the slices over which `f` is meromorphic, and polynomials killing the poles
  set Nice := {b ∈ D | ∀ t ∈ closedBall (0 : ℂ) r, MeromorphicAt (fun s ↦ f (b, s)) t}
  choose! p hpm hpa hpr using fun b (hb : b ∈ Nice) ↦
    exists_monic_analyticOnNhd_eval_mul (isCompact_closedBall (0 : ℂ) r) hb.2
  have hrec : ∀ b ∈ Nice, ∀ k,
      ∑ j ∈ Finset.range ((p b).natDegree + 1), (p b).coeff j * μ (k + j) b = 0 := by
    intro b hb k
    have h0 := circleIntegral_pow_mul_eq_zero hr.le (hpa b hb) k
    simp_rw [eval_eq_sum_range] at h0
    rwa [circleIntegral_pow_mul_sum_mul hr.le ((hslice b hb.1).continuousOn.mono hsphA)] at h0
  obtain ⟨O, hO, hOne, hOD, hOnice⟩ := exists_isOpen_forall_meromorphicAt_slice hD hbad hmer
    isOpen_univ (by simpa using hDne)
  have hOD' : O ⊆ D := fun b hb ↦ (hOD hb).2
  obtain ⟨d, rows, ⟨b₁, hb₁D, hb₁⟩, hJ⟩ := exists_hankelMinor_ne_zero_forall_eq_zero hD hDc hμ
    hO hOD' hOne fun b hb ↦
      ⟨p b, (hpm b ⟨hOD' hb, hOnice b hb⟩).ne_zero, hrec b ⟨hOD' hb, hOnice b hb⟩⟩
  -- the denominator
  set cof : Fin (d + 1) → B → ℂ := fun j ↦ hankelCof μ rows j
  have hcof : ∀ j, DifferentiableOn ℂ (cof j) D := differentiableOn_hankelCof hμ rows
  set c : B × ℂ → ℂ := fun z ↦ ∑ j : Fin (d + 1), cof j z.1 * z.2 ^ (j : ℕ)
  have hc : DifferentiableOn ℂ c (D ×ˢ univ) := DifferentiableOn.fun_sum fun j _ ↦
    ((hcof j).comp differentiableOn_fst fun z hz ↦ hz.1).mul (differentiableOn_snd.pow _)
  have hcs : ∀ b, Differentiable ℂ (fun s ↦ c (b, s)) := fun b ↦ by
    simp only [c]
    fun_prop
  have hmom : ∀ b ∈ D, ∀ k : ℕ, ∮ s in C(0, r), s ^ k * (c (b, s) * f (b, s)) = 0 := by
    intro b hb k
    have hcb : ∀ s, c (b, s) = ∑ j : Fin (d + 1), cof j b * s ^ (j : ℕ) := fun s ↦ rfl
    simp_rw [hcb]
    rw [circleIntegral_pow_mul_sum_mul hr.le ((hslice b hb).continuousOn.mono hsphA)]
    have h := hJ (Fin.snoc rows k) b hb
    rw [← sum_hankelCof_mul] at h
    exact h
  -- the Cauchy integral of `c * f`
  set F : B × ℂ → ℂ := fun z ↦
    (2 * π * I)⁻¹ * ∮ s in C(0, r), (s - z.2)⁻¹ * (c (z.1, s) * f (z.1, s))
  have hsub : ∀ z ∈ D ×ˢ ball (0 : ℂ) r, ∀ s ∈ sphere (0 : ℂ) r, s - z.2 ≠ 0 :=
    fun z hz s hs ↦ sub_ne_zero.mpr fun h ↦ by
      have h1 := mem_ball_zero_iff.mp (mem_prod.mp hz).2
      rw [mem_sphere_zero_iff_norm, h] at hs
      linarith
  have hF : DifferentiableOn ℂ F (D ×ˢ ball 0 r) := by
    have hG₁ : ∀ s ∈ sphere (0 : ℂ) r,
        DifferentiableOn ℂ (fun z : B × ℂ ↦ (s - z.2)⁻¹) (D ×ˢ ball 0 r) := fun s hs ↦
      DifferentiableOn.inv (by fun_prop) fun z hz ↦ hsub z hz s hs
    have hG₂ : ∀ s ∈ sphere (0 : ℂ) r,
        DifferentiableOn ℂ (fun z : B × ℂ ↦ c (z.1, s)) (D ×ˢ ball 0 r) := fun s _ ↦
      hc.comp (f := fun z : B × ℂ ↦ (z.1, s)) (by fun_prop) fun z hz ↦
        ⟨(mem_prod.mp hz).1, mem_univ _⟩
    have hG₃ : ∀ s ∈ sphere (0 : ℂ) r,
        DifferentiableOn ℂ (fun z : B × ℂ ↦ f (z.1, s)) (D ×ˢ ball 0 r) := fun s hs ↦
      hann.comp (f := fun z : B × ℂ ↦ (z.1, s)) (by fun_prop) fun z hz ↦
        ⟨(mem_prod.mp hz).1, hsphA hs⟩
    have hK₁ : ContinuousOn (fun q : (B × ℂ) × ℂ ↦ (q.2 - q.1.2)⁻¹)
        ((D ×ˢ ball 0 r) ×ˢ sphere 0 r) :=
      ContinuousOn.inv₀ (by fun_prop) fun q hq ↦
        hsub q.1 (mem_prod.mp hq).1 q.2 (mem_prod.mp hq).2
    have hK₂ : ContinuousOn (fun q : (B × ℂ) × ℂ ↦ c (q.1.1, q.2))
        ((D ×ˢ ball 0 r) ×ˢ sphere 0 r) :=
      hc.continuousOn.comp (f := fun q : (B × ℂ) × ℂ ↦ (q.1.1, q.2)) (by fun_prop)
        fun q hq ↦ ⟨(mem_prod.mp (mem_prod.mp hq).1).1, mem_univ _⟩
    have hK₃ : ContinuousOn (fun q : (B × ℂ) × ℂ ↦ f (q.1.1, q.2))
        ((D ×ˢ ball 0 r) ×ˢ sphere 0 r) :=
      hann.continuousOn.comp (f := fun q : (B × ℂ) × ℂ ↦ (q.1.1, q.2)) (by fun_prop)
        fun q hq ↦ ⟨(mem_prod.mp (mem_prod.mp hq).1).1, hsphA (mem_prod.mp hq).2⟩
    have hK : ContinuousOn (Function.uncurry fun (z : B × ℂ) (s : ℂ) ↦
        (s - z.2)⁻¹ * (c (z.1, s) * f (z.1, s))) ((D ×ˢ ball 0 r) ×ˢ sphere 0 r) :=
      hK₁.mul (hK₂.mul hK₃)
    have hG : DifferentiableOn ℂ
        (fun z : B × ℂ ↦ ∮ s in C(0, r), (s - z.2)⁻¹ * (c (z.1, s) * f (z.1, s)))
        (D ×ˢ ball 0 r) :=
      differentiableOn_circleIntegral (hD.prod isOpen_ball) hr
        (fun s hs ↦ (hG₁ s hs).mul ((hG₂ s hs).mul (hG₃ s hs))) hK
    exact hG.const_mul _
  -- near the circles, `F = c * f`
  have hFann : ∀ b ∈ D, ∀ t : ℂ, r₁ < ‖t‖ → ‖t‖ < r → F (b, t) = c (b, t) * f (b, t) :=
    fun b hb t ht₁ ht₂ ↦ Laurent.cauchyIntegral_eq_of_forall_moment_eq_zero
      (f := fun s ↦ c (b, s) * f (b, s))
      (hAeq ▸ (hcs b).differentiableOn.mul (hslice b hb)) hρ (hmom b hb) ht₁ ht₂
  -- on the good slices, `F = c * f` away from the poles
  have hFnice : ∀ b ∈ Nice, ∀ t ∈ ball (0 : ℂ) r, (p b).eval t ≠ 0 →
      F (b, t) = c (b, t) * f (b, t) := by
    intro b hb t ht hpt
    have h₁ : AnalyticOnNhd ℂ (fun s ↦ (p b).eval s * F (b, s)) (ball 0 r) :=
      ((p b).differentiable.differentiableOn.mul
        (hF.comp (by fun_prop) fun s hs ↦ ⟨hb.1, hs⟩)).analyticOnNhd isOpen_ball
    have h₂ : AnalyticOnNhd ℂ (fun s ↦ c (b, s) * ((p b).eval s * f (b, s))) (ball 0 r) :=
      fun s hs ↦ ((hcs b).analyticAt s).mul (hpa b hb s (ball_subset_closedBall hs))
    set t₀ : ℂ := (((max r₁ 0 + r) / 2 : ℝ) : ℂ)
    have ht₀ : ‖t₀‖ = (max r₁ 0 + r) / 2 := by
      simp only [t₀, norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    have hA₀ : IsOpen {s : ℂ | r₁ < ‖s‖ ∧ ‖s‖ < r} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm
        continuous_const)
    have hmax : r₁ ≤ max r₁ 0 := le_max_left _ _
    have hmax' : max r₁ 0 < r := max_lt hr₁ hr
    have heq : (fun s ↦ (p b).eval s * F (b, s)) =ᶠ[𝓝 t₀]
        fun s ↦ c (b, s) * ((p b).eval s * f (b, s)) := by
      filter_upwards [hA₀.mem_nhds (show r₁ < ‖t₀‖ ∧ ‖t₀‖ < r by
        constructor <;> rw [ht₀] <;> linarith)] with s hs
      rw [hFann b hb.1 s hs.1 hs.2]
      ring
    have := h₁.eqOn_of_preconnected_of_eventuallyEq h₂ (convex_ball 0 r).isPreconnected
      (mem_ball_zero_iff.mpr (by rw [ht₀]; linarith)) heq ht
    refine mul_left_cancel₀ hpt ?_
    simp only at this
    rw [this]
    ring
  -- the zero set of `c` has empty interior: its leading coefficient is the chosen minor
  have hc0 : interior ((D ×ˢ ball 0 r) ∩ c ⁻¹' {0}) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun z hz ↦ hb₁ ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    rw [← ball_prod_same] at hball
    have hzD : z.1 ∈ D := (interior_subset hz).1.1
    have hvan : ∀ b ∈ ball z.1 ε, hankelMinor μ rows b = 0 := by
      intro b hb
      set P : ℂ[X] := ∑ j : Fin (d + 1), C (cof j b) * X ^ (j : ℕ)
      have hPeval : ∀ t, P.eval t = c (b, t) := fun t ↦ by
        simp [P, c, eval_finsetSum]
      have hP0 : P = 0 := by
        refine P.eq_zero_of_infinite_isRoot ((infinite_of_mem_nhds z.2
          (ball_mem_nhds z.2 hε)).mono fun t ht ↦ ?_)
        have := (interior_subset (hball (show (b, t) ∈ ball z.1 ε ×ˢ ball z.2 ε from ⟨hb, ht⟩))).2
        simpa [IsRoot, hPeval] using this
      have hcoeff := congrArg (fun P : ℂ[X] ↦ P.coeff d) hP0
      simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hcoeff
      rw [Fintype.sum_eq_single (Fin.last d) fun j hj ↦ ite_eq_right fun h ↦ hj
        (Fin.ext (by simpa using h.symm))] at hcoeff
      simpa [cof, hankelCof_last] using hcoeff
    have hana : AnalyticOnNhd ℂ (hankelMinor μ rows) D := fun b hb ↦
      analyticAt_of_differentiableOn_of_finiteDimensional hD
        (differentiableOn_hankelMinor hμ rows) hb
    exact hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hzD
      (Filter.mem_of_superset (ball_mem_nhds z.1 hε) hvan) hb₁D
  refine ⟨c, F, hc.mono (prod_mono subset_rfl (subset_univ _)), hF, hc0, ?_⟩
  -- `F = c * f` at the points of continuity of `f`, by density of the good points
  rintro ⟨b, t⟩ ⟨hbD, ht⟩ hS hfc
  obtain ⟨N, hN, u, w, hu, hw, hw0, hfuw⟩ :=
    hmer b hbD t (mem_ball_zero_iff.mp ht).le hS
  by_contra hne
  have hΦ : ContinuousAt (fun y ↦ F y - c y * f y) (b, t) := by
    have hopen := (hD.prod isOpen_ball).mem_nhds (show (b, t) ∈ D ×ˢ ball 0 r from ⟨hbD, ht⟩)
    exact (hF.continuousOn.continuousAt hopen).sub
      (((hc.mono (prod_mono subset_rfl (subset_univ _))).continuousOn.continuousAt hopen).mul
        hfc)
  set U₀ := interior ({y | F y - c y * f y ≠ 0} ∩ N ∩ (D ×ˢ ball 0 r))
  have hzU₀ : (b, t) ∈ U₀ := mem_interior_iff_mem_nhds.mpr (inter_mem (inter_mem
    (hΦ.eventually_ne (sub_ne_zero.mpr hne)) hN)
    ((hD.prod isOpen_ball).mem_nhds ⟨hbD, ht⟩))
  have hU₀N : U₀ ⊆ N := interior_subset.trans (inter_subset_left.trans inter_subset_right)
  set Y := U₀ ∩ w ⁻¹' {0}ᶜ
  have hYo : IsOpen Y :=
    (hw.continuousOn.mono hU₀N).isOpen_inter_preimage isOpen_interior isOpen_compl_singleton
  have hYne : Y.Nonempty := by
    by_contra hY
    have : U₀ ⊆ interior (N ∩ w ⁻¹' {0}) := interior_maximal (fun y hy ↦ ⟨hU₀N hy, by
      by_contra h
      exact hY ⟨y, hy, h⟩⟩) isOpen_interior
    rw [hw0] at this
    exact this hzU₀
  obtain ⟨y₀, hy₀⟩ := hYne
  have hY₀ : ∀ y ∈ Y, y.1 ∈ D := fun y hy ↦
    (mem_prod.mp (interior_subset hy.1 : y ∈ _).2).1
  obtain ⟨O', -, ⟨b', hb'⟩, hO'sub, hO'nice⟩ := exists_isOpen_forall_meromorphicAt_slice hD hbad
    hmer (isOpenMap_fst _ hYo) ⟨y₀.1, ⟨y₀, hy₀, rfl⟩, hY₀ y₀ hy₀⟩
  obtain ⟨⟨b'', t'⟩, hy, rfl⟩ := (hO'sub hb').1
  have hnice : b'' ∈ Nice := ⟨(hO'sub hb').2, hO'nice b'' hb'⟩
  -- `f` is holomorphic near `(b'', t')`, so `t'` is not a root of `p b''`
  have hYN : Y ⊆ interior N := fun y hy ↦ interior_mono (inter_subset_left.trans
    inter_subset_right) hy.1
  have hsl : AnalyticAt ℂ (fun s ↦ f (b'', s)) t' := by
    set W' : Set ℂ := (fun s ↦ (b'', s)) ⁻¹' Y
    have hW' : W' ∈ 𝓝 t' := (hYo.preimage (by fun_prop)).mem_nhds hy
    have hd : DifferentiableOn ℂ (fun s ↦ u (b'', s) / w (b'', s)) W' := by
      intro s hs
      have hN' : N ∈ 𝓝 (b'', s) := mem_interior_iff_mem_nhds.mp (hYN hs)
      exact (((hu.differentiableAt hN').comp s (by fun_prop)).div
        ((hw.differentiableAt hN').comp s (by fun_prop)) hs.2).differentiableWithinAt
    refine (hd.analyticAt hW').congr ?_
    filter_upwards [hW'] with s hs
    exact (hfuw _ (interior_subset (hYN hs)) hs.2).symm
  have hyD : (b'', t') ∈ D ×ˢ ball (0 : ℂ) r :=
    (interior_subset hy.1 : (b'', t') ∈ _).2
  exact (interior_subset hy.1 : (b'', t') ∈ _).1.1
    (sub_eq_zero.mpr (hFnice b'' hnice t' (mem_prod.mp hyD).2 (hpr b'' hnice t' hsl)))

end Prod

/-! ### Holomorphic denominators -/

section Denominator

/-- `f` has a holomorphic denominator near `a` across `S`: on an open neighbourhood `W` of `a`
there are holomorphic functions `c` and `F` such that the zero set of `c` has empty interior and
`F = c * f` at every point outside `S` at which `f` is continuous. -/
def HasDenominatorAt (S : Set E) (f : E → ℂ) (a : E) : Prop :=
  ∃ W : Set E, IsOpen W ∧ a ∈ W ∧ ∃ c F : E → ℂ, DifferentiableOn ℂ c W ∧
    DifferentiableOn ℂ F W ∧ interior (W ∩ c ⁻¹' {0}) = ∅ ∧
    ∀ z ∈ W, z ∉ S → ContinuousAt f z → F z = c z * f z

variable {S : Set E} {f : E → ℂ} {a : E}

/-- A local quotient representation is a holomorphic denominator. -/
theorem IsLocallyQuotientAt.hasDenominatorAt (h : IsLocallyQuotientAt f a) :
    HasDenominatorAt S f a := by
  obtain ⟨N, hN, u, w, hu, hw, hw0, hf⟩ := h
  have hW : interior N ⊆ N := interior_subset
  have hW0 : interior (interior N ∩ w ⁻¹' {0}) = ∅ :=
    subset_empty_iff.mp (hw0 ▸ interior_mono (inter_subset_inter_left _ hW))
  refine ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN, w, u, hw.mono hW,
    hu.mono hW, hW0, fun z hz _ hfz ↦ ?_⟩
  by_contra hne
  have hN' : N ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  have hΦ : ContinuousAt (fun y ↦ u y - w y * f y) z :=
    (hu.continuousOn.continuousAt hN').sub ((hw.continuousOn.continuousAt hN').mul hfz)
  have hev := hΦ.eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨y, hy, hyN, hyw⟩ := mem_closure_iff_nhds.mp
    (subset_closure_diff_zero isOpen_interior hW0 hz) _ hev
  refine hy ?_
  rw [hf y (hW hyN) hyw, mul_div_cancel₀ _ hyw, sub_self]

/-- Holomorphic denominators can be transported along affine isomorphisms. -/
theorem HasDenominatorAt.of_continuousLinearEquiv {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (e : E' ≃L[ℂ] E) (b : E) {a' : E'}
    (h : HasDenominatorAt ((fun x ↦ e x + b) ⁻¹' S) (fun x ↦ f (e x + b)) a') :
    HasDenominatorAt S f (e a' + b) := by
  obtain ⟨W, hW, ha, c, F, hc, hF, hc0, hcF⟩ := h
  set ψ : E → E' := fun y ↦ e.symm (y - b)
  have hψ : Differentiable ℂ ψ := by fun_prop
  have hψo : IsOpenMap ψ := e.symm.toHomeomorph.isOpenMap.comp (Homeomorph.subRight b).isOpenMap
  have hψe : ∀ x, ψ (e x + b) = x := fun x ↦ by simp [ψ]
  have heψ : ∀ y, e (ψ y) + b = y := fun y ↦ by simp [ψ]
  refine ⟨ψ ⁻¹' W, hW.preimage hψ.continuous, by simpa [hψe] using ha, c ∘ ψ, F ∘ ψ,
    hc.comp hψ.differentiableOn fun y hy ↦ hy, hF.comp hψ.differentiableOn fun y hy ↦ hy,
    ?_, fun z hz hzS hfz ↦ ?_⟩
  · refine eq_empty_iff_forall_notMem.mpr fun y hy ↦ ?_
    have hsub : ψ '' interior (ψ ⁻¹' W ∩ (c ∘ ψ) ⁻¹' {0}) ⊆ W ∩ c ⁻¹' {0} := by
      rintro _ ⟨y', hy', rfl⟩
      exact (interior_subset hy' : y' ∈ ψ ⁻¹' W ∩ (c ∘ ψ) ⁻¹' {0})
    have : ψ y ∈ interior (W ∩ c ⁻¹' {0}) :=
      interior_maximal hsub (hψo _ isOpen_interior) ⟨y, hy, rfl⟩
    rwa [hc0] at this
  · have hcont : ContinuousAt (fun x ↦ f (e x + b)) (ψ z) := by
      refine ContinuousAt.comp (g := f) ?_ (by fun_prop)
      rwa [heψ]
    have := hcF (ψ z) hz (by simpa [heψ] using hzS) hcont
    simpa [heψ] using this

/-- Local quotient representations can be transported along affine isomorphisms. -/
theorem IsLocallyQuotientAt.comp_continuousLinearEquiv {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (e : E' ≃L[ℂ] E) (b : E) {x : E'}
    (h : IsLocallyQuotientAt f (e x + b)) : IsLocallyQuotientAt (fun x ↦ f (e x + b)) x := by
  obtain ⟨N, hN, u, w, hu, hw, hw0, hf⟩ := h
  set χ : E' → E := fun x ↦ e x + b
  have hχ : Differentiable ℂ χ := by fun_prop
  have hχo : IsOpenMap χ := (Homeomorph.addRight b).isOpenMap.comp e.toHomeomorph.isOpenMap
  refine ⟨χ ⁻¹' N, hχ.continuous.continuousAt.preimage_mem_nhds hN, u ∘ χ, w ∘ χ,
    hu.comp hχ.differentiableOn fun y hy ↦ hy, hw.comp hχ.differentiableOn fun y hy ↦ hy, ?_,
    fun y hy hwy ↦ hf (χ y) hy hwy⟩
  refine eq_empty_iff_forall_notMem.mpr fun y hy ↦ ?_
  have hsub : χ '' interior (χ ⁻¹' N ∩ (w ∘ χ) ⁻¹' {0}) ⊆ N ∩ w ⁻¹' {0} := by
    rintro _ ⟨y', hy', rfl⟩
    exact (interior_subset hy' : y' ∈ χ ⁻¹' N ∩ (w ∘ χ) ⁻¹' {0})
  have : χ y ∈ interior (N ∩ w ⁻¹' {0}) :=
    interior_maximal hsub (hχo _ isOpen_interior) ⟨y, hy, rfl⟩
  rwa [hw0] at this

/-- Finitely many functions with holomorphic denominators near `a` have a common holomorphic
denominator near `a`. -/
theorem exists_common_denominator {ι : Type*} (T : Finset ι) {f : ι → E → ℂ}
    (h : ∀ i ∈ T, HasDenominatorAt S (f i) a) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧ ∃ c : E → ℂ, DifferentiableOn ℂ c W ∧
      interior (W ∩ c ⁻¹' {0}) = ∅ ∧ ∀ i ∈ T, ∃ F : E → ℂ, DifferentiableOn ℂ F W ∧
        ∀ z ∈ W, z ∉ S → ContinuousAt (f i) z → F z = c z * f i z := by
  classical
  choose! W hW ha c F hc hF hc0 hcF using h
  set W₀ := ⋂ i ∈ T, W i
  have hdiff : ∀ T' : Finset ι, T' ⊆ T →
      DifferentiableOn ℂ (fun z ↦ ∏ i ∈ T', c i z) W₀ := by
    intro T' hT'
    induction T' using Finset.induction_on with
    | empty => simp
    | insert j T' hj ih =>
      simp_rw [Finset.prod_insert hj]
      exact ((hc j (hT' (Finset.mem_insert_self j T'))).mono fun z hz ↦
        mem_iInter₂.mp hz j (hT' (Finset.mem_insert_self j T'))).mul
        (ih ((Finset.subset_insert j T').trans hT'))
  refine ⟨W₀, isOpen_biInter_finset fun i hi ↦ hW i hi, mem_iInter₂.mpr ha,
    fun z ↦ ∏ i ∈ T, c i z, hdiff T subset_rfl, ?_, fun i hi ↦ ?_⟩
  · refine interior_inter_preimage_zero_prod_eq_empty T (fun i hi ↦ (hc i hi).continuousOn.mono
      fun z hz ↦ mem_iInter₂.mp hz i hi) fun i hi ↦ ?_
    exact subset_empty_iff.mp (hc0 i hi ▸ interior_mono (inter_subset_inter_left _
      fun z hz ↦ mem_iInter₂.mp hz i hi))
  · refine ⟨fun z ↦ (∏ j ∈ T.erase i, c j z) * F i z, (hdiff _ (Finset.erase_subset i T)).mul
      ((hF i hi).mono fun z hz ↦ mem_iInter₂.mp hz i hi), fun z hz hzS hfz ↦ ?_⟩
    change (∏ j ∈ T.erase i, c j z) * F i z = (∏ j ∈ T, c j z) * f i z
    rw [hcF i hi z (mem_iInter₂.mp hz i hi) hzS hfz, ← mul_assoc,
      Finset.prod_erase_mul T (fun j ↦ c j z) hi]

end Denominator
