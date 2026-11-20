import Tengoku.PshdLean.PshLines.PSHD.Borel
import Tengoku.PshdLean.PshLines.PSHD.BallUpperSemicontinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite nonnegative functions

Proposition 2.1 of `pshd-vibe`: a finite nonnegative function on an open set
that is subharmonic on every connected component of every affine complex-line
section is plurisubharmonic. The proof is by induction on the dimension: the
induction hypothesis on the complex hyperplane `(ℂ ∙ e)ᗮ` gives Borel
measurability through Lemma 1.2, Lemmas 1.3-1.5 give local upper bounds, and
ball averages give upper semicontinuity.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace PshLines.PSHD

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Restricting to translates of a complex subspace preserves subharmonicity
on line sections.
@isnad1 id=linesubh.1h5v.s9.0b5131ed9835 from=translated src=- shape=a89c12d6 vocab=f6552181
-/
theorem LineSubharmonicOn.comp_submodule_add {u : E → ℝ} {D : Set E}
    (hl : LineSubharmonicOn u D) (K : Submodule ℂ E) (a : E) :
    LineSubharmonicOn (fun w : K => u (w + a)) {w : K | (w : E) + a ∈ D} := by
  intro c v hv s hs
  have key : ∀ s : ℂ, ((c + s • v : K) : E) + a = ((c : E) + a) + s • (v : E) := fun s => by
    simp only [Submodule.coe_add, Submodule.coe_smul]
    abel
  have hset : (fun s : ℂ => c + s • v) ⁻¹' {w : K | (w : E) + a ∈ D} =
      (fun s : ℂ => ((c : E) + a) + s • (v : E)) ⁻¹' D := by
    ext s
    simp only [mem_preimage, mem_ofPred_eq, key]
  have hv' : (v : E) ≠ 0 := by simpa using hv
  have h := hl ((c : E) + a) (v : E) hv' s (by rw [← hset]; exact hs)
  simp only [hset, key]
  exact h

/-- In complex dimension at most one, line subharmonicity already gives upper
semicontinuity.
@isnad1 id=uppersem.3h3v.s6.273c68e78a80 from=translated src=- shape=8bbb55b6 vocab=9f97437f
-/
theorem LineSubharmonicOn.upperSemicontinuousOn_of_finrank_le_one [FiniteDimensional ℂ E]
    (hn : Module.finrank ℂ E ≤ 1) {u : E → ℝ} {D : Set E} (hD : IsOpen D)
    (hl : LineSubharmonicOn u D) : UpperSemicontinuousOn u D := by
  intro z hz
  suffices h : UpperSemicontinuousAt u z from h.upperSemicontinuousWithinAt D
  intro b hb
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Eventually.of_forall fun x => (Subsingleton.elim z x) ▸ hb
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hspan : ∀ w : E, ∃ c : ℂ, c • v = w :=
    (finrank_eq_one_iff_of_nonzero' v hv).mp (le_antisymm hn Module.finrank_pos)
  have hline := hl.upperSemicontinuousAt_line hD hz v b (by simpa using hb)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hline
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  filter_upwards [ball_mem_nhds z (mul_pos hε hvpos)] with y hy
  obtain ⟨c, hc⟩ := hspan (y - z)
  have hcε : dist c 0 < ε := by
    rw [dist_zero_right]
    rw [mem_ball, dist_eq_norm, ← hc, norm_smul] at hy
    exact lt_of_mul_lt_mul_right hy hvpos.le
  simpa [hc] using hball hcε

/-- **Step 1 of Proposition 2.1.** Upper semicontinuity on the slices parallel
to a complex hyperplane gives Borel measurability through Lemma 1.2.
@isnad1 id=measurab.5h4v.s10.04937931fb4d from=translated src=- shape=993b1681 vocab=2b69377b
-/
theorem LineSubharmonicOn.measurable_indicator [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℂ E] {u : E → ℝ} {D : Set E} (hD : IsOpen D)
    (hpos : ∀ x ∈ D, 0 ≤ u x) (hl : LineSubharmonicOn u D) {e : E} (he : ‖e‖ = 1)
    (hslice : ∀ t : ℂ, UpperSemicontinuousOn (fun w : (ℂ ∙ e)ᗮ => u (w + t • e))
      {w | (w : E) + t • e ∈ D}) :
    Measurable (D.indicator u) := by
  set W := (ℂ ∙ e)ᗮ
  have he0 : e ≠ 0 := by
    intro h
    simp [h] at he
  let G : Set (W × ℂ) := {p | (p.1 : E) + p.2 • e ∈ D}
  have hG : IsOpen G := hD.preimage (by fun_prop)
  let F : W × ℂ → ℝ := fun p => u ((p.1 : E) + p.2 • e)
  have hborel : Measurable (fun p : G => F p.1) :=
    borel_measurable_of_sections (X := W) hG (f := fun w t => u ((w : E) + t • e))
      (fun t => hslice t) (fun _ _ h => hpos _ h) (fun w _ h => hl w e he0 _ h)
  have hFG : Measurable (G.indicator F) := by
    refine measurable_of_restrict_of_restrict_compl hG.measurableSet ?_ ?_
    · convert hborel using 1
      funext p
      simp [Set.domRestrict, p.property]
    · convert (measurable_const : Measurable fun _ : (Gᶜ : Set (W × ℂ)) => (0 : ℝ)) using 1
      funext p
      exact indicator_of_notMem p.property _
  have hmem : ∀ y : E, y - ⟪e, y⟫_ℂ • e ∈ W := fun y => by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, he]
  let Ψ : E → W × ℂ := fun y => (⟨y - ⟪e, y⟫_ℂ • e, hmem y⟩, ⟪e, y⟫_ℂ)
  have hΦΨ : ∀ y, ((Ψ y).1 : E) + (Ψ y).2 • e = y := fun y => by simp [Ψ]
  have hΨ : Measurable Ψ := by
    refine Continuous.measurable (Continuous.prodMk ?_ ?_)
    · exact Continuous.subtype_mk (by fun_prop) _
    · fun_prop
  have heq : D.indicator u = G.indicator F ∘ Ψ := by
    funext y
    by_cases hy : y ∈ D
    · have hyG : Ψ y ∈ G := by
        change ((Ψ y).1 : E) + (Ψ y).2 • e ∈ D
        rw [hΦΨ]
        exact hy
      simp only [Function.comp_apply, indicator_of_mem hy, indicator_of_mem hyG, F, hΦΨ]
    · have hyG : Ψ y ∉ G := by
        change ((Ψ y).1 : E) + (Ψ y).2 • e ∉ D
        rw [hΦΨ]
        exact hy
      simp only [Function.comp_apply, indicator_of_notMem hy, indicator_of_notMem hyG]
  rw [heq]
  exact hFG.comp hΨ

/-- The closing step of Proposition 2.1 in universe `u`: a Borel, nonnegative,
locally bounded above function that is subharmonic on every connected component
of every affine complex-line section of an open set is upper semicontinuous
there. Steps 1-2 reduce Proposition 2.1 to this statement; the ball-average
route and the article's route through a plurisubharmonic representative both
prove it.-/
def BoundedLineSubharmonicUSC : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ} {D : Set E}, IsOpen D →
    LineSubharmonicOn u D → Measurable u → (∀ x ∈ D, 0 ≤ u x) →
    (∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r)) → UpperSemicontinuousOn u D

/-- The ball-average route closes Proposition 2.1.
@isnad1 id=boundedl.0h0v.s0.9b71cf81d297 from=translated src=- shape=45709ebd vocab=d19378b0
-/
theorem boundedLineSubharmonicUSC_of_ballAverage : BoundedLineSubharmonicUSC.{u} :=
  fun hD hl hu hpos hbdd => hl.upperSemicontinuousOn hD hu hpos hbdd

/-- **Induction of Proposition 2.1.** Given a closing step, every nonnegative
function that is subharmonic on line sections of an open set is upper
semicontinuous: slices along `(ℂ ∙ e)ᗮ` are upper semicontinuous by induction,
which gives Borel measurability (Step 1) and local upper bounds (Step 2).
@isnad1 id=uppersem.5h4v.s7.aba0dc87bd49 from=translated src=- shape=0795e825 vocab=59152a41
-/
theorem upperSemicontinuousOn_of_boundedLineSubharmonicUSC
    (hstep : BoundedLineSubharmonicUSC.{u}) (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E],
      Module.finrank ℂ E = n → ∀ {u : E → ℝ} {D : Set E}, IsOpen D →
        (∀ x ∈ D, 0 ≤ u x) → LineSubharmonicOn u D → UpperSemicontinuousOn u D := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E _ _ _ hn u D hD hpos hl
  rcases Nat.lt_or_ge n 2 with h | h
  · exact hl.upperSemicontinuousOn_of_finrank_le_one (by omega) hD
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  have he0 : e ≠ 0 := by
    intro h
    simp [h] at he
  have : Fact (Module.finrank ℂ E = (n - 1) + 1) := ⟨by omega⟩
  have hW : Module.finrank ℂ (ℂ ∙ e)ᗮ = n - 1 := Submodule.finrank_orthogonal_span_singleton he0
  have hslice : ∀ t : ℂ, UpperSemicontinuousOn (fun w : (ℂ ∙ e)ᗮ => u (w + t • e))
      {w | (w : E) + t • e ∈ D} := fun t =>
    ih (n - 1) (by omega) hW (hD.preimage (by fun_prop)) (fun w hw => hpos _ hw)
      (hl.comp_submodule_add _ _)
  borelize E
  have hmeas := hl.measurable_indicator hD hpos he hslice
  have heqOn : EqOn u (D.indicator u) D := fun x hx => (indicator_of_mem hx u).symm
  have hl' := hl.congr heqOn
  have husc := hstep hD hl' hmeas
    (fun x hx => by rw [← heqOn hx]; exact hpos x hx)
    (fun p hp => hl'.exists_bddAbove (by omega) hmeas hD hp)
  intro x hx
  exact (husc x hx).congr_of_eventuallyEq hx
    (eventually_nhdsWithin_of_forall fun y hy c => by rw [heqOn hy])

/-- **Proposition 2.1** (`pshd-vibe`). A nonnegative real function on an open
set that is subharmonic on every connected component of every affine
complex-line section is plurisubharmonic.
@isnad1 id=discpsho.3h3v.s6.cb7e15c2a381 from=translated src=- shape=4e8b9adb vocab=fe226cd7
-/
theorem LineSubharmonicOn.discPshOn_of_nonneg [FiniteDimensional ℂ E] {u : E → ℝ} {D : Set E}
    (hD : IsOpen D) (hpos : ∀ x ∈ D, 0 ≤ u x) (hl : LineSubharmonicOn u D) :
    DiscPshOn (fun x => (u x : EReal)) D :=
  hl.discPshOn (upperSemicontinuousOn_of_boundedLineSubharmonicUSC
    boundedLineSubharmonicUSC_of_ballAverage _ rfl hD hpos hl)

end PshLines.PSHD
