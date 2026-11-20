import Tengoku.PshdLean.PshLines.PSHD.NullLineSlices
import Tengoku.PshdLean.PshLines.PSHD.ComponentSections
import Tengoku.PshdLean.PshLines.PSHD.LocalBound
import Tengoku.PshdLean.PshLines.PlurisubharmonicAE
import Tengoku.PshdLean.PshLines.PlurisubharmonicPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Pointwise recovery of the representative along lines

Step 4 of Proposition 2.1 of `pshd-vibe`, following the article. Let `u` be
subharmonic on every affine complex-line section of an open set and let `v` be
plurisubharmonic there with `u = v` almost everywhere. Through a given point,
some complex line meets the exceptional null set in a planar null set. On that
line both restrictions are plurisubharmonic in one variable and agree almost
everywhere, hence agree everywhere, in particular at the given point.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Pointwise recovery of the representative along lines** (Step 4 of
Proposition 2.1). A real function which is subharmonic on every connected
component of every affine complex-line section of an open set agrees at every
point with any plurisubharmonic function equal to it almost everywhere.
@isnad1 id=eq.5h6v.s7.9d93dfea251c from=translated src=- shape=afaa7bc6 vocab=a43ffb85
-/
theorem LineSubharmonicOn.eqOn_of_ae_eq_of_lines {u : E → ℝ} {v : E → EReal} {D : Set E}
    (hD : IsOpen D) (hl : LineSubharmonicOn u D) (hv : PlurisubharmonicOn v D)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : ∀ᵐ y ∂μ.restrict D, (u y : EReal) = v y) :
    ∀ x ∈ D, (u x : EReal) = v x := by
  classical
  intro x hx
  let S : Set E := {y | y ∈ D ∧ (u y : EReal) ≠ v y}
  have hS : μ S = 0 := by
    rw [ae_restrict_iff' hD.measurableSet] at hae
    rw [← compl_mem_ae_iff]
    filter_upwards [hae] with y hy hyS
    exact hyS.2 (hy hyS.1)
  by_cases hE : Nontrivial E
  · let _ : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    have hS' : (volume : Measure E) S = 0 :=
      Measure.absolutelyContinuous_isAddHaarMeasure volume μ hS
    obtain ⟨e, he, hnull⟩ := exists_unit_line_preimage_null hS' x
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at he
    let O : Set ℂ := (fun t : ℂ ↦ x + t • e) ⁻¹' D
    have hO : IsOpen O := hD.preimage (by fun_prop)
    have h0 : (0 : ℂ) ∈ O := by simpa [O] using hx
    have h₁ : PlurisubharmonicOn (fun t : ℂ ↦ (u (x + t • e) : EReal)) O :=
      (discPshOn_of_connectedComponentIn hO fun t ht ↦ hl x e he0 t ht).plurisubharmonicOn hO
    have h₂ : PlurisubharmonicOn (fun t : ℂ ↦ v (x + t • e)) O :=
      hv.comp_affine ((ContinuousLinearMap.id ℂ ℂ).smulRight e) x
    have hae' : (fun t : ℂ ↦ (u (x + t • e) : EReal)) =ᵐ[volume.restrict O]
        fun t ↦ v (x + t • e) := by
      rw [EventuallyEq, ae_restrict_iff' hO.measurableSet]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht htO
      by_contra hne
      exact ht ⟨htO, hne⟩
    simpa using h₁.eqOn_of_ae_eq h₂ hO volume hae' h0
  · have hsub : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    by_contra hne
    have hSx : S = univ := by
      refine eq_univ_of_forall fun y ↦ ?_
      rw [Subsingleton.elim y x]
      exact ⟨hx, hne⟩
    rw [hSx] at hS
    exact (Measure.measure_univ_pos.mpr (NeZero.ne μ)).ne' hS

end PshLines.PSHD
