import Tengoku.PshdLean.PshLines.PSHD.LocalBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Affine complex-line sections

Elementary consequences of subharmonicity on every connected component of
every affine complex-line section, used in Proposition 2.1 of `pshd-vibe`.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The line condition only depends on the values in the domain.
@isnad1 id=linesubh.2h4v.s5.27d54359a7a0 from=translated src=- shape=1d74f7e5 vocab=0aa09659
-/
theorem LineSubharmonicOn.congr {u w : E → ℝ} {D : Set E} (hu : LineSubharmonicOn u D)
    (heq : EqOn u w D) : LineSubharmonicOn w D := by
  intro c v hv z hz
  refine (hu c v hv z hz).congr ?_
  intro t ht
  have htD : t ∈ (fun t : ℂ => c + t • v) ⁻¹' D := connectedComponentIn_subset _ _ ht
  simp only [heq htD]

/-- On an open domain, every line through a point of the domain is upper
semicontinuous at that point.
@isnad1 id=uppersem.3h5v.s7.e6bb1ddccc46 from=translated src=- shape=f46deb0f vocab=5a128cb7
-/
theorem LineSubharmonicOn.upperSemicontinuousAt_line {u : E → ℝ} {D : Set E}
    (hD : IsOpen D) (hl : LineSubharmonicOn u D) {z : E} (hz : z ∈ D) (v : E) :
    UpperSemicontinuousAt (fun t : ℂ => u (z + t • v)) 0 := by
  by_cases hv : v = 0
  · subst hv
    simpa using (upperSemicontinuousAt_const (x := (0 : ℂ)) (z := u z))
  have hP : IsOpen ((fun t : ℂ => z + t • v) ⁻¹' D) := hD.preimage (by fun_prop)
  have h0 : (0 : ℂ) ∈ (fun t : ℂ => z + t • v) ⁻¹' D := by simpa using hz
  have hnhds : connectedComponentIn ((fun t : ℂ => z + t • v) ⁻¹' D) 0 ∈ 𝓝 (0 : ℂ) :=
    hP.connectedComponentIn.mem_nhds (mem_connectedComponentIn h0)
  intro b hb
  have h := (hl z v hv 0 h0).upperSemicontinuousOn 0 (mem_connectedComponentIn h0)
    (b : EReal) (EReal.coe_lt_coe_iff.mpr hb)
  rw [nhdsWithin_eq_nhds.mpr hnhds] at h
  filter_upwards [h] with t ht
  exact_mod_cast ht

/-- An extended-real function satisfying the disc criterion on every connected
component of every affine complex-line section satisfies the disc submean
inequality on every affine closed disc in the domain.
@isnad1 id=hasdiscs.1h3v.s8.115169411530 from=translated src=- shape=a62107f4 vocab=b8b20bff
-/
theorem hasDiscSubmeanOn_of_line_sections {φ : E → EReal} {D : Set E}
    (hl : ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' D,
      DiscPshOn (fun t ↦ φ (c + t • v)) (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' D) z)) :
    HasDiscSubmeanOn φ D := by
  intro x v r hr hDisc C hC
  by_cases hv : v = 0
  · subst hv
    simp [circleDeficit, mul_comm]
  set P := (fun t : ℂ => x + t • v) ⁻¹' D
  have hball : closedBall (0 : ℂ) r ⊆ P := fun t ht => hDisc ⟨t, ht, rfl⟩
  have h0 : (0 : ℂ) ∈ P := hball (mem_closedBall_self hr.le)
  have hdisc : affineClosedDisc (0 : ℂ) 1 r = closedBall 0 r := by
    simp [affineClosedDisc]
  have hK : affineClosedDisc (0 : ℂ) 1 r ⊆ connectedComponentIn P 0 := by
    rw [hdisc]
    exact (convex_closedBall (0 : ℂ) r).isPreconnected.subset_connectedComponentIn
      (mem_closedBall_self hr.le) hball
  have h := (hl x v hv 0 h0).submean 0 1 r hr hK C (by
    rw [hdisc]
    intro t ht
    exact hC _ ⟨t, ht, rfl⟩)
  simpa [circleDeficit] using h

/-- Subharmonicity on line sections gives the disc submean inequality on every
affine closed disc in the domain.
@isnad1 id=hasdiscs.1h3v.s5.fbafa1c9ca98 from=translated src=- shape=438cd883 vocab=41a89cd1
-/
theorem LineSubharmonicOn.hasDiscSubmeanOn {u : E → ℝ} {D : Set E}
    (hl : LineSubharmonicOn u D) : HasDiscSubmeanOn (fun x => (u x : EReal)) D :=
  hasDiscSubmeanOn_of_line_sections hl

/-- An upper semicontinuous function that is subharmonic on line sections
satisfies the project's disc criterion.
@isnad1 id=discpsho.2h3v.s5.3d143b203771 from=translated src=- shape=4ece1fc2 vocab=e4a9745b
-/
theorem LineSubharmonicOn.discPshOn {u : E → ℝ} {D : Set E}
    (hl : LineSubharmonicOn u D) (husc : UpperSemicontinuousOn u D) :
    DiscPshOn (fun x => (u x : EReal)) D :=
  ⟨fun _ _ => EReal.coe_ne_top _,
    continuous_coe_real_ereal.comp_upperSemicontinuousOn husc EReal.coe_strictMono.monotone,
    hl.hasDiscSubmeanOn⟩

end PshLines.PSHD
