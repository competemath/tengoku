import Tengoku.PshdLean.PshLines.PSHD.HighValueStar
import Tengoku.PshdLean.PshLines.PSHD.Incidence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Local upper bounds

Step 2 of `pshd-vibe`, Proposition 2.1: a Borel function that is subharmonic on
every connected component of every affine complex-line section is locally
bounded above.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Subharmonicity on every connected component of every affine complex-line
section of `D`.-/
def LineSubharmonicOn (u : E → ℝ) (D : Set E) : Prop :=
  ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' D,
    DiscPshOn (fun t ↦ (u (c + t • v) : EReal))
      (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' D) z)

omit [FiniteDimensional ℂ E] in
/-- The parameters of a line lying in a closed ball form a compact set.-/
theorem isCompact_line_preimage_closedBall (c : E) {v : E} (hv : v ≠ 0) (p : E) (r : ℝ) :
    IsCompact ((fun t : ℂ ↦ c + t • v) ⁻¹' closedBall p r) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_closedBall.preimage (by fun_prop)) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (r + ‖p - c‖) / ‖v‖)).subset ?_
  intro t ht
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  simp only [mem_preimage, mem_closedBall, dist_eq_norm] at ht
  rw [mem_closedBall, dist_zero_right, le_div_iff₀ hvpos]
  calc ‖t‖ * ‖v‖ = ‖t • v‖ := (norm_smul t v).symm
    _ = ‖(c + t • v - p) + (p - c)‖ := by congr 1; abel
    _ ≤ ‖c + t • v - p‖ + ‖p - c‖ := norm_add_le _ _
    _ ≤ r + ‖p - c‖ := by linarith

omit [FiniteDimensional ℂ E] in
/-- The parameters of a line lying in an open ball form a convex set.-/
theorem convex_line_preimage_ball (c v p : E) (r : ℝ) :
    Convex ℝ ((fun t : ℂ ↦ c + t • v) ⁻¹' ball p r) := by
  have h : (fun t : ℂ ↦ c + t • v) ⁻¹' ball p r =
      ((LinearMap.toSpanSingleton ℂ E v).restrictScalars ℝ) ⁻¹' ball (p - c) r := by
    ext t
    simp only [mem_preimage, mem_ball, dist_eq_norm, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply]
    congr! 1
    abel_nf
  rw [h]
  exact (convex_ball _ _).linear_preimage _

variable [MeasurableSpace E] [BorelSpace E]

/-- **Local upper bounds** (`pshd-vibe`, Proposition 2.1, Step 2).-/
theorem LineSubharmonicOn.exists_bddAbove (hn : 2 ≤ Module.finrank ℂ E) {u : E → ℝ}
    (hu : Measurable u) {D : Set E} (hD : IsOpen D) (hl : LineSubharmonicOn u D)
    {p : E} (hp : p ∈ D) : ∃ r > 0, BddAbove (u '' ball p r) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨R₃, hR₃, hball⟩ := Metric.isOpen_iff.mp hD p hp
  set R := R₃ / 4 with hRdef
  have hR : 0 < R := by positivity
  have hball3 : closedBall p (3 * R) ⊆ D :=
    (closedBall_subset_ball (by linarith)).trans hball
  refine ⟨R / 2, by positivity, ?_⟩
  by_contra hunb
  rw [not_bddAbove_iff] at hunb
  have hx : ∀ j : ℕ, ∃ x ∈ ball p (R / 2), (j : ℝ) < u x := by
    intro j
    obtain ⟨_, ⟨x, hx, rfl⟩, hjx⟩ := hunb j
    exact ⟨x, hx, hjx⟩
  choose x hxball hxj using hx
  obtain ⟨C, hC, hstar⟩ := exists_uniform_highValue_star_of_components (E := E) hn hR
  have hμ : ∀ j, ∃ μ : Measure E, IsProbabilityMeasure μ ∧
      μ {y | ‖y - x j‖ ∈ Icc (R / 2) R ∧ u (x j) ≤ u y} = 1 ∧
      rieszEnergy (2 * (Module.finrank ℂ E - 1) : ℕ) μ ≤ C := by
    intro j
    refine hstar u hu D hD (x j) ?_ (fun v hv z hz ↦ hl (x j) v hv z hz)
    intro y hy
    apply hball3
    rw [mem_closedBall] at hy ⊢
    have := mem_ball.mp (hxball j)
    calc dist y p ≤ dist y (x j) + dist (x j) p := dist_triangle _ _ _
      _ ≤ 3 * R := by linarith
  choose μ hμprob hμS hμI using hμ
  set S : ℕ → Set E := fun j ↦ {y | ‖y - x j‖ ∈ Icc (R / 2) R ∧ u (x j) ≤ u y}
  have hSm : ∀ j, MeasurableSet (S j) := fun j ↦
    (measurableSet_preimage (by fun_prop) measurableSet_Icc).inter
      (measurableSet_le measurable_const hu)
  have hSK : ∀ j, S j ⊆ closedBall p (2 * R) := by
    intro j y hy
    rw [mem_closedBall]
    have h1 := mem_ball.mp (hxball j)
    have h2 := hy.1.2
    calc dist y p ≤ dist y (x j) + dist (x j) p := dist_triangle _ _ _
      _ ≤ 2 * R := by rw [dist_eq_norm]; linarith
  obtain ⟨c, v, hv, hrec⟩ := exists_affineLine_frequently_meets hn (isCompact_closedBall p (2 * R))
    hSm hSK μ hμS hC hμI
  -- the line section through the compact ball lies in one component
  set T := (fun t : ℂ ↦ c + t • v) ⁻¹' closedBall p (2 * R)
  set O := (fun t : ℂ ↦ c + t • v) ⁻¹' ball p (3 * R)
  obtain ⟨j₀, -, t₀, ht₀⟩ := hrec 0
  have ht₀T : t₀ ∈ T := hSK j₀ ht₀
  have hTO : T ⊆ O := fun t ht ↦ closedBall_subset_ball (by linarith) ht
  have hOD : O ⊆ (fun t : ℂ ↦ c + t • v) ⁻¹' D := fun t ht ↦ hball3 (ball_subset_closedBall ht)
  have hOcomp : O ⊆ connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' D) t₀ :=
    (convex_line_preimage_ball c v p (3 * R)).isPreconnected.subset_connectedComponentIn
      (hTO ht₀T) hOD
  have hpsh := (hl c v hv t₀ (hOD (hTO ht₀T))).mono (hTO.trans hOcomp)
  obtain ⟨s, hsT, hmax⟩ := hpsh.upperSemicontinuousOn.exists_isMaxOn ⟨t₀, ht₀T⟩
    (isCompact_line_preimage_closedBall c hv p (2 * R))
  obtain ⟨m, hm⟩ := exists_nat_gt (u (c + s • v))
  obtain ⟨j, hmj, t, ht⟩ := hrec m
  have htT : t ∈ T := hSK j ht
  have h1 : u (c + t • v) ≤ u (c + s • v) := by
    have := hmax htT
    simp only [Set.mem_ofPred_eq] at this
    exact_mod_cast this
  have h2 : u (x j) ≤ u (c + t • v) := ht.2
  have h3 : (m : ℝ) ≤ j := by exact_mod_cast hmj
  linarith [hxj j]

end PshLines.PSHD
