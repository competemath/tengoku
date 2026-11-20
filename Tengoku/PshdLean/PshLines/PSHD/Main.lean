import Tengoku.PshdLean.PshLines.PSHD.Finite
import Tengoku.PshdLean.PshLines.PshAddition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Subharmonicity on all affine complex lines forces upper semicontinuity

Theorem 1.1 of `pshd-vibe`. In the project's normalization a function which is
identically `⊥` on a component is allowed by `DiscPshOn`, so the hypothesis
"subharmonic or identically `-∞` on every connected component of every affine
complex-line section" is the disc criterion on those components, and the
conclusion "plurisubharmonic" is the disc criterion on the open domain.
-/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace PshLines.PSHD

variable {E : Type*}

/-- The truncation `max φ (-m)` shifted by `m`, as a finite real function.-/
def truncShift (φ : E → EReal) (m : ℕ) (x : E) : ℝ :=
  (max (φ x) ((-(m : ℝ) : ℝ) : EReal)).toReal + m

theorem coe_truncShift {φ : E → EReal} {x : E} (hx : φ x ≠ ⊤) (m : ℕ) :
    ((truncShift φ m x : ℝ) : EReal) = max (φ x) ((-(m : ℝ) : ℝ) : EReal) + (m : ℝ) := by
  have h1 : max (φ x) ((-(m : ℝ) : ℝ) : EReal) ≠ ⊤ :=
    ne_of_lt (max_lt (lt_top_iff_ne_top.mpr hx) (EReal.coe_lt_top _))
  have h2 : max (φ x) ((-(m : ℝ) : ℝ) : EReal) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  rw [truncShift, EReal.coe_add, EReal.coe_toReal h1 h2]

theorem truncShift_nonneg {φ : E → EReal} {x : E} (hx : φ x ≠ ⊤) (m : ℕ) :
    0 ≤ truncShift φ m x := by
  have h := coe_truncShift hx m
  have hle : ((0 : ℝ) : EReal) ≤ max (φ x) ((-(m : ℝ) : ℝ) : EReal) + (m : ℝ) := by
    calc ((0 : ℝ) : EReal) = ((-(m : ℝ) : ℝ) : EReal) + (m : ℝ) := by
          rw [← EReal.coe_add]; simp
      _ ≤ _ := add_le_add_left (le_max_right _ _) _
  rw [← h] at hle
  exact_mod_cast hle

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Lower truncations.** If `φ` has no value `⊤` on `Ω` and satisfies the disc
criterion on every component of every affine complex-line section, then each
finite nonnegative truncation `max φ (-m) + m` is subharmonic on these sections.-/
theorem lineSubharmonicOn_truncShift {φ : E → EReal} {Ω : Set E} (htop : ∀ x ∈ Ω, φ x ≠ ⊤)
    (hl : ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' Ω,
      DiscPshOn (fun t ↦ φ (c + t • v)) (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' Ω) z))
    (m : ℕ) : LineSubharmonicOn (truncShift φ m) Ω := by
  intro c v hv z hz
  refine (((hl c v hv z hz).max
    (discPshOn_const ((-(m : ℝ) : ℝ) : EReal) (EReal.coe_ne_top _) _)).add
    (discPshOn_const ((m : ℝ) : EReal) (EReal.coe_ne_top _) _)).congr ?_
  intro t ht
  have htΩ : t ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' Ω := connectedComponentIn_subset _ _ ht
  exact (coe_truncShift (htop _ htΩ) m).symm

/-- **Passage from finite to extended-real functions.** If an extended-real
function without the value `⊤` satisfies the disc criterion on line sections
and all of its shifted lower truncations `max φ (-m) + m` are plurisubharmonic,
then it is plurisubharmonic: it is the decreasing limit of the truncations.-/
theorem discPshOn_of_line_sections_of_truncShift {φ : E → EReal} {Ω : Set E}
    (htop : ∀ x ∈ Ω, φ x ≠ ⊤)
    (hl : ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' Ω,
      DiscPshOn (fun t ↦ φ (c + t • v)) (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' Ω) z))
    (hu : ∀ m : ℕ, DiscPshOn (fun x => ((truncShift φ m x : ℝ) : EReal)) Ω) :
    DiscPshOn φ Ω := by
  have hψ : ∀ m : ℕ, DiscPshOn (fun x => max (φ x) ((-(m : ℝ) : ℝ) : EReal)) Ω := by
    intro m
    refine ((hu m).add (discPshOn_const ((-(m : ℝ) : ℝ) : EReal) (EReal.coe_ne_top _) _)).congr ?_
    intro x hx
    simp only
    rw [coe_truncShift (htop x hx), add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero,
      add_zero]
  refine ⟨htop, ?_, hasDiscSubmeanOn_of_line_sections hl⟩
  intro z hz b hb
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : EReal) < b := by
    induction b using EReal.rec with
    | bot => exact absurd hb not_lt_bot
    | coe b => exact ⟨b - 1, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
    | top => exact ⟨0, EReal.coe_lt_top 0⟩
  obtain ⟨m, hm⟩ := exists_nat_ge (-r)
  have hmb : ((-(m : ℝ) : ℝ) : EReal) < b :=
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by linarith)) hr
  have hz' : max (φ z) ((-(m : ℝ) : ℝ) : EReal) < b := max_lt hb hmb
  filter_upwards [(hψ m).upperSemicontinuousOn z hz b hz'] with y hy
  exact lt_of_le_of_lt (le_max_left _ _) hy

/-- **Theorem 1.1** (`pshd-vibe`). If an extended-real function without the
value `⊤` on an open set satisfies the disc criterion on every connected
component of every affine complex-line section, then it is upper
semicontinuous, hence plurisubharmonic.-/
theorem discPshOn_of_line_sections [FiniteDimensional ℂ E] {φ : E → EReal} {Ω : Set E}
    (hΩ : IsOpen Ω) (htop : ∀ x ∈ Ω, φ x ≠ ⊤)
    (hl : ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' Ω,
      DiscPshOn (fun t ↦ φ (c + t • v)) (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' Ω) z)) :
    DiscPshOn φ Ω :=
  discPshOn_of_line_sections_of_truncShift htop hl fun m =>
    LineSubharmonicOn.discPshOn_of_nonneg hΩ (fun x hx => truncShift_nonneg (htop x hx) m)
      (lineSubharmonicOn_truncShift htop hl m)

/-- **Theorem 1.1** (`pshd-vibe`), in the form of plurisubharmonic germs.-/
theorem plurisubharmonicOn_of_line_sections [FiniteDimensional ℂ E] {φ : E → EReal}
    {Ω : Set E} (hΩ : IsOpen Ω) (htop : ∀ x ∈ Ω, φ x ≠ ⊤)
    (hl : ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' Ω,
      DiscPshOn (fun t ↦ φ (c + t • v)) (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' Ω) z)) :
    UpperSemicontinuousOn φ Ω ∧ PlurisubharmonicOn φ Ω :=
  have h := discPshOn_of_line_sections hΩ htop hl
  ⟨h.upperSemicontinuousOn, h.plurisubharmonicOn hΩ⟩

end PshLines.PSHD
