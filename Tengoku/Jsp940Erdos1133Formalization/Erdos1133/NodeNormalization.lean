import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.CircleInterpolation
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set Finset
open Erdos1152.V5

namespace Erdos1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Physical points in one period of length `2 * r` viewed on the Fourier circle.-/
def normalizeNode (r x : ℝ) : FourierCircle := ((Real.pi * x / r : ℝ) : FourierCircle)

theorem normalizeNode_angle_mem {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ico (-r) r) :
    Real.pi * x / r ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
  constructor
  · apply (le_div_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le]
  · apply (div_lt_iff₀ hr).mpr
    nlinarith [mul_lt_mul_of_pos_left hx.2 Real.pi_pos]

theorem normalizeNode_injOn {r : ℝ} (hr : 0 < r) :
    Set.InjOn (normalizeNode r) (Ico (-r) r) := by
  intro x hx y hy hxy
  have heq : Real.pi * x / r = Real.pi * y / r :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (normalizeNode_angle_mem hr hx) (normalizeNode_angle_mem hr hy)).mp hxy
  have hm : Real.pi * x = Real.pi * y := (div_left_inj' hr.ne').mp heq
  nlinarith [Real.pi_pos]

def normalizedNodes (r : ℝ) (Γ : Finset ℝ) : Finset FourierCircle :=
  Γ.image (normalizeNode r)

theorem normalizedNodes_card {r : ℝ} (hr : 0 < r) (Γ : Finset ℝ)
    (hΓ : ∀ x ∈ Γ, x ∈ Ico (-r) r) : (normalizedNodes r Γ).card = Γ.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  exact normalizeNode_injOn hr (hΓ x hx) (hΓ y hy) hxy

theorem mem_normalizedNodes_iff {r : ℝ} {Γ : Finset ℝ} {z : FourierCircle} :
    z ∈ normalizedNodes r Γ ↔ ∃ x ∈ Γ, normalizeNode r x = z := by
  exact Finset.mem_image

theorem normalizeNode_mem_normalizedNodes_iff {r : ℝ} (hr : 0 < r)
    (Γ : Finset ℝ) (hΓ : ∀ x ∈ Γ, x ∈ Ico (-r) r)
    {x : ℝ} (hx : x ∈ Ico (-r) r) :
    normalizeNode r x ∈ normalizedNodes r Γ ↔ x ∈ Γ := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := mem_normalizedNodes_iff.mp h
    have : y = x := normalizeNode_injOn hr (hΓ y hy) hx heq
    simpa [this] using hy
  · intro hxΓ
    exact mem_normalizedNodes_iff.mpr ⟨x, hxΓ, rfl⟩

theorem contracted_node_mem_period {r β x : ℝ} (hr : 0 < r) (hβ : β < 1)
    (hx : x ∈ Icc (-β * r) (β * r)) : x ∈ Ico (-r) r := by
  have hsmall : β * r < r := by nlinarith
  constructor <;> nlinarith [hx.1, hx.2]

def indexedRealNodes {k : ℕ} (t : Fin k → ℝ) : Finset ℝ := univ.image t

theorem indexedRealNodes_card {k : ℕ} {t : Fin k → ℝ} (ht : Function.Injective t) :
    (indexedRealNodes t).card = k := by
  simpa [indexedRealNodes] using Finset.card_image_of_injective univ ht

theorem mem_indexedRealNodes {k : ℕ} {t : Fin k → ℝ} {x : ℝ} :
    x ∈ indexedRealNodes t ↔ ∃ i, t i = x := by
  simp [indexedRealNodes]

theorem indexedRealNodes_mem_period {r β : ℝ} {k : ℕ}
    (hr : 0 < r) (hβ : β < 1) (t : Fin k → ℝ)
    (ht : ∀ i, t i ∈ Icc (-β * r) (β * r)) :
    ∀ x ∈ indexedRealNodes t, x ∈ Ico (-r) r := by
  intro x hx
  obtain ⟨i, rfl⟩ := mem_indexedRealNodes.mp hx
  exact contracted_node_mem_period hr hβ (ht i)

theorem normalized_indexed_card {r β : ℝ} {k : ℕ}
    (hr : 0 < r) (hβ : β < 1) (t : Fin k → ℝ) (hi : Function.Injective t)
    (ht : ∀ i, t i ∈ Icc (-β * r) (β * r)) :
    (normalizedNodes r (indexedRealNodes t)).card = k := by
  rw [normalizedNodes_card hr _ (indexedRealNodes_mem_period hr hβ t ht)]
  exact indexedRealNodes_card hi

theorem normalizeNode_comp_injective {r β : ℝ} {k : ℕ}
    (hr : 0 < r) (hβ : β < 1) (t : Fin k → ℝ) (hi : Function.Injective t)
    (ht : ∀ i, t i ∈ Icc (-β * r) (β * r)) :
    Function.Injective (fun i => normalizeNode r (t i)) := by
  intro i j hij
  apply hi
  exact normalizeNode_injOn hr (contracted_node_mem_period hr hβ (ht i))
    (contracted_node_mem_period hr hβ (ht j)) hij

theorem normalized_indexed_mem_iff {r : ℝ} {k : ℕ} {t : Fin k → ℝ}
    {z : FourierCircle} :
    z ∈ normalizedNodes r (indexedRealNodes t) ↔ ∃ i, normalizeNode r (t i) = z := by
  simp [normalizedNodes, indexedRealNodes, Finset.mem_image]

end Erdos1133
