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

/--
@isnad1 id=mem.2h2v.s6.e42e53ad7bbe from=translated src=- shape=b58befad vocab=dc38bfb6
-/
theorem normalizeNode_angle_mem {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ico (-r) r) :
    Real.pi * x / r ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
  constructor
  · apply (le_div_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le]
  · apply (div_lt_iff₀ hr).mpr
    nlinarith [mul_lt_mul_of_pos_left hx.2 Real.pi_pos]

/--
@isnad1 id=injon.1h1v.s4.45742dc38509 from=translated src=- shape=33a99ba5 vocab=3247ca64
-/
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

/--
@isnad1 id=eq.2h2v.s5.1aabbc7666c2 from=translated src=- shape=5e0da472 vocab=230bbcde
-/
theorem normalizedNodes_card {r : ℝ} (hr : 0 < r) (Γ : Finset ℝ)
    (hΓ : ∀ x ∈ Γ, x ∈ Ico (-r) r) : (normalizedNodes r Γ).card = Γ.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  exact normalizeNode_injOn hr (hΓ x hx) (hΓ y hy) hxy

/--
@isnad1 id=iff.0h3v.s5.7093d032747d from=translated src=- shape=dfd3d406 vocab=de325993
-/
theorem mem_normalizedNodes_iff {r : ℝ} {Γ : Finset ℝ} {z : FourierCircle} :
    z ∈ normalizedNodes r Γ ↔ ∃ x ∈ Γ, normalizeNode r x = z := by
  exact Finset.mem_image

/--
@isnad1 id=iff.3h3v.s6.7d835d3bfd5a from=translated src=- shape=53e0b02a vocab=660b2f64
-/
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

/--
@isnad1 id=mem.3h3v.s6.6bd28a745417 from=translated src=- shape=332ddd39 vocab=df3eb6a7
-/
theorem contracted_node_mem_period {r β x : ℝ} (hr : 0 < r) (hβ : β < 1)
    (hx : x ∈ Icc (-β * r) (β * r)) : x ∈ Ico (-r) r := by
  have hsmall : β * r < r := by nlinarith
  constructor <;> nlinarith [hx.1, hx.2]

def indexedRealNodes {k : ℕ} (t : Fin k → ℝ) : Finset ℝ := univ.image t

/--
@isnad1 id=eq.1h2v.s4.4029f556e7e1 from=translated src=- shape=2eceedcb vocab=7299d3c6
-/
theorem indexedRealNodes_card {k : ℕ} {t : Fin k → ℝ} (ht : Function.Injective t) :
    (indexedRealNodes t).card = k := by
  simpa [indexedRealNodes] using Finset.card_image_of_injective univ ht

/--
@isnad1 id=iff.0h3v.s5.4ebbef9b80c5 from=translated src=- shape=82cae55c vocab=6b8f4c8b
-/
theorem mem_indexedRealNodes {k : ℕ} {t : Fin k → ℝ} {x : ℝ} :
    x ∈ indexedRealNodes t ↔ ∃ i, t i = x := by
  simp [indexedRealNodes]

/--
@isnad1 id=mem.4h5v.s6.03852d086354 from=translated src=- shape=e85240b8 vocab=d34f1516
-/
theorem indexedRealNodes_mem_period {r β : ℝ} {k : ℕ}
    (hr : 0 < r) (hβ : β < 1) (t : Fin k → ℝ)
    (ht : ∀ i, t i ∈ Icc (-β * r) (β * r)) :
    ∀ x ∈ indexedRealNodes t, x ∈ Ico (-r) r := by
  intro x hx
  obtain ⟨i, rfl⟩ := mem_indexedRealNodes.mp hx
  exact contracted_node_mem_period hr hβ (ht i)

/--
@isnad1 id=eq.4h4v.s6.26a508dca688 from=translated src=- shape=2f58669c vocab=7da83cf5
-/
theorem normalized_indexed_card {r β : ℝ} {k : ℕ}
    (hr : 0 < r) (hβ : β < 1) (t : Fin k → ℝ) (hi : Function.Injective t)
    (ht : ∀ i, t i ∈ Icc (-β * r) (β * r)) :
    (normalizedNodes r (indexedRealNodes t)).card = k := by
  rw [normalizedNodes_card hr _ (indexedRealNodes_mem_period hr hβ t ht)]
  exact indexedRealNodes_card hi

/--
@isnad1 id=injectiv.4h4v.s6.018761c6238a from=translated src=- shape=e4af26e4 vocab=70369160
-/
theorem normalizeNode_comp_injective {r β : ℝ} {k : ℕ}
    (hr : 0 < r) (hβ : β < 1) (t : Fin k → ℝ) (hi : Function.Injective t)
    (ht : ∀ i, t i ∈ Icc (-β * r) (β * r)) :
    Function.Injective (fun i => normalizeNode r (t i)) := by
  intro i j hij
  apply hi
  exact normalizeNode_injOn hr (contracted_node_mem_period hr hβ (ht i))
    (contracted_node_mem_period hr hβ (ht j)) hij

/--
@isnad1 id=iff.0h4v.s5.21967b8029f8 from=translated src=- shape=0f49df1f vocab=2629a0d2
-/
theorem normalized_indexed_mem_iff {r : ℝ} {k : ℕ} {t : Fin k → ℝ}
    {z : FourierCircle} :
    z ∈ normalizedNodes r (indexedRealNodes t) ↔ ∃ i, normalizeNode r (t i) = z := by
  simp [normalizedNodes, indexedRealNodes, Finset.mem_image]

end Erdos1133
