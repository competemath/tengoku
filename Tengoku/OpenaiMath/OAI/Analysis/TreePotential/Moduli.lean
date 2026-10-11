import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.FiniteHeads

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section AsymptoticModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed finite-codimensional subspaces for asymptotic moduli. -/

structure ClosedFiniteCodim where
  space : Submodule ℝ E
  closed : IsClosed (space : Set E)
  finiteCodim : Module.Finite ℝ (E ⧸ space)

/-- We take these infima and suprema in the extended reals, so their definitions
    are meaningful without tacit boundedness side conditions. On infinite
    dimensional normed spaces their values at positive radii are finite. -/
def averagedModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1 ≤ ‖y‖},
      (((‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1 : ℝ) : EReal)

def oneSidedModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖ = 1},
      ((‖x.val + t • y.val‖ - 1 : ℝ) : EReal)

def IsAUC : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulus E t

end AsymptoticModuli

lemma ereal_le_of_forall_pos_sub_le (a : ℝ) (b : EReal)
    (h : ∀ ε : ℝ, 0 < ε → ((a - ε : ℝ) : EReal) ≤ b) : (a : EReal) ≤ b := by
  cases b using EReal.rec with
  | bot => exact ((EReal.bot_lt_coe (a - 1)).not_ge (h 1 zero_lt_one)).elim
  | coe b => exact EReal.coe_le_coe_iff.mpr (le_of_forall_pos_sub_le (fun ε hε =>
      EReal.coe_le_coe_iff.mp (h ε hε)))
  | top => exact le_top

lemma averagedModulus_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t b : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ F : ClosedFiniteCodim E,
      ∀ y : E, y ∈ F.space → 1 ≤ ‖y‖ →
        b - ε ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1) :
    (b : EReal) ≤ averagedModulus E t := by
  apply le_iInf
  intro x
  apply ereal_le_of_forall_pos_sub_le
  intro ε hε
  obtain ⟨F, hF⟩ := h x.val x.property ε hε
  apply le_iSup_of_le F
  apply le_iInf
  intro y
  exact EReal.coe_le_coe_iff.mpr (hF y.val y.property.1 y.property.2)

lemma midpoint_center_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x z y : E) (t : ℝ) :
    (‖z + t • y‖ + ‖z - t • y‖) / 2 ≤
      (‖x + t • y‖ + ‖x - t • y‖) / 2 + ‖z - x‖ := by
  have h1 := norm_sub_norm_le (z + t • y) (x + t • y)
  have h2 := norm_sub_norm_le (z - t • y) (x - t • y)
  have he1 : (z + t • y) - (x + t • y) = z - x := by abel
  have he2 : (z - t • y) - (x - t • y) = z - x := by abel
  rw [he1] at h1
  rw [he2] at h2
  linarith

lemma optimal_pair_parameters {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ a θ : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ θ ∧ θ ≤ 1/2 ∧ a^2 + θ^2 ≤ 1 ∧
      a + t * θ / 2 = Real.sqrt (1 + t^2/4) := by
  let d := Real.sqrt (4 + t^2)
  have hd : 0 < d := Real.sqrt_pos.2 (by positivity)
  have hd2 : d^2 = 4 + t^2 := Real.sq_sqrt (by positivity)
  have hdle : 2 ≤ d := by nlinarith
  refine ⟨2 / d, t / d, by positivity, (div_le_one hd).mpr hdle,
    by positivity, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · have he : (2 / d)^2 + (t / d)^2 = 1 := by
      field_simp
      nlinarith
    exact he.le
  · have he : 2 / d + t * (t / d) / 2 = d / 2 := by
      field_simp
      nlinarith
    rw [he]
    have hs : (d / 2)^2 = 1 + t^2 / 4 := by nlinarith
    rw [← hs, Real.sqrt_sq (by positivity)]

section TestSeparable
open scoped Classical
variable {I : Type*}

def testVectorBasis (K : TestFamily I) : Module.Basis I ℝ (TestVector K) :=
  Finsupp.basisSingleOne.map (testVectorEquiv K).symm

end TestSeparable

namespace TreeCalculus
open scoped Classical

end TreeCalculus

end BoundedTreePotentials

end

end OAI
