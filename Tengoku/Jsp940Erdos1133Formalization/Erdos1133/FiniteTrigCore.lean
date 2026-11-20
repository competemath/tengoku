import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.TrigMultipeak
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.PeriodizedPeaks
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.SparseCells
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.SpacingBudget

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators Real
open Finset Set Erdos1152.V5
namespace Erdos1133
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Arbitrary nodes admit bounded real data that cannot be interpolated with
a fixed uniform bound, even after adding a positive proportion of frequencies.-/
theorem finite_trig_obstruction :
    ∀ A > (0:ℝ), ∃ δ > (0:ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ Γ : Finset ℝ, (∀ x ∈ Γ, x ∈ Ico (-(n:ℝ)) n) → Γ.card=2*n →
    ∃ y : ℝ → ℝ, (∀ x ∈ Γ, |y x| ≤ 1) ∧
      ∀ m : ℕ, n ≤ m → (m:ℝ) ≤ n+δ*n →
      ∀ H : CircleFunction, H ∈ bandSpace m → (∀ x, (H x).im=0) → ‖H‖ ≤ A →
      ∃ x ∈ Γ, (H ((Real.pi*x/n:ℝ):FourierCircle)).re ≠ y x := by
  classical
  intro A hA
  let B := 3*A+4
  have hB : 1 < B := by dsimp [B]; linarith
  obtain ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,hpackets⟩ := sparse_packet_family_exists B hB
  obtain ⟨K,hK,hD,hgap,hbudget,hperiodbudget⟩ :=
    exists_packet_spacing C squareTailMass hC squareTailMass_nonneg ρ
  let D : ℝ := ((2*ρ+1)*K : ℕ)
  change 1 ≤ D at hD
  change 2*(ρ:ℝ) < D at hgap
  change (4*C/D^2)*squareTailMass ≤ 1 at hbudget
  change (C/D^2)*squareTailMass^2 ≤ 1 at hperiodbudget
  have hD0 : 0 < D := by linarith
  obtain ⟨η,hη,N₀,hcells⟩ := separated_sparse_cells ρ K hK
  obtain ⟨δ,hδ,n₀,hcount⟩ := exists_strict_zero_budget η hη
  refine ⟨δ,hδ,max (max N₀ n₀) 1,?_⟩
  intro n hn Γ hΓrange hΓcard
  have hnN : N₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnn : n₀ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnpos : 0 < n := by have := (le_max_right (max N₀ n₀) 1).trans hn; omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hnpos
  obtain ⟨s,c,hs,hcard,habs,hinterior,hsparse,horiented⟩ := hcells n hnN Γ hΓcard.le
  obtain ⟨F⟩ := hpackets Γ s c hsparse
  have hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i| :=
    fun i _ j _ => (habs i j).le
  have horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i :=
    fun i _ j _ _ => (horiented i j).symm.le
  have hcenters : ∀ i ∈ s, ∀ j ∈ s, i < j → D ≤ c j-c i := by
    intro i hi j hj hij
    have hdij : (1:ℝ) ≤ ((j-i:ℤ):ℝ) := by exact_mod_cast (show (1:ℤ) ≤ j-i by omega)
    have he : c j-c i = D*((j-i:ℤ):ℝ) := horiented i j
    rw [he]
    nlinarith
  have hpbound : ∀ j ∈ s, F.p j ∈ Ioo (-(n:ℝ)) n := by
    intro j hj
    have hc := hinterior j hj
    have hp := abs_le.mp (F.near j hj)
    change -(n:ℝ)+2*D ≤ c j ∧ c j ≤ (n:ℝ)-2*D at hc
    constructor <;> linarith
  have hpmono : ∀ i ∈ s, ∀ j ∈ s, i < j → F.p i < F.p j := by
    intro i hi j hj hij
    have hc := hcenters i hi j hj hij
    have hp := abs_le.mp (F.near i hi)
    have hq := abs_le.mp (F.near j hj)
    linarith
  let t : ℤ → ℝ := fun j => Real.pi*F.p j/n
  have ht : ∀ i ∈ s, ∀ j ∈ s, i < j → t i < t j := by
    intro i hi j hj hij
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (hpmono i hi j hj hij) Real.pi_pos) hnr
  have htb : ∀ j ∈ s, t j ∈ Ioo (-Real.pi) Real.pi := by
    intro j hj
    have hp := hpbound j hj
    constructor
    · apply (lt_div_iff₀ hnr).mpr
      nlinarith [mul_lt_mul_of_pos_left hp.1 Real.pi_pos]
    · apply (div_lt_iff₀ hnr).mpr
      nlinarith [mul_lt_mul_of_pos_left hp.2 Real.pi_pos]
  have hpΓ : ∀ j ∈ s, F.p j ∉ Γ := by
    intro j hj
    exact peak_not_mem_nodes Γ (F.g j) (F.p j) (F.nodes j hj) (hB.trans_le (F.peak j hj))
  have htΓ : ∀ j ∈ s, (t j:FourierCircle) ∉ normalizedNodes n Γ := by
    intro j hj hmem
    have hx := hpbound j hj
    exact hpΓ j hj ((normalizeNode_mem_normalizedNodes_iff hnr Γ hΓrange ⟨hx.1.le,hx.2⟩).mp hmem)
  have hnormcard : (normalizedNodes n Γ).card=2*n :=
    (normalizedNodes_card hnr Γ hΓrange).trans hΓcard
  have hpeaks : ∀ ψ : ℤ → ℝ, (∀ i, |ψ i|=1) →
      ∃ φ : CircleFunction, φ ∈ bandSpace n ∧ (∀ x, (φ x).im=0) ∧
        (∀ x ∈ normalizedNodes n Γ, ‖φ x‖ ≤ 1) ∧
        ∀ j ∈ s, A < ψ j*(φ (t j:FourierCircle)).re := by
    intro ψ hψ
    apply F.periodized_peaks n hnpos hs hC.le hσ.le hσπ.le hD hgap.le hsep horder
      hinterior
    · intro x hx
      exact abs_le.mpr ⟨(hΓrange x hx).1,(hΓrange x hx).2.le⟩
    · intro j hj
      exact abs_le.mpr ⟨(hpbound j hj).1.le,(hpbound j hj).2.le⟩
    · exact hbudget
    · exact hperiodbudget
    · dsimp [B]; linarith
    · exact hψ
  obtain ⟨y,hy,hbad⟩ := finite_trig_obstruction_of_peaks n (normalizedNodes n Γ)
    hnormcard s hs t ht htb htΓ A hA hpeaks
  refine ⟨fun x => y (normalizeNode n x),?_,?_⟩
  · intro x hx
    exact hy _ (mem_normalizedNodes_iff.mpr ⟨x,hx,rfl⟩)
  · intro m hnm hm H hH hHr hHnorm
    obtain ⟨z,hz,hneq⟩ := hbad m hnm (hcount n hnn s.card m hcard hnm hm) H hH hHr hHnorm
    obtain ⟨x,hx,rfl⟩ := mem_normalizedNodes_iff.mp hz
    exact ⟨x,hx,hneq⟩

end Erdos1133
