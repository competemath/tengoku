import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.ErgodicTransitivity

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

def globalTail (h : ℤ) : Submodule ℂ GlobalHilbert :=
  ⨅ j : ℤ, ⨅ _ : j < h, (coordinateL2 j).ker

def sliceProjection (j : ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  (singleL2 j).comp (coordinateL2 j)

def residueClass (m t : ℕ) : Set Base := {x | residue m x = t}
lemma measurableSet_residueClass (m t : ℕ) : MeasurableSet (residueClass m t) :=
  measurableSet_eq_fun (measurable_residue m) measurable_const
lemma residueClass_nonnull {m t : ℕ} (ht : t < 2^m) : baseMeasure (residueClass m t) ≠ 0 := by
  change baseHaar {x : PadicInt 2 | twoResidue m x = t} ≠ 0
  have hcont : Continuous (twoResidue m) :=
    continuous_of_discreteTopology.comp (continuous_twoResidue m)
  have hOpen : IsOpen {x : PadicInt 2 | twoResidue m x = t} :=
    (isOpen_discrete ({t}:Set ℕ)).preimage hcont
  have hmem : twoResidue m (t : PadicInt 2) = t := by
    simp only [twoResidue, map_natCast]
    exact ZMod.val_natCast_of_lt ht
  exact (hOpen.measure_pos baseHaar ⟨(t : PadicInt 2),hmem⟩).ne'

def residueIndicator (m t : ℕ) : ScalarHilbert :=
  indicatorConstLp 2 (measurableSet_residueClass m t) (measure_ne_top baseMeasure _) (1:ℂ)
lemma residueIndicator_ae (m t : ℕ) : residueIndicator m t =ᵐ[baseMeasure]
    (residueClass m t).indicator (fun _ => (1:ℂ)) := indicatorConstLp_coeFn
lemma residueIndicator_ne_zero {m t : ℕ} (ht : t < 2^m) : residueIndicator m t ≠ 0 := by
  intro hz
  apply residueClass_nonnull ht
  rw [measure_eq_zero_iff_ae_notMem]
  have he := Lp.eq_zero_iff_ae_eq_zero.mp hz
  filter_upwards [he,residueIndicator_ae m t] with x hx hi
  intro hmem
  have h10 : (1:ℂ)=0 := by rw [← Set.indicator_of_mem hmem (fun _ => (1:ℂ)), ← hi]; exact hx
  exact one_ne_zero h10
lemma residueIndicator_orthogonal (m : ℕ) {s t : ℕ} (hst : s ≠ t) :
    inner ℂ (residueIndicator m s) (residueIndicator m t) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [residueIndicator_ae m s, residueIndicator_ae m t] with x hs ht
  rw [hs,ht]
  by_cases hxs : x ∈ residueClass m s
  · have hxt : x ∉ residueClass m t := fun hx => hst (hxs.symm.trans hx)
    simp [Set.indicator_of_notMem hxt]
  · simp [Set.indicator_of_notMem hxs]
lemma residueIndicator_independent (m : ℕ) :
    LinearIndependent ℂ (fun t : Fin (2^m) => residueIndicator m t) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro t; exact residueIndicator_ne_zero t.isLt
  · intro s t hst
    exact residueIndicator_orthogonal m (fun he => hst (Fin.ext he))
lemma scalarHilbert_infinite : ¬FiniteDimensional ℂ ScalarHilbert := by
  intro hfin
  let := hfin
  have hh := (residueIndicator_independent (Module.finrank ℂ ScalarHilbert + 1)).fintype_card_le_finrank
  simp only [Fintype.card_fin] at hh
  have hlt := Nat.lt_two_pow_self (n:=Module.finrank ℂ ScalarHilbert + 1)
  omega

lemma globalHilbert_infinite : ¬FiniteDimensional ℂ GlobalHilbert := by
  intro hfin
  let := hfin
  apply scalarHilbert_infinite
  apply FiniteDimensional.of_injective (singleL2 0).toLinearMap
  intro f g he
  have he' : singleL2 0 f = singleL2 0 g := he
  simpa only [coordinateL2_singleL2] using congrArg (coordinateL2 0) he'

end
end BackwardIntertwiners

end OAI
