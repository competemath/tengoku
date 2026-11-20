import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Multipeak
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Phase
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.PeakSigns

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators Real
open Finset Set Erdos1152.V5

namespace Erdos1133
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Convert actual freely signed peaks into bad data for every degree below
the oscillation threshold. The chosen data are independent of that degree.-/
theorem finite_trig_obstruction_of_peaks (N : ℕ) (Γ : Finset FourierCircle)
    (hΓ : Γ.card=2*N) (s : Finset ℤ) (hs : s.Nonempty) (t : ℤ → ℝ)
    (ht : ∀ i ∈ s, ∀ j ∈ s, i<j → t i<t j)
    (htbounds : ∀i∈s,t i∈Ioo (-Real.pi) Real.pi)
    (htΓ : ∀i∈s,(t i:FourierCircle)∉Γ)
    (A : ℝ) (hA : 0<A)
    (hpeaks : ∀ψ:ℤ→ℝ,(∀i,|ψ i|=1)→∃φ:CircleFunction,
      φ∈bandSpace N ∧ (∀x,(φ x).im=0) ∧ (∀x∈Γ,‖φ x‖≤1) ∧
      ∀i∈s,A<ψ i*(φ (t i:FourierCircle)).re) :
    ∃y:FourierCircle→ℝ,(∀x∈Γ,|y x|≤1) ∧
      ∀ m : ℕ, N ≤ m → 2 * (m - N) < s.card - 1 → ∀ H : CircleFunction,
        H ∈ bandSpace m → (∀ x, (H x).im = 0) → ‖H‖ ≤ A →
        ∃x∈Γ,(H x).re≠y x := by
  classical
  obtain ⟨phase,hphase0,hphase⟩ := circleNodeProduct_exists_real_phase N Γ hΓ
  let v : ℤ→ℝ := fun i => (phase*circleNodeProduct N Γ (t i:FourierCircle)).re
  have hv : ∀i∈s,v i≠0 := by
    intro i hi hzero
    have he : phase*circleNodeProduct N Γ (t i:FourierCircle)=0 :=
      Complex.ext hzero (hphase _)
    have hp0 : circleNodeProduct N Γ (t i:FourierCircle)≠0 := by
      intro hz
      exact htΓ i hi ((circleNodeProduct_eq_zero_iff N Γ _).mp hz)
    exact mul_ne_zero hphase0 hp0 he
  let k := s.card-1
  have hscard : s.card=k+1 := by
    have := Finset.card_pos.mpr hs
    dsimp [k]
    omega
  obtain ⟨ψ,hψ,halt⟩ := choose_alternating_peak_signs s hscard v hv
  obtain ⟨φ,hφ,hφr,hφnodes,hφpeak⟩ := hpeaks ψ hψ
  refine ⟨fun x => (φ x).re,fun x hx => (Complex.abs_re_le_norm _).trans (hφnodes x hx),?_⟩
  intro m hNm hm H hH hHr hHnorm
  by_contra hnone
  push Not at hnone
  have hsame : ∀x∈Γ,H x=φ x := by
    intro x hx
    exact Complex.ext (hnone x hx) (by rw [hHr,hφr])
  let q : Fin (k+1)→ℝ := fun i => t (s.orderEmbOfFin hscard i)
  have hq : StrictMono q := by
    intro i j hij
    exact ht _ (s.orderEmbOfFin_mem hscard i) _ (s.orderEmbOfFin_mem hscard j)
      ((s.orderEmbOfFin hscard).strictMono hij)
  have hqspan : q (Fin.last k)-q 0<2*Real.pi := by
    have hl := htbounds _ (s.orderEmbOfFin_mem hscard (Fin.last k))
    have hr := htbounds _ (s.orderEmbOfFin_mem hscard 0)
    dsimp [q]
    linarith [hl.2,hr.1]
  have hsmall : ∀ i : Fin (k+1), |(H (q i:FourierCircle)).re| < |(φ (q i:FourierCircle)).re| := by
    intro i
    have hp := hφpeak _ (s.orderEmbOfFin_mem hscard i)
    have hψp : ψ (s.orderEmbOfFin hscard i)*(φ (q i:FourierCircle)).re ≤
        |(φ (q i:FourierCircle)).re| := by
      calc
        _ ≤ |ψ (s.orderEmbOfFin hscard i)*(φ (q i:FourierCircle)).re| := le_abs_self _
        _ = _ := by rw [abs_mul,hψ,one_mul]
    exact (Complex.abs_re_le_norm _).trans
      ((ContinuousMap.norm_coe_le_norm H (q i:FourierCircle)).trans hHnorm) |>.trans_lt
        (hp.trans_le hψp)
  have hsign := halt (fun i => (φ (t i:FourierCircle)).re)
    (fun i hi => hA.trans (hφpeak i hi))
  have hbound := interpolant_peak_oscillations_le hNm Γ hΓ φ H hφ hH hφr hHr hsame
    phase hphase0 hphase q hq hqspan
    (fun i => htΓ _ (s.orderEmbOfFin_mem hscard i)) hsmall hsign
  exact (not_lt_of_ge hbound) hm

end Erdos1133
