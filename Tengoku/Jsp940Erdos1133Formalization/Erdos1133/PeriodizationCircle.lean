import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Periodization
import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.PrivalovProbe

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators
open Erdos1152.V5

namespace Erdos1133

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem exists_circle_of_finite_expansion (F : ℂ → ℂ) (T : ℝ) (m : ℕ)
    (c : ℤ → ℂ)
    (he : ∀ x : ℝ, F x=∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ),
      c j*Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(x:ℂ)/(T:ℂ))) :
    ∃ P : CircleFunction, P ∈ bandSpace m ∧
      ∀ x : ℝ, P ((2*Real.pi*x/T : ℝ) : FourierCircle)=F x := by
  refine ⟨finiteFourier (Finset.Icc (-(m:ℤ)) (m:ℤ)) c, ?_, ?_⟩
  · unfold finiteFourier
    apply Submodule.sum_mem
    intro j hj
    exact (bandSpace m).smul_mem (c j) (character_mem_spectrum (Finset.mem_Icc.mp hj))
  · intro x
    rw [finiteFourier_apply, he x]
    apply Finset.sum_congr rfl
    intro j _
    rw [character_coe]
    congr 2
    push_cast
    ring

theorem periodize_circle_of_bandwidth_le (g : ℂ → ℂ) {C σ T : ℝ} {m : ℕ}
    (hd : Differentiable ℂ g) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (hm : periodizationBandwidth σ T ≤ m) :
    ∃ P : CircleFunction, P ∈ bandSpace m ∧
      ∀ x : ℝ, P ((2*Real.pi*x/T : ℝ) : FourierCircle)=periodize g T x := by
  let : Fact (0 < T) := ⟨hT⟩
  obtain ⟨c,hc⟩ := periodize_finite_expansion g (T := T) hd hC hσ hg
  obtain ⟨P,hP,hPe⟩ := exists_circle_of_finite_expansion (periodize g T) T
    (periodizationBandwidth σ T) c hc
  refine ⟨P, ?_, hPe⟩
  apply spectrum_mono (t := Set.Icc (-(m:ℤ)) m) _ hP
  intro j hj
  simp only [Set.mem_Icc] at *
  constructor <;> omega

/-- Every circle argument has a representative in the normalized physical scale.-/
theorem normalized_circle_surjective {T : ℝ} (hT : T ≠ 0) :
    Function.Surjective (fun x : ℝ => ((2*Real.pi*x/T : ℝ) : FourierCircle)) := by
  intro u
  let t := AddCircle.equivIco (2*Real.pi) (-Real.pi) u
  refine ⟨(t:ℝ)*T/(2*Real.pi), ?_⟩
  dsimp only
  have he : 2*Real.pi*((t:ℝ)*T/(2*Real.pi))/T=(t:ℝ) := by field_simp
  rw [he]
  exact (AddCircle.equivIco (2*Real.pi) (-Real.pi)).symm_apply_apply u

theorem circle_norm_le_of_physical {P : CircleFunction} {T B : ℝ} (hT : T ≠ 0)
    (hB : 0 ≤ B)
    (hb : ∀ x : ℝ, ‖P ((2*Real.pi*x/T : ℝ) : FourierCircle)‖ ≤ B) : ‖P‖ ≤ B := by
  apply (ContinuousMap.norm_le P hB).mpr
  intro u
  obtain ⟨x,rfl⟩ := normalized_circle_surjective hT u
  exact hb x

end Erdos1133
