import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.MultipeakPeriodTail
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.PeriodizationCircle
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.NodeNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators Real
open Finset Set Erdos1152.V5
namespace Erdos1133
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A separated family of genuine local packets yields arbitrarily signed
peaks in the original trigonometric band, with unit data at every node.
@isnad1 id=ex.16h13v.s10.de47926a7f13 from=translated src=- shape=a3a2ca6f vocab=27beb492
-/
theorem SparsePacketFamily.periodized_peaks
    {Γ : Finset ℝ} {s : Finset ℤ} {c : ℤ → ℝ} {A B ρ σ M C D : ℝ}
    (F : SparsePacketFamily Γ s c B ρ σ M C) (n : ℕ) (hn : 0 < n)
    (hs : s.Nonempty) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hσπ : σ ≤ Real.pi)
    (hD : 1 ≤ D) (hgap : 2*ρ ≤ D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-(n:ℝ)+2*D) ((n:ℝ)-2*D))
    (hnodebound : ∀ x ∈ Γ, |x| ≤ n)
    (hpeakbound : ∀ j ∈ s, |F.p j| ≤ n)
    (hbudget : (4*C/D^2)*squareTailMass ≤ 1)
    (hperiodbudget : (C/D^2)*squareTailMass^2 ≤ 1)
    (hBA : 3*A+2 < B) (ψ : ℤ → ℝ) (hψ : ∀ i, |ψ i|=1) :
    ∃ φ : CircleFunction, φ ∈ bandSpace n ∧ (∀ x, (φ x).im=0) ∧
      (∀ x ∈ normalizedNodes n Γ, ‖φ x‖ ≤ 1) ∧
      ∀ j ∈ s, A < ψ j*(φ (normalizeNode n (F.p j))).re := by
  classical
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hT : 0 < 2*(n:ℝ) := by positivity
  have hD0 : 0 < D := by linarith
  let G := signedPacketSum s ψ F.g
  let C₀ := ∑ i ∈ s, C*(1+|c i|)^6
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun i hi => by positivity)
  have hdec : ∀ z : ℂ, ‖G z‖ ≤ C₀*Real.exp (σ*|z.im|)/(1+‖z‖)^6 :=
    signedPacketSum_decay s c ψ F.g hC (fun i _ => hψ i) F.decay
  have hband : periodizationBandwidth σ (2*(n:ℝ)) ≤ n := by
    apply periodizationBandwidth_le
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hσπ hnr.le]
  obtain ⟨P,hP,hPe⟩ := periodize_circle_of_bandwidth_le G
    (signedPacketSum_entire s ψ F.g F.entire) hC₀ hσ hT hdec hband
  have hPe' (x : ℝ) : P (normalizeNode n x)=periodize G (2*(n:ℝ)) x := by
    have he : 2*Real.pi*x/(2*(n:ℝ))=Real.pi*x/n := by ring
    simpa only [he,normalizeNode] using hPe x
  have hPr : ∀ x, (P x).im=0 := by
    intro x
    obtain ⟨t,rfl⟩ := normalized_circle_surjective hT.ne' x
    rw [hPe]
    exact periodize_real G (signedPacketSum_real s ψ F.g F.real) hC₀ hσ hT hdec t
  have herr (x : ℝ) (hx : |x| ≤ n) : ‖P (normalizeNode n x)-G x‖ ≤ 1 := by
    rw [hPe']
    exact (multipeak_periodize_error s c ψ F.g hC hD hbound horder
      (fun i _ => hψ i) F.real_decay x hx).trans hperiodbudget
  obtain ⟨_,hnodes,hpeaks⟩ := F.signed_estimates hs hC hD0 hgap hsep
    hbudget ψ (fun i _ => hψ i)
  let φ : CircleFunction := (1/3:ℂ) • P
  have hφe (x : FourierCircle) : φ x=(1/3:ℂ)*P x := rfl
  refine ⟨φ,(bandSpace n).smul_mem (1/3:ℂ) hP,?_,?_,?_⟩
  · intro x
    rw [hφe,Complex.mul_im,hPr]
    norm_num
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := mem_normalizedNodes_iff.mp hx
    have hb : ‖P (normalizeNode n t)‖ ≤ 3 := by
      calc
        _ ≤ ‖P (normalizeNode n t)-G t‖+‖G t‖ := by simpa [add_comm] using norm_le_insert' (P (normalizeNode n t)) (G t)
        _ ≤ 1+2 := add_le_add (herr t (hnodebound t ht)) (hnodes t ht)
        _ = 3 := by norm_num
    rw [hφe,norm_mul]
    norm_num
    linarith
  · intro j hj
    have he := herr (F.p j) (hpeakbound j hj)
    have hre : |(P (normalizeNode n (F.p j))).re-(G (F.p j)).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans he
    have hsigned : |ψ j*((P (normalizeNode n (F.p j))).re-(G (F.p j)).re)| ≤ 1 := by
      simpa only [abs_mul,hψ,one_mul] using hre
    have hpk := hpeaks j hj
    have hlower := (abs_le.mp hsigned).1
    rw [hφe,Complex.mul_re]
    norm_num
    nlinarith

end Erdos1133
