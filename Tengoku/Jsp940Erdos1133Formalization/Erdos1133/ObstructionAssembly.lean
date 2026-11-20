import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.IndexedObstruction
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.ExactInterpolation
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.AnalyticParameters
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.EntireToTrig

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set
open Erdos1152.V5

namespace Erdos1133

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- Full finite trigonometric obstruction; the data are independent of the
allowed degree. This is the common interface between the two analytic halves.-/
def TrigObstructionAt (A δ : ℝ) (n : ℕ) : Prop :=
  ∀ Γ : Finset ℝ, (∀ x ∈ Γ, x ∈ Ico (-(n : ℝ)) n) → Γ.card = 2*n →
    ∃ y : ℝ → ℝ, (∀ x ∈ Γ, |y x| ≤ 1) ∧
      ∀ m : ℕ, n ≤ m → (m : ℝ) ≤ n+δ*n →
        ∀ P : CircleFunction, P ∈ bandSpace m → (∀ u, (P u).im=0) →
          ‖P‖ ≤ A → ∃ x ∈ Γ, (P ((Real.pi*x/n : ℝ) : FourierCircle)).re ≠ y x

def FiniteTrigObstructions : Prop :=
  ∀ A > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → TrigObstructionAt A δ n

/-- Exact assembly of the contradiction. Both analytic inputs remain named
hypotheses here and are discharged by the final theorem, not asserted as axioms.-/
theorem centered_obstruction_of_trig_and_approx
    {H A δ τ K q : ℝ} {n m : ℕ}
    (hτ : 0 < τ) (hτn : τ < (n : ℝ))
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1) (hKA : K/(1-q) ≤ A)
    (hNm : n ≤ m) (hm : (m : ℝ) ≤ n+δ*n)
    (htrig : TrigObstructionAt A δ n)
    (happrox : ∀ t : Fin (2*n) → ℝ, Function.Injective t →
      (∀ i, t i ∈ Icc (-τ) τ) →
      (∀ d : Fin (2*n) → ℝ, (∀ i, |d i| ≤ 1) →
        ∃ f : ℂ → ℂ,
          IsBernsteinFunction (Real.pi*((((2*n : ℕ) : ℝ)+1)/(2*τ))) H f ∧
          ∀ i, f (t i)=(d i : ℂ)) →
      ∀ d : Fin (2*n) → ℝ, ‖d‖ ≤ 1 →
        ∃ P : CircleFunction, P ∈ bandSpace m ∧ (∀ u, (P u).im=0) ∧
          ‖P‖ ≤ K ∧ ∀ i, |(P ((Real.pi*t i/n : ℝ) : FourierCircle)).re-d i| ≤ q) :
    CenteredIntervalRealBernsteinObstruction H (2*n) (2*τ) := by
  classical
  intro t ht hloc
  have htloc : ∀ i, t i ∈ Icc (-τ) τ := by
    intro i
    obtain ⟨hl,hu⟩ := hloc i
    constructor <;> linarith
  by_contra hno
  push Not at hno
  have hinterp : ∀ d : Fin (2*n) → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ,
        IsBernsteinFunction (Real.pi*((((2*n : ℕ) : ℝ)+1)/(2*τ))) H f ∧
        ∀ i, f (t i)=(d i : ℂ) := by
    intro d hd
    obtain ⟨f,hf,hfr,hfi⟩ := hno (fun i => ⟨d i,abs_le.mp (hd i)⟩)
    exact ⟨f,hf,hfi⟩
  let Γ : Finset ℝ := Finset.univ.image t
  have hΓcard : Γ.card = 2*n := by
    simp [Γ,Finset.card_image_of_injective _ ht]
  have hΓloc : ∀ x ∈ Γ, x ∈ Ico (-(n : ℝ)) n := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hil,hir⟩ := htloc i
    constructor <;> linarith
  obtain ⟨y,hy,hybad⟩ := htrig Γ hΓloc hΓcard
  let d : Fin (2*n) → ℝ := fun i => y (t i)
  have hd : ‖d‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    exact hy (t i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  obtain ⟨P,hPb,hPr,hPd,hPK⟩ := exact_unit_real_trig_interpolation
    (fun i : Fin (2*n) => ((Real.pi*t i/n : ℝ) : FourierCircle))
    m K q hK hq hq1 (happrox t ht htloc hinterp) d hd
  obtain ⟨x,hx,hbad⟩ := hybad m hNm hm P hPb hPr (hPK.trans hKA)
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  apply hbad
  exact congrArg Complex.re (hPd i)

/-- Every parameter in the window argument is chosen here. In particular the
window constants are fixed before the degree slack, avoiding a circular choice.-/
theorem finiteBernsteinObstructions_of_finiteTrig
    (htrig : FiniteTrigObstructions) :
    ∀ H > (0 : ℝ), ∃ k : ℕ, 2 ≤ k ∧ FiniteBernsteinObstruction H k := by
  intro H hH
  obtain ⟨η,hη,hwindow⟩ := plateauWindow_uniform_positive
  let ρ : ℝ := η/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let K : ℝ := (H/ρ)*(2*Real.pi)+1/2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨δ,hδ,n₀,hfinite⟩ := htrig (2*K) (by positivity)
  let β := interiorRatio δ
  let α := plateauRate δ
  have hβ : 0 < β := interiorRatio_pos hδ
  have hβ1 : β < 1 := interiorRatio_lt_one hδ
  have hα : 0 < α := plateauRate_pos hδ
  obtain ⟨R,hR1,hR⟩ := exists_large_plateauPeriodError
    (H := H/ρ) hα hβ.le hβ1 (by positivity) (show (0 : ℝ) < 1/2 by norm_num)
  obtain ⟨n,hn⟩ := exists_nat_gt
    (max 1 (max R (max (η/(α*β)) (max ((4+δ)/δ) (n₀ : ℝ)))))
  have hbounds : (1 : ℝ) ≤ n ∧ R ≤ n ∧ η/(α*β) ≤ n ∧
      (4+δ)/δ ≤ n ∧ (n₀ : ℝ) ≤ n := by
    simpa only [max_le_iff] using hn.le
  obtain ⟨hn1,hnR,hnη,hnδ,hn₀⟩ := hbounds
  have hnpos : (0 : ℝ) < n := by linarith
  have hnNat : 0 < n := by exact_mod_cast hnpos
  let τ : ℝ := β*n
  have hτ : 0 < τ := mul_pos hβ hnpos
  have hτn : τ < n := by
    dsimp [τ]
    nlinarith
  have hητ : η ≤ α*τ := by
    have hh := (div_le_iff₀ (mul_pos hα hβ)).mp hnη
    dsimp [τ]
    nlinarith
  let σ := compressedType δ n
  have hσ : 0 ≤ σ := Real.pi_pos.le.trans (compressedType_bounds hδ hnδ).1
  let m := periodizationBandwidth (σ+6*α) (2*(n : ℝ))
  have hm : n ≤ m ∧ (m : ℝ) ≤ n+δ*n := compressed_bandwidth_budget hδ hnδ
  refine ⟨2*n, by omega, ?_⟩
  apply finiteObstruction_of_centered_interval_real (L := 2*τ) (by positivity)
  apply centered_obstruction_of_trig_and_approx (A := 2*K) (δ := δ)
    (K := K) (q := 1/2) (m := m) hτ hτn hK.le (by norm_num) (by norm_num)
    (by norm_num; ring_nf; rfl) hm.1 hm.2 (hfinite n (by exact_mod_cast hn₀))
  intro t ht hloc hinterp d hd
  have hσeq : Real.pi*((((2*n : ℕ) : ℝ)+1)/(2*τ)) = σ := by
    dsimp [σ,compressedType,τ,β]
    ring
  have hinterp' : ∀ d : Fin (2*n) → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ, IsBernsteinFunction σ H f ∧ ∀ i, f (t i)=(d i : ℂ) := by
    simpa only [hσeq] using hinterp
  have hnloc : ∀ i, |t i| ≤ τ := fun i => abs_le.mpr (hloc i)
  have hwin : ∀ i, ρ ≤ plateauWindowReal α τ (t i) := by
    intro i
    exact hwindow α τ (t i) hα.le hητ (hnloc i)
  have herror : plateauPeriodError α τ (2*(n : ℝ)) (H/ρ) ≤ 1/2 := hR n hnR
  obtain ⟨P,hPb,hPr,hPK,hPe⟩ := entire_interpolation_gives_approx_trig
    t hα hτ.le (show τ < 2*(n : ℝ)/2 by linarith) hH.le hρ hσ
    (show (0 : ℝ) ≤ 1/2 by norm_num) hnloc hwin (le_refl m) herror hinterp' d hd
  refine ⟨P,hPb,hPr,hPK,?_⟩
  intro i
  convert hPe i using 1 <;> congr 2 <;> ring

end Erdos1133
