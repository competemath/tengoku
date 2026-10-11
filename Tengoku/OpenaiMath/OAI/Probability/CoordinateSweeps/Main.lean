import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.CoordinateSweeps.Perturbation

namespace OAI

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps
lemma moment_le_exp_of_logMoment_le {t B : ℝ} (ht : 0≤t)
    (h : logMoment t ≤ (B:EReal)) : t ≤ Real.exp B := by
  by_cases hz : t=0
  · rw [hz]; exact (Real.exp_pos _).le
  · rw [logMoment,ite_eq_right hz] at h
    have hh : Real.log t ≤ B := by exact_mod_cast h
    simpa only [Real.exp_log (lt_of_le_of_ne ht (Ne.symm hz))] using Real.exp_le_exp.mpr hh
lemma logMoment_le_of_moment_le_exp {t B : ℝ} (ht : 0≤t) (h : t≤Real.exp B) :
    logMoment t ≤ (B:EReal) := by
  simpa only [Real.log_exp] using logMoment_le_of_le ht (Real.exp_pos B) h
end CoordinateSweeps
namespace CoordinateSweeps.Grid.Holes
open SparseScalar SparseDimension ScalarInduction
variable {G : Grid} {h r : ℕ} (H : G.Holes h)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
/-- Real exponential version of the exact conditional main estimate, used only
as the induction predicate; its equivalence to logMoment includes zero moments. -/
def MomentBound (G : Grid) (q : ℕ) (z : ℝ) : Prop :=
  ∀ (h : ℕ) (H : G.Holes h) (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer),
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost)
noncomputable def cHat (s : ℕ) : ℝ := c s+1/(20*Real.sqrt (Real.log s))
noncomputable def eHat (s : ℕ) : ℝ := e s-1/(20*Real.sqrt (Real.log s))
end CoordinateSweeps
namespace CoordinateSweeps.Grid.Holes
open ScalarInduction YoungCorner
variable {A B : Grid} {r h q : ℕ} (H : (concat A B).Holes h)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.YoungCorner
lemma log_factorial_lower (k : ℕ) (hk : 0<k) :
    (k:ℝ)*Real.log k-k ≤ Real.log (k.factorial:ℝ) := by
  have hs := Stirling.le_log_factorial_stirling hk.ne'
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hl := Real.log_nonneg hk1
  have hp : 0≤Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith
lemma shape_finrank_pos (μ : YoungDiagram) :
    0 < Module.finrank ℂ (shapeSubrep μ (Equiv.refl _)).toSubmodule := by
  have : Nontrivial (shapeSubrep μ (Equiv.refl _)).toSubmodule :=
    by
      by_contra hn
      have : Subsingleton (shapeSubrep μ (Equiv.refl _)).toSubmodule := not_nontrivial_iff_subsingleton.mp hn
      apply bot_ne_top (α := Subrepresentation (shapeSubrep μ (Equiv.refl _)).toRepresentation)
      exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact Module.finrank_pos
/-- The translated removed diagram has the entropy required in the large-k
branch, using the checked factorial/rank-count lower bound. -/
lemma removed_dimension_entropy (μ : YoungDiagram) (p s : ℕ)
    (hs : 0<s) (hM : Fintype.card (Boxes μ) ≤ s)
    (hfloor : (s:ℝ)^a ≤ p+1) (hL : 800 ≤ Real.log s)
    (hk : (s:ℝ)^(1-a/2) ≤ Fintype.card (Boxes (removedPart μ p))) :
    (a/4)*(Fintype.card (Boxes (removedPart μ p)):ℝ)*Real.log s ≤
      Real.log (Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule) := by
  let k := Fintype.card (Boxes (removedPart μ p))
  let D := Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule
  let L := 2*(Fintype.card (Boxes μ)/(p+1))
  have hs0 : (0:ℝ)<s := by exact_mod_cast hs
  have hk0 : 0<k := by
    have hh : (0:ℝ)<k := (Real.rpow_pos_of_pos hs0 _).trans_le hk
    exact_mod_cast hh
  have hD0 : 0<D := shape_finrank_pos _
  have hLp : 0<L := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hk0
    exact Nat.zero_le (x.val.1+x.val.2) |>.trans_lt (removedPart_rank_lt μ p x)
  have hL0 : (0:ℝ)<L := by exact_mod_cast hLp
  have hc := shape_dimension_entropy (removedPart μ p)
    (shapeSubrep (removedPart μ p) (Equiv.refl _)).toRepresentation
    (shapeSubrep_hasShape _ _) L (removedPart_rank_lt μ p)
  have hc' : (k.factorial:ℝ) ≤ (L:ℝ)^k*D := by exact_mod_cast hc
  have hlog := Real.log_le_log (by exact_mod_cast Nat.factorial_pos k : (0:ℝ)<k.factorial) hc'
  rw [Real.log_mul (by positivity : (L:ℝ)^k≠0) (by exact_mod_cast hD0.ne'),Real.log_pow] at hlog
  have hfac := log_factorial_lower k hk0
  have hLp' : (L:ℝ)*(p+1) ≤ 2*s := by
    have hh := Nat.div_mul_le_self (Fintype.card (Boxes μ)) (p+1)
    have hh' : (Fintype.card (Boxes μ)/(p+1))*(p+1) ≤ s := hh.trans hM
    dsimp [L]
    exact_mod_cast (show 2*(Fintype.card (Boxes μ)/(p+1))*(p+1)≤2*s by nlinarith [hh'])
  have hLupper : (L:ℝ) ≤ 2*(s:ℝ)^(1-a) := by
    have hh := mul_le_mul_of_nonneg_left hfloor hL0.le
    have hhs : (L:ℝ)*(s:ℝ)^a ≤ 2*s := hh.trans hLp'
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hs0 a)).mp
    calc
      _ ≤ 2*(s:ℝ) := hhs
      _ = 2*(s:ℝ)^(1-a)*(s:ℝ)^a := by rw [mul_assoc,←Real.rpow_add hs0]; norm_num
  have hLogL : Real.log L ≤ Real.log 2+(1-a)*Real.log s := by
    have hh := Real.log_le_log hL0 hLupper
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hs0 _).ne',Real.log_rpow hs0] at hh
    exact hh
  have hLogk : (1-a/2)*Real.log s ≤ Real.log k := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hs0 (1-a/2)) hk
    simpa only [Real.log_rpow hs0] using hh
  have hl2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hkR : (0:ℝ)≤k := Nat.cast_nonneg _
  have hh1 := mul_le_mul_of_nonneg_left hLogL hkR
  have hh2 := mul_le_mul_of_nonneg_left hLogk hkR
  have hh3 : (a/4)*Real.log s ≥ Real.log 2+1 := by norm_num [a] at *; linarith
  have hh4 := mul_le_mul_of_nonneg_left hh3 hkR
  change (a/4)*(k:ℝ)*Real.log s ≤ Real.log D
  nlinarith
end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.Grid.Holes
open YoungCorner ScalarInduction
variable {G : Grid} {h : ℕ} (H : G.Holes h)

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner ScalarInduction
variable {A B : Grid} {r h q : ℕ} (H : (concat A B).Holes h)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
open Filter
lemma eventually_scaleLarge : ∀ᶠ r : ℕ in atTop, ScaleLarge r := by
  obtain ⟨r₀,hr₀⟩ := exists_scaleLarge
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hh : (r₀:ℝ)*Real.log 2 ≤ (r:ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (Real.log_nonneg (by norm_num))
  exact ⟨hr₀.1.trans hr,hr₀.2.1.trans hh,hr₀.2.2.trans hh⟩
lemma exists_main_scale : ∃ r : ℕ, ScaleLarge r ∧ SparseScalar.ScaleReady r ∧
    ∀ G : Grid, G.Allowed r → ScalarInduction.MainSizeReady SparseScalar.q G.size := by
  obtain ⟨S,hS⟩ := eventually_atTop.mp (ScalarInduction.eventually_mainSizeReady SparseScalar.q)
  have hp : Tendsto (fun r : ℕ => (2:ℝ)^r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hall : ∀ᶠ r : ℕ in atTop, ScaleLarge r ∧ SparseScalar.ScaleReady r ∧ S≤(2:ℝ)^r := by
    filter_upwards [eventually_scaleLarge,SparseScalar.eventually_scaleReady,
      hp.eventually (eventually_ge_atTop S)] with r h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨r,hr,hs,ht⟩ := hall.exists
  exact ⟨r,hr,hs,fun G hG => hS G.size (ht.trans (G.pow_r_le_size hG))⟩

end CoordinateSweeps

end OAI
