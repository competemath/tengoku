import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.NuclearApproximation

namespace OAI

universe uA

section

noncomputable section

open scoped ComplexOrder

open CurrentMain Pureness

namespace NuclearTrace

section TracePairing

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_norm_mul_positive (τ : TracialState A) (u : A) (hu : ‖u‖ ≤ 1)
    {b : A} (hb : 0 ≤ b) : ‖τ.functional (u*b)‖ ≤ (τ.functional b).re := by
  let r := CFC.sqrt b
  have hr : star r = r := (CFC.sqrt_nonneg b).star_eq
  have he : τ.functional (u*b) = τ.functional ((r*u)*r) := by
    rw [τ.tracial (r*u) r]
    rw [← mul_assoc,CFC.sqrt_mul_sqrt_self b hb,τ.tracial]
  rw [he]
  apply (trace_norm_mul_le τ _ _).trans
  have hmul : traceTwoNorm τ (r*u) ≤ traceTwoNorm τ r :=
    (traceTwoNorm_mul_right τ u r).trans
      ((mul_le_mul_of_nonneg_right hu (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _))
  calc
    _ ≤ traceTwoNorm τ r * traceTwoNorm τ r :=
      mul_le_mul_of_nonneg_right hmul (traceTwoNorm_nonneg τ _)
    _ = (τ.functional b).re := by
      rw [← pow_two,traceTwoNorm_sq,hr,CFC.sqrt_mul_sqrt_self b hb]

lemma trace_norm_mul_selfAdjoint (τ : TracialState A) (u : A) (hu : ‖u‖ ≤ 1)
    {b : A} (hb : IsSelfAdjoint b) : ‖τ.functional (u*b)‖ ≤ traceOneNorm τ b := by
  calc
    _ = ‖τ.functional (u*b⁺)-τ.functional (u*b⁻)‖ := by
      rw [← map_sub,← mul_sub,CFC.posPart_sub_negPart b hb]
    _ ≤ ‖τ.functional (u*b⁺)‖+‖τ.functional (u*b⁻)‖ := norm_sub_le _ _
    _ ≤ (τ.functional b⁺).re+(τ.functional b⁻).re := add_le_add
      (trace_norm_mul_positive τ u hu (CFC.posPart_nonneg b))
      (trace_norm_mul_positive τ u hu (CFC.negPart_nonneg b))
    _ = traceOneNorm τ b := by
      rw [← Complex.add_re,← map_add,CFC.posPart_add_negPart b hb]
      rfl

end TracePairing

section Coefficients

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Fintype I] [DecidableEq I]

def residualCoefficient (i₀ : I) (r : A) (i : I) : A := if i=i₀ then CFC.sqrt r else 0

lemma residualCoefficient_synthesis (i₀ : I) (r : A) (hr : 0 ≤ r)
    (T : CStarMatrix I I ℂ) :
    matrixSynthesis (residualCoefficient i₀ r) T = T i₀ i₀ • r := by
  change (∑ i, ∑ j, T i j • (star (residualCoefficient i₀ r i)*residualCoefficient i₀ r j)) = _
  simp [residualCoefficient,apply_ite,ite_mul,(CFC.sqrt_nonneg r).star_eq,
    CFC.sqrt_mul_sqrt_self r hr]

lemma residualCoefficient_mass (i₀ : I) (r : A) (hr : 0 ≤ r) :
    (∑ i, star (residualCoefficient i₀ r i)*residualCoefficient i₀ r i) = r := by
  simpa [matrixSynthesis_one,CStarMatrix.one_apply] using
    residualCoefficient_synthesis i₀ r hr 1

lemma residualCoefficient_pairing (τ : TracialState A) (i₀ : I) (r : A) (hr : 0 ≤ r)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) (u : A) (hu : ‖u‖ ≤ 1) :
    ‖τ.functional (u*matrixSynthesis (residualCoefficient i₀ r) T)‖ ≤ (τ.functional r).re := by
  rw [residualCoefficient_synthesis i₀ r hr T,mul_smul_comm,map_smul,norm_smul]
  have hentry : ‖T i₀ i₀‖ ≤ 1 := (show ‖T i₀ i₀‖ ≤ ‖T‖ from CStarMatrix.norm_entry_le_norm).trans hT
  exact (mul_le_mul hentry (trace_norm_mul_positive τ u hu hr)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Coefficients

section NormalizeSystem

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace FiniteCoefficientSystem

def mass (F : FiniteCoefficientSystem A) : A := ∑ i, star (F.coefficient i)*F.coefficient i

def clip (F : FiniteCoefficientSystem A) : FiniteCoefficientSystem A :=
  { F with coefficient := fun i => F.coefficient i*rowNormalizer F.mass }

def residual (F : FiniteCoefficientSystem A) : A :=
  1-rowNormalizer F.mass*F.mass*rowNormalizer F.mass

lemma residual_nonneg (F : FiniteCoefficientSystem A) : 0 ≤ F.residual :=
  (rowNormalizer_bounds (row_mass_nonneg F.coefficient)).1

def fill (F : FiniteCoefficientSystem A) (i₀ : F.Index) : FiniteCoefficientSystem A :=
  { F with coefficient := residualCoefficient i₀ F.residual }

def normalize (F : FiniteCoefficientSystem A) (i₀ : F.Index) : FiniteCoefficientSystem A :=
  F.clip.add (F.fill i₀)

omit [PartialOrder A] [StarOrderedRing A] in
lemma output_one (F : FiniteCoefficientSystem A) : F.output 1 = F.mass := by
  change matrixSynthesis F.coefficient (F.input 1) = _
  rw [F.input_one,matrixSynthesis_one]
  rfl

lemma normalize_output_one (F : FiniteCoefficientSystem A) (i₀ : F.Index) :
    (F.normalize i₀).output 1 = 1 := by
  rw [normalize,add_output,output_one,output_one]
  change (∑ i, star (F.coefficient i*rowNormalizer F.mass)*(F.coefficient i*rowNormalizer F.mass)) +
    (∑ i, star (residualCoefficient i₀ F.residual i)*residualCoefficient i₀ F.residual i) = 1
  rw [residualCoefficient_mass i₀ F.residual F.residual_nonneg]
  change (∑ i, star (F.coefficient i*rowNormalizer (∑ j, star (F.coefficient j)*F.coefficient j))*
    (F.coefficient i*rowNormalizer (∑ j, star (F.coefficient j)*F.coefficient j))) + _ = _
  rw [rowNormalizer_mass]
  change rowNormalizer F.mass*F.mass*rowNormalizer F.mass +
    (1-rowNormalizer F.mass*F.mass*rowNormalizer F.mass) = 1
  abel

lemma normalize_pairing (F : FiniteCoefficientSystem A) (i₀ : F.Index)
    (τ : TracialState A) (x u : A) (hx : ‖x‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : (τ.functional F.mass).re ≤ 1+δ)
    (herr : traceOneNorm τ (F.mass-1) ≤ δ) :
    ‖τ.functional (u*(F.output x-(F.normalize i₀).output x))‖ ≤
      Real.sqrt (2*(2+δ)*δ)+δ := by
  have hT : ‖F.input x‖ ≤ 1 := (F.input_norm x).trans hx
  have hclip := rowNormalizer_pairing_bound τ F.coefficient (F.input x) hT u hu hδ hmass herr
  have hc : ‖τ.functional (u*(F.output x-F.clip.output x))‖ ≤ Real.sqrt (2*(2+δ)*δ) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).2 hclip
  have hrmass : (τ.functional F.residual).re ≤ δ :=
    ((Complex.le_def.mp (τ.functional.monotone
      (rowNormalizer_bounds (row_mass_nonneg F.coefficient)).2.1)).1).trans herr
  have hr : ‖τ.functional (u*(F.fill i₀).output x)‖ ≤ δ :=
    (residualCoefficient_pairing τ i₀ F.residual F.residual_nonneg (F.input x) hT u hu).trans hrmass
  rw [normalize,add_output]
  have he : u*(F.output x-(F.clip.output x+(F.fill i₀).output x)) =
    u*(F.output x-F.clip.output x)-u*(F.fill i₀).output x := by noncomm_ring
  rw [he,map_sub]
  exact (norm_sub_le _ _).trans (add_le_add hc hr)

end FiniteCoefficientSystem

end NormalizeSystem

lemma exists_clipping_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 2*δ+Real.sqrt (2*(2+δ)*δ) < ε := by
  let δ : ℝ := min 1 (min (ε/8) (ε^2/128))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := min_le_left _ _
  have he1 : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : δ ≤ ε^2/128 := (min_le_right _ _).trans (min_le_right _ _)
  have hb : 2*(2+δ)*δ ≤ (ε/4)^2 := by
    have hm := mul_le_mul_of_nonneg_right hd1 hd.le
    nlinarith
  have hs : Real.sqrt (2*(2+δ)*δ) ≤ ε/4 :=
    (Real.sqrt_le_iff).2 ⟨by positivity,hb⟩
  exact ⟨δ,hd,hd1,by linarith⟩

section NuclearNormalizedApproximation

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

end NuclearNormalizedApproximation

end NuclearTrace

end

end

end OAI
