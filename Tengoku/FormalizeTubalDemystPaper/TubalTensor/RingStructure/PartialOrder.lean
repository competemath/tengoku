import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.StarRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/RingStructure/PartialOrder.lean
  ≤_M partial order on K_M.

  a ≤_M b iff M(b - a) is real and entrywise nonnegative.
-/

namespace TubalTensor

open Complex Matrix

variable {n : ℕ}

namespace KM

variable {td : TubalData n}

/-- The predicate: M(b - a) is real and entrywise nonnegative.-/
private def leM (a b : KM n td) : Prop :=
  let v := td.applyM (toComplex (toFun b - toFun a))
  (∀ i, (v i).im = 0) ∧ (∀ i, 0 ≤ (v i).re)

private theorem leM_refl (a : KM n td) : leM a a := by
  unfold leM
  simp only [sub_self, toComplex_zero]
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> simp

private theorem leM_antisymm {a b : KM n td} (hab : leM a b) (hba : leM b a) : a = b := by
  unfold leM at hab hba
  set v := td.applyM (toComplex (toFun b - toFun a)) with hv_def
  -- M(a - b) = -M(b - a)
  have hvneg : td.applyM (toComplex (toFun a - toFun b)) = -v := by
    rw [show toFun a - toFun b = -(toFun b - toFun a) from (neg_sub _ _).symm]
    rw [toComplex_neg]
    exact Matrix.mulVec_neg _ td.M
  -- From hba: each component of -v has nonneg real part, so v has nonpos real part
  have hle : ∀ i, (v i).re ≤ 0 := by
    intro i
    have h := hba.2 i; rw [hvneg] at h
    simp only [Pi.neg_apply, Complex.neg_re] at h; linarith
  -- Combined: v = 0
  have hv_zero : v = 0 := by
    ext i; exact Complex.ext (le_antisymm (hle i) (hab.2 i)) (hab.1 i)
  -- By injectivity: b - a = 0
  have h_diff : toComplex (toFun b - toFun a) = 0 := by
    apply td.applyM_injective
    change v = _; rw [hv_zero]; exact (Matrix.mulVec_zero _).symm
  ext i
  have hi := congr_fun (toComplex_injective (h_diff.trans toComplex_zero.symm)) i
  simp [Pi.sub_apply] at hi; linarith

private theorem leM_trans {a b c : KM n td} (hab : leM a b) (hbc : leM b c) : leM a c := by
  unfold leM at *
  have hsum : td.applyM (toComplex (toFun c - toFun a)) =
      td.applyM (toComplex (toFun c - toFun b)) +
      td.applyM (toComplex (toFun b - toFun a)) := by
    rw [show toFun c - toFun a = (toFun c - toFun b) + (toFun b - toFun a) from by abel]
    rw [toComplex_add, td.applyM_add]
  constructor
  · intro i
    have := hbc.1 i; have := hab.1 i
    simp only [hsum, Pi.add_apply, Complex.add_im]; linarith
  · intro i
    have := hbc.2 i; have := hab.2 i
    simp only [hsum, Pi.add_apply, Complex.add_re]; linarith

/-- **Partial order on K_M**: a ≤_M b iff M(b − a) is real and entrywise nonnegative.-/
noncomputable instance instPartialOrder : PartialOrder (KM n td) where
  le := leM
  le_refl := leM_refl
  le_antisymm _ _ := leM_antisymm
  le_trans _ _ _ := leM_trans

/-- Characterization of ≤_M: a ≤ b iff M(b − a) is real and entrywise nonneg.
@isnad1 id=iff.0h4v.s7.f470a179cfdc from=translated src=- shape=cd1cbe00 vocab=b5ba2df4
-/
theorem le_iff (a b : KM n td) :
    a ≤ b ↔ (∀ i, (td.applyM (toComplex (KM.toFun b - KM.toFun a)) i).im = 0) ∧
             (∀ i, 0 ≤ (td.applyM (toComplex (KM.toFun b - KM.toFun a)) i).re) :=
  Iff.rfl

end KM

end TubalTensor
