import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A smooth local solution of the scaled Picard equation in a Banach space.
At zero time scale its derivative in the unknown curve is the identity, so
no invertibility hypothesis on a nonzero-time linearization is assumed. -/

open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Residual of the scaled Picard equation, with parameters `(time, field
parameter, initial curve)` and an unknown curve in the Banach space `B`.-/
def picardResidual (K : B →L[ℝ] B) (V : A × B → B)
    (q : (ℝ × (A × B)) × B) : B :=
  q.2 - q.1.2.2 - q.1.1 • K (V (q.1.2.1, q.2))

omit [CompleteSpace A] [CompleteSpace B] in
/--
@isnad1 id=contdiff.1h8v.s8.b4be9e6d1b2a from=translated src=- shape=0a7b1712 vocab=e9cb0ee0
-/
theorem picardResidual_contDiffAt (K : B →L[ℝ] B) (V : A × B → B)
    {a : A} {b y : B} {δ : ℝ} (hV : ContDiffAt ℝ ⊤ V (a, y)) :
    ContDiffAt ℝ ⊤ (picardResidual K V) ((δ, (a, b)), y) := by
  have hp : ContDiffAt ℝ ⊤ (fun q : (ℝ × (A × B)) × B => (q.1.2.1, q.2))
      ((δ, (a, b)), y) := (contDiffAt_fst.snd.fst).prodMk contDiffAt_snd
  have hv : ContDiffAt ℝ ⊤ (fun q : (ℝ × (A × B)) × B => K (V (q.1.2.1, q.2)))
      ((δ, (a, b)), y) :=
    K.contDiff.contDiffAt.comp ((δ, (a, b)), y) (hV.comp ((δ, (a, b)), y) hp)
  exact (contDiffAt_snd.sub contDiffAt_fst.snd.snd).sub (contDiffAt_fst.fst.smul hv)

omit [CompleteSpace A] [CompleteSpace B] in
/-- At zero time scale, the partial derivative in the unknown curve is the
identity, hence invertible without a separate assumption.
@isnad1 id=eq.1h6v.s10.41e806d24aa1 from=translated src=- shape=f0c0209e vocab=ab422e6c
-/
theorem picardResidual_partial_zero (K : B →L[ℝ] B) (V : A × B → B)
    {a : A} {b : B} (hV : ContDiffAt ℝ ⊤ V (a, b)) :
    fderiv ℝ (picardResidual K V) ((0, (a, b)), b) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × (A × B)) B = ContinuousLinearMap.id ℝ B := by
  have hG := (picardResidual_contDiffAt K V (b := b) (δ := 0) hV).differentiableAt
    (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have he : HasFDerivAt (fun y : B => ((0, (a, b)), y))
      (ContinuousLinearMap.inr ℝ (ℝ × (A × B)) B) b := by
    have hd : (0 : B →L[ℝ] ℝ × (A × B)).prod (ContinuousLinearMap.id ℝ B) =
        ContinuousLinearMap.inr ℝ (ℝ × (A × B)) B := by ext x <;> rfl
    rw [← hd]
    exact (hasFDerivAt_const ((0 : ℝ), (a, b)) b).prodMk (hasFDerivAt_id b)
  have h := hG.hasFDerivAt.comp b he
  have hid : HasFDerivAt (fun y : B => y - b) (ContinuousLinearMap.id ℝ B) b := by
    simpa using (hasFDerivAt_id b).sub_const b
  have hh : HasFDerivAt (fun y : B => y - b)
      (fderiv ℝ (picardResidual K V) ((0, (a, b)), b) ∘L
        ContinuousLinearMap.inr ℝ (ℝ × (A × B)) B) b := by
    simpa [picardResidual, Function.comp_def] using h
  exact hh.unique hid

/-- A smooth branch solving the scaled Picard equation near zero time, with
joint dependence on the field parameter and the initial curve.
@isnad1 id=ex.1h6v.s9.beb9b5150340 from=translated src=- shape=7b5770ab vocab=89b129a2
-/
theorem exists_smooth_picard_branch (K : B →L[ℝ] B) (V : A × B → B)
    {a : A} {b : B} (hV : ContDiffAt ℝ ⊤ V (a, b)) :
    ∃ Φ : ℝ × (A × B) → B,
      ContDiffAt ℝ ⊤ Φ (0, (a, b)) ∧ Φ (0, (a, b)) = b ∧
      ∀ᶠ q in 𝓝 (0, (a, b)), Φ q = q.2.2 + q.1 • K (V (q.2.1, Φ q)) := by
  have hG := picardResidual_contDiffAt K V (b := b) (δ := 0) hV
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hi : (fderiv ℝ (picardResidual K V) ((0, (a, b)), b) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × (A × B)) B).IsInvertible := by
    rw [picardResidual_partial_zero K V hV]
    exact ⟨ContinuousLinearEquiv.refl ℝ B, rfl⟩
  refine ⟨hG.implicitFunction hn hi, hG.contDiffAt_implicitFunction hn hi,
    hG.implicitFunction_apply_self hn hi, ?_⟩
  filter_upwards [hG.eventually_apply_implicitFunction hn hi] with q hq
  have he : hG.implicitFunction hn hi q - q.2.2 -
      q.1 • K (V (q.2.1, hG.implicitFunction hn hi q)) = 0 := by
    simpa [picardResidual] using hq
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp he) |>.trans (add_comm _ _)

end

end DuistermaatVanDerKallen
