import Tengoku.NavierStokesEuler.Euler.LpSmoothFieldJets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebra of literal smooth square-integrable spatial fields

All jets below remain actual Fréchet derivatives. The operations preserve
their genuine L² classes and continuity in an external parameter.
-/

noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory ContinuousLinearMap EulerSmoothLimit Filter
open scoped ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def jetPostcompose (L : V →L[ℝ] W) (n : ℕ) :
    (Space [×n]→L[ℝ] V) →L[ℝ] (Space [×n]→L[ℝ] W) :=
  compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) V W L

def mapField (L : V →L[ℝ] W) (A : SmoothL2Field V) : SmoothL2Field W where
  field := L ∘ A.field
  smooth := L.contDiff.comp A.smooth
  integrable n := (jetPostcompose L n).comp_memLp' (A.integrable n) |>.ae_eq
    (Eventually.of_forall (fun x => (L.iteratedFDeriv_comp_left A.smooth.contDiffAt (by simp)).symm))

/--
@isnad1 id=eq.0h5v.s7.da0dd4343721 from=translated src=- shape=75d08194 vocab=a1ce92f3
-/
@[simp] theorem mapField_field (L : V →L[ℝ] W) (A : SmoothL2Field V) (x : Space) :
    (mapField L A).field x = L (A.field x) := rfl

/--
@isnad1 id=eq.0h4v.s16.c363c2930b09 from=translated src=- shape=ae20e974 vocab=eee0f288
-/
theorem toLp_mapField (L : V →L[ℝ] W) (A : SmoothL2Field V) :
    (mapField L A).toLp = L.compLpL 2 volume A.toLp := by
  apply Lp.ext
  filter_upwards [(mapField L A).toLp_ae, L.coeFn_compLpL A.toLp, A.toLp_ae] with x h₁ h₂ h₃
  exact h₁.trans ((congrArg L h₃).symm.trans h₂.symm)

/--
@isnad1 id=eq.0h5v.s18.88d56ec707f0 from=translated src=- shape=5ae39369 vocab=36a0097d
-/
theorem jetLp_mapField (L : V →L[ℝ] W) (A : SmoothL2Field V) (n : ℕ) :
    (mapField L A).jetLp n = (jetPostcompose L n).compLpL 2 volume (A.jetLp n) := by
  apply Lp.ext
  filter_upwards [(mapField L A).jetLp_ae n, (jetPostcompose L n).coeFn_compLpL (A.jetLp n),
    A.jetLp_ae n] with x h₁ h₂ h₃
  exact h₁.trans ((L.iteratedFDeriv_comp_left (x := x) A.smooth.contDiffAt (by simp)).trans
    ((congrArg (jetPostcompose L n) h₃).symm.trans h₂.symm))

def addField (A B : SmoothL2Field V) : SmoothL2Field V where
  field := A.field+B.field
  smooth := A.smooth.add B.smooth
  integrable n := ((A.integrable n).add (B.integrable n)).ae_eq
    (Eventually.of_forall (fun x => (iteratedFDeriv_add_apply (i := n) (x := x)
      (A.smooth.contDiffAt.of_le (by simp)) (B.smooth.contDiffAt.of_le (by simp))).symm))

/--
@isnad1 id=eq.0h4v.s6.40def80aaff4 from=translated src=- shape=40fb49ed vocab=c6bc4225
-/
@[simp] theorem addField_field (A B : SmoothL2Field V) (x : Space) :
    (addField A B).field x = A.field x+B.field x := rfl

/--
@isnad1 id=eq.0h3v.s13.3870917a8bcf from=translated src=- shape=f04e478c vocab=b7cefe48
-/
theorem toLp_addField (A B : SmoothL2Field V) : (addField A B).toLp = A.toLp+B.toLp := by
  apply Lp.ext
  filter_upwards [(addField A B).toLp_ae, A.toLp_ae, B.toLp_ae,
    Lp.coeFn_add A.toLp B.toLp] with x h₁ h₂ h₃ h₄
  exact h₁.trans ((congrArg₂ (fun v w : V => v+w) h₂ h₃).symm.trans h₄.symm)

/--
@isnad1 id=eq.0h4v.s16.52d63cc04aef from=translated src=- shape=17573041 vocab=28f89904
-/
theorem jetLp_addField (A B : SmoothL2Field V) (n : ℕ) :
    (addField A B).jetLp n = A.jetLp n+B.jetLp n := by
  apply Lp.ext
  filter_upwards [(addField A B).jetLp_ae n, A.jetLp_ae n, B.jetLp_ae n,
    Lp.coeFn_add (A.jetLp n) (B.jetLp n)] with x h₁ h₂ h₃ h₄
  have hd := iteratedFDeriv_add_apply (i := n) (x := x)
    (A.smooth.contDiffAt.of_le (by simp)) (B.smooth.contDiffAt.of_le (by simp))
  exact h₁.trans (hd.trans ((congrArg₂ (fun u v : Space [×n]→L[ℝ] V => u+v) h₂ h₃).symm.trans h₄.symm))

def zeroField : SmoothL2Field V where
  field := 0
  smooth := contDiff_const
  integrable n := by
    rw [iteratedFDeriv_zero]
    exact MemLp.zero

/--
@isnad1 id=eq.0h3v.s20.79205bd6b826 from=translated src=- shape=d7f88475 vocab=86d47f27
-/
theorem jetLp_derivative (A : SmoothL2Field V) (n : ℕ) :
    A.derivative.jetLp n =
      (continuousMultilinearCurryRightEquiv' ℝ n Space V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
        2 volume (A.jetLp (n+1)) := by
  let L : (Space [×(n+1)]→L[ℝ] V) →L[ℝ] (Space [×n]→L[ℝ] (Space →L[ℝ] V)) :=
    (continuousMultilinearCurryRightEquiv' ℝ n Space V).toContinuousLinearEquiv.toContinuousLinearMap
  apply Lp.ext
  filter_upwards [A.derivative.jetLp_ae n,
    ContinuousLinearMap.coeFn_compLpL (𝕜 := ℝ) (𝕜' := ℝ)
      (E := Space [×(n+1)]→L[ℝ] V) (F := Space [×n]→L[ℝ] (Space →L[ℝ] V))
      (σ := RingHom.id ℝ) L (A.jetLp (n+1)),
    A.jetLp_ae (n+1)] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, iteratedFDeriv_succ_eq_comp_right]
  exact ((continuousMultilinearCurryRightEquiv' ℝ n Space V).apply_symm_apply _).symm

def directionalField (A : SmoothL2Field V) (v : Space) : SmoothL2Field V :=
  mapField (ContinuousLinearMap.apply ℝ V v) A.derivative

/--
@isnad1 id=eq.0h4v.s9.e70fef6ee1ef from=translated src=- shape=8cfc68d1 vocab=20a81ccd
-/
@[simp] theorem directionalField_field (A : SmoothL2Field V) (v x : Space) :
    (directionalField A v).field x = fderiv ℝ A.field x v := rfl

/--
@isnad1 id=eq.0h2v.s18.8ece8352f7d1 from=translated src=- shape=925a1aeb vocab=9546f960
-/
theorem toLp_eq_jet_zero (A : SmoothL2Field V) :
    A.toLp = (continuousMultilinearCurryFin0 ℝ Space V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 volume (A.jetLp 0) := by
  let L := (continuousMultilinearCurryFin0 ℝ Space V).toContinuousLinearEquiv.toContinuousLinearMap
  apply Lp.ext
  filter_upwards [A.toLp_ae, L.coeFn_compLpL (A.jetLp 0), A.jetLp_ae 0] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, iteratedFDeriv_zero_eq_comp]
  exact ((continuousMultilinearCurryFin0 ℝ Space V).apply_symm_apply _).symm

variable {K : Type*} [TopologicalSpace K]

/--
@isnad1 id=continuo.1h3v.s16.90b3b3f880b6 from=translated src=- shape=e5109c86 vocab=28f8b6c0
-/
theorem continuous_toLp (A : K → SmoothL2Field V)
    (hA : Continuous (fun t => (A t).jetLp 0)) : Continuous (fun t => (A t).toLp) := by
  have he : (fun t => (A t).toLp) =
      fun t => (continuousMultilinearCurryFin0 ℝ Space V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
        2 volume ((A t).jetLp 0) := funext (fun t => toLp_eq_jet_zero (A t))
  rw [he]
  exact ContinuousLinearMap.continuous _ |>.comp hA

/--
@isnad1 id=continuo.1h6v.s17.e4c22eb1d8f4 from=translated src=- shape=81804920 vocab=d86fbdf7
-/
theorem continuous_jetLp_mapField (L : V →L[ℝ] W) (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (mapField L (A t)).jetLp n) := by
  have he : (fun t => (mapField L (A t)).jetLp n) =
      fun t => (jetPostcompose L n).compLpL 2 volume ((A t).jetLp n) :=
    funext (fun t => jetLp_mapField L (A t) n)
  rw [he]
  exact ContinuousLinearMap.continuous _ |>.comp (hA n)

/--
@isnad1 id=continuo.2h5v.s17.e1aafe6e4a99 from=translated src=- shape=db546eba vocab=4d9cf078
-/
theorem continuous_jetLp_addField (A B : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (addField (A t) (B t)).jetLp n) := by
  have he : (fun t => (addField (A t) (B t)).jetLp n) =
      (fun t => (A t).jetLp n)+(fun t => (B t).jetLp n) :=
    funext (fun t => jetLp_addField (A t) (B t) n)
  rw [he]
  exact (hA n).add (hB n)

/--
@isnad1 id=continuo.1h4v.s19.bb7c433ad805 from=translated src=- shape=b86b6667 vocab=bf207b09
-/
theorem continuous_jetLp_derivative (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (A t).derivative.jetLp n) := by
  have he : (fun t => (A t).derivative.jetLp n) =
      fun t => (continuousMultilinearCurryRightEquiv' ℝ n Space V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
        2 volume ((A t).jetLp (n+1)) := funext (fun t => jetLp_derivative (A t) n)
  rw [he]
  exact ContinuousLinearMap.continuous _ |>.comp (hA (n+1))

/--
@isnad1 id=continuo.1h5v.s17.6014b7fbfb92 from=translated src=- shape=1521dd25 vocab=9387097b
-/
theorem continuous_jetLp_directionalField (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (v : Space) (n : ℕ) :
    Continuous (fun t => (directionalField (A t) v).jetLp n) :=
  continuous_jetLp_mapField (ContinuousLinearMap.apply ℝ V v) (fun t => (A t).derivative)
    (continuous_jetLp_derivative A hA) n

end EulerLpTranslation.SmoothL2Field
