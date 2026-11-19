/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku
import Tengoku.Nashembedding.NashEmbedding.Torus.Perturbation.GuntherIdentity
import Tengoku.Nashembedding.NashEmbedding.Torus.Perturbation.GuntherOperator
import Tengoku.Nashembedding.NashEmbedding.Sobolev.CoeffTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Günther's identity on the momentum side

`gunther_identity` (position space, real-valued maps) is transported to coefficient
sequences: for a vector sequence `v` whose components are rapidly decaying and
`conjReflect`-fixed (so that its synthesis `vsynth v` is a smooth periodic real map),

  `-Δ̂ (∂ᵢv · ∂ⱼv) = ∂ᵢ(Lv · ∂ⱼv) + ∂ⱼ(Lv · ∂ᵢv) - 2 Lv · ∂ᵢ∂ⱼv + 2 ∑ₖ ∂ᵢ∂ₖv · ∂ⱼ∂ₖv`

where products are `seqConv`, `·` is `dotConv`, `∂ᵢ` is `vpartial i`, `L` is `vlap`, and
`Δ̂ = laplacianCoeff` (so `-Δ̂` is `L` on scalar sequences).

Consequently the polarized pieces `Fb`, `Ub` of the Günther operator satisfy
`∂ᵢv · ∂ⱼv = ∂ᵢ Fb j v v + ∂ⱼ Fb i v v + Ub i j v v`, which is the identity behind the
ansatz of Theorem B. The dictionary between real maps `ℝⁿ → ℝᴺ` and vector sequences
(`vcoeff`, `vsynth`) is set up here as well.
-/

open scoped BigOperators ContDiff
open NashEmbedding.Sobolev Matrix

noncomputable section

namespace NashEmbedding

variable {n N : ℕ}

/-! ## Real maps ↔ vector sequences -/

/-- Componentwise rapid decay.-/
def VRapid (n N : ℕ) (v : VecSeq n N) : Prop := ∀ α, IsRapidDecay n (v α)

/-- Componentwise `conjReflect`-fixed: the coefficients of a real-valued map.-/
def VReal (v : VecSeq n N) : Prop := ∀ α, conjReflect (v α) = v α

/-- The coefficient sequences of a real map `u : ℝⁿ → ℝᴺ`.-/
def vcoeff (n : ℕ) (u : (Fin n → ℝ) → (Fin N → ℝ)) : VecSeq n N :=
  fun α => stdFourierCoeff n (fun x => ((u x α : ℝ) : ℂ))

/-- The (real) synthesis of a vector sequence.-/
def vsynth (n : ℕ) (v : VecSeq n N) : (Fin n → ℝ) → (Fin N → ℝ) :=
  fun x α => (fourierSynthesis n (v α) x).re

/--
@isnad1 id=vmem.1h4v.s4.28e41c53fbf3 from=translated src=- shape=e4d74c45 vocab=4f005cda
-/
lemma VRapid.vmem {v : VecSeq n N} (hv : VRapid n N v) (s : ℝ) : VMem n N s v :=
  fun α => hv α s

/--
@isnad1 id=vrapid.1h3v.s4.a1091de1484e from=translated src=- shape=511837e9 vocab=178af9e3
-/
lemma vrapid_of_vmem {v : VecSeq n N} (hv : ∀ k : ℕ, VMem n N k v) : VRapid n N v := by
  intro α s
  exact (hv ⌈s⌉₊ α).mono (Nat.le_ceil s)

/-- Coordinate partials of periodic maps are periodic (any target).
@isnad1 id=isperiod.1h4v.s5.64f235625843 from=translated src=- shape=11aadae2 vocab=013d58ae
-/
lemma isPeriodic2Pi_pderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : IsPeriodic2Pi f) (i : Fin n) : IsPeriodic2Pi (pderiv i f) := by
  intro x k
  have h : (fun y => f (y + periodicShift n k)) = f := funext fun y => hf y k
  show fderiv ℝ f (x + periodicShift n k) (Pi.single i 1) = fderiv ℝ f x (Pi.single i 1)
  rw [← fderiv_comp_add_right (f := f) (x := x) (periodicShift n k), h]

/--
@isnad1 id=smoothpe.1h4v.s5.a3a8478c8e1d from=translated src=- shape=11aadae2 vocab=2c2bf85e
-/
lemma SmoothPeriodic.pderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : SmoothPeriodic f) (i : Fin n) : SmoothPeriodic (pderiv i f) :=
  ⟨pderiv_contDiff hf.smooth i, isPeriodic2Pi_pderiv hf.periodic i⟩

/--
@isnad1 id=smoothpe.1h3v.s5.abeee0c3e773 from=translated src=- shape=098bfb89 vocab=4ee9b1f5
-/
lemma SmoothPeriodic.sumSqDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : SmoothPeriodic f) : SmoothPeriodic (sumSqDeriv f) := by
  refine ⟨sumSqDeriv_contDiff hf.smooth, ?_⟩
  intro x k
  show (∑ a, NashEmbedding.pderiv a (NashEmbedding.pderiv a f) (x + periodicShift n k))
      = ∑ a, NashEmbedding.pderiv a (NashEmbedding.pderiv a f) x
  exact Finset.sum_congr rfl fun a _ =>
    isPeriodic2Pi_pderiv (isPeriodic2Pi_pderiv hf.periodic a) a x k

/--
@isnad1 id=smoothpe.2h4v.s7.652267ae35cc from=translated src=- shape=44caa028 vocab=7b2afe87
-/
lemma SmoothPeriodic.dotProduct {u w : (Fin n → ℝ) → (Fin N → ℝ)}
    (hu : SmoothPeriodic u) (hw : SmoothPeriodic w) :
    SmoothPeriodic (fun x => u x ⬝ᵥ w x) := by
  refine ⟨contDiff_dotProduct hu.smooth hw.smooth, ?_⟩
  intro x k
  simp only [hu.periodic x k, hw.periodic x k]

/-- The complexified component `x ↦ (u x α : ℂ)` of a smooth periodic real map is smooth
periodic.
@isnad1 id=and.1h4v.s7.580742de6527 from=translated src=- shape=d4842cf1 vocab=f21974fe
-/
lemma smoothPeriodic_ofReal_comp {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (α : Fin N) : ContDiff ℝ ∞ (fun x => ((u x α : ℝ) : ℂ)) ∧
      IsPeriodic2Pi (fun x => ((u x α : ℝ) : ℂ)) := by
  constructor
  · exact Complex.ofRealCLM.contDiff.comp
      (((ContinuousLinearMap.proj α : (Fin N → ℝ) →L[ℝ] ℝ).contDiff).comp hu.smooth)
  · intro x k
    simp only [hu.periodic x k]

/--
@isnad1 id=and.1h2v.s7.6a16ecf2bbb2 from=translated src=- shape=905f612c vocab=f21974fe
-/
lemma smoothPeriodic_ofReal_scalar {f : (Fin n → ℝ) → ℝ} (hf : SmoothPeriodic f) :
    ContDiff ℝ ∞ (fun x => ((f x : ℝ) : ℂ)) ∧ IsPeriodic2Pi (fun x => ((f x : ℝ) : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp hf.smooth, ?_⟩
  intro x k
  simp only [hf.periodic x k]

/-- Casting to `ℂ` commutes with `pderiv` (scalar case).
@isnad1 id=eq.1h3v.s7.90b540340bae from=translated src=- shape=bd0c8996 vocab=0b1b4d1c
-/
lemma pderiv_ofReal {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    pderiv i (fun x => ((f x : ℝ) : ℂ)) = fun x => ((pderiv i f x : ℝ) : ℂ) := by
  funext x
  have hd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have h : HasFDerivAt (fun y => ((f y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt
  show fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x (Pi.single i 1) = _
  rw [h.fderiv]
  rfl

/-- Casting to `ℂ` commutes with `pderiv` (component case).
@isnad1 id=eq.1h5v.s8.9e990909a9c4 from=translated src=- shape=09ed8c37 vocab=0b1b4d1c
-/
lemma pderiv_ofReal_comp {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : ContDiff ℝ ∞ u) (i : Fin n)
    (α : Fin N) :
    pderiv i (fun x => ((u x α : ℝ) : ℂ)) = fun x => ((pderiv i u x α : ℝ) : ℂ) := by
  funext x
  have hd : DifferentiableAt ℝ u x := hu.differentiable (by simp) x
  have h : HasFDerivAt (fun y => ((u y α : ℝ) : ℂ))
      (Complex.ofRealCLM.comp
        (((ContinuousLinearMap.proj α : (Fin N → ℝ) →L[ℝ] ℝ)).comp (fderiv ℝ u x))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x
      (((ContinuousLinearMap.proj α : (Fin N → ℝ) →L[ℝ] ℝ)).hasFDerivAt.comp x hd.hasFDerivAt)
  show fderiv ℝ (fun y => ((u y α : ℝ) : ℂ)) x (Pi.single i 1) = _
  rw [h.fderiv]
  rfl

/--
@isnad1 id=vrapid.2h3v.s6.edd81022da24 from=translated src=- shape=43874902 vocab=423615e8
-/
lemma vcoeff_vrapid (hn : 0 < n) {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    VRapid n N (vcoeff n u) := fun α =>
  isRapidDecay_stdFourierCoeff hn (smoothPeriodic_ofReal_comp hu α).1 (smoothPeriodic_ofReal_comp hu α).2

/--
@isnad1 id=vreal.1h3v.s6.191a132ad3de from=translated src=- shape=d2d2e314 vocab=0f4261d5
-/
lemma vcoeff_vreal {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    VReal (vcoeff n u) := fun α =>
  conjReflect_stdFourierCoeff_of_real (smoothPeriodic_ofReal_comp hu α).1.continuous
    (fun x => by simp)

/-- The synthesis of a `VReal` sequence is real: `((vsynth v x α : ℝ) : ℂ) = ǎ_α x`.
@isnad1 id=eq.1h5v.s5.8aec56f4a134 from=translated src=- shape=746a4064 vocab=a0dc53d5
-/
lemma ofReal_vsynth {v : VecSeq n N} (hr : VReal v) (x : Fin n → ℝ) (α : Fin N) :
    ((vsynth n v x α : ℝ) : ℂ) = fourierSynthesis n (v α) x := by
  unfold vsynth
  exact Complex.ext (by simp) (by simp [fourierSynthesis_im_eq_zero (hr α) x])

/--
@isnad1 id=smoothpe.2h3v.s6.ff494d7be13c from=translated src=- shape=6efc9308 vocab=c47f898e
-/
lemma vsynth_smoothPeriodic (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) :
    SmoothPeriodic (vsynth n v) := by
  constructor
  · rw [contDiff_pi]
    intro α
    exact Complex.reCLM.contDiff.comp (fourierSynthesis_contDiff hn (hv α))
  · intro x k
    funext α
    show (fourierSynthesis n (v α) (x + periodicShift n k)).re = _
    rw [fourierSynthesis_isPeriodic2Pi x k]
    rfl

/--
@isnad1 id=eq.3h3v.s5.6dae3a3c64fd from=translated src=- shape=b6871ceb vocab=92b78766
-/
lemma vcoeff_vsynth (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v) :
    vcoeff n (vsynth n v) = v := by
  funext α
  unfold vcoeff
  have : (fun x => ((vsynth n v x α : ℝ) : ℂ)) = fourierSynthesis n (v α) := by
    funext x; exact ofReal_vsynth hr x α
  rw [this]
  funext m
  exact stdFourierCoeff_fourierSynthesis_of_rapidDecay hn (hv α) m

/-! ## The dictionary for derivatives and dot products -/

/--
@isnad1 id=eq.2h4v.s7.d8a70d7e2080 from=translated src=- shape=bac37527 vocab=ef127589
-/
lemma vcoeff_pderiv (hn : 0 < n) {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (i : Fin n) : vcoeff n (pderiv i u) = vpartial i (vcoeff n u) := by
  funext α
  show stdFourierCoeff n (fun x => ((pderiv i u x α : ℝ) : ℂ))
      = partialCoeff i (stdFourierCoeff n (fun x => ((u x α : ℝ) : ℂ)))
  rw [← pderiv_ofReal_comp hu.smooth i α]
  exact stdFourierCoeff_partialDeriv' hn (smoothPeriodic_ofReal_comp hu α).1
    (smoothPeriodic_ofReal_comp hu α).2 i

/--
@isnad1 id=eq.2h3v.s7.bbb9dc9a735a from=translated src=- shape=b8b8eb1a vocab=e2b7629e
-/
lemma vcoeff_sumSqDeriv (hn : 0 < n) {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    vcoeff n (sumSqDeriv u) = vlap (vcoeff n u) := by
  funext α
  have hc : ∀ k : Fin n, pderiv k (pderiv k (fun y => ((u y α : ℝ) : ℂ)))
      = fun y => ((pderiv k (pderiv k u) y α : ℝ) : ℂ) := by
    intro k
    rw [pderiv_ofReal_comp hu.smooth k α,
      pderiv_ofReal_comp (pderiv_contDiff hu.smooth k) k α]
  have h : (fun x => ((sumSqDeriv u x α : ℝ) : ℂ))
      = fun x => ∑ k, pderiv k (pderiv k (fun y => ((u y α : ℝ) : ℂ))) x := by
    funext x
    simp only [hc]
    have hsum : sumSqDeriv u x α = ∑ k, pderiv k (pderiv k u) x α := by
      show (∑ k, pderiv k (pderiv k u) x) α = _
      simp [Finset.sum_apply]
    rw [hsum]
    push_cast
    rfl
  show stdFourierCoeff n (fun x => ((sumSqDeriv u x α : ℝ) : ℂ)) = _
  rw [h]
  exact stdFourierCoeff_sumSqDeriv hn (smoothPeriodic_ofReal_comp hu α).1
    (smoothPeriodic_ofReal_comp hu α).2

/-! ## The identity on sequences -/

/-- `Ub` is symmetric on the diagonal.
@isnad1 id=eq.2h5v.s5.41f1465aaf7f from=translated src=- shape=5985695d vocab=9185844e
-/
theorem Ub_symm (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (i j : Fin n) :
    Ub i j v v = Ub j i v v := by
  have hcomm : ∀ a b : VecSeq n N, dotConv a b = dotConv b a := by
    intro a b
    funext m
    exact Finset.sum_congr rfl fun α _ => by rw [seqConv_comm]
  have hswap : vpartial i (vpartial j v) = vpartial j (vpartial i v) := by
    funext α m
    simp only [vpartial, partialCoeff]
    ring
  have h3 : ∀ k : Fin n, dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))
      = dotConv (vpartial j (vpartial k v)) (vpartial i (vpartial k v)) := fun k => hcomm _ _
  funext m
  simp only [Ub, hcomm (vpartial i v) (vpartial j v), hswap, h3]

end NashEmbedding

end
