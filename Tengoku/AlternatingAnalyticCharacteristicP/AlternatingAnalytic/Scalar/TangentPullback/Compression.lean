import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Analytic.CPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compressing pullback families to the operator obstruction

Given bounded linear maps `P : X → D` and `I : E → X`, the bounded linear map
`T ↦ R ∘ T ∘ J`, with `J` extension of forms along `P` and `R` restriction along `I`, sends
the pullback by `g` on `Alt(X; F)` to the pullback by `P ∘ g ∘ I`. Hence, if a family of
operators `g(y)` on `X` satisfies `P ∘ g(σ u) ∘ I = u` along an analytic slice `σ`, then
analyticity of `y ↦ g(y)^*` at `σ u₀` forces analyticity of the operator obstruction
`A(u) = u^*` at `u₀`. This is the common step of both parts of Proposition 6.5.
Bounded bilinear maps and pairs of polynomial maps are polynomial.
-/

noncomputable section

namespace AlternatingAnalytic.TangentPullback

variable {K : Type*} [NontriviallyNormedField K]
  {X D E F : Type*}
  [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  {ι : Type*} [Fintype ι]

/-- The bounded linear map `T ↦ R ∘ T ∘ J`, where `J` extends forms along `P` and `R`
restricts forms along `I`.-/
def formCompression (P : X →L[K] D) (I : E →L[K] X) :
    ((X [⋀^ι]→L[K] F) →L[K] (X [⋀^ι]→L[K] F)) →L[K]
      ((D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F)) :=
  (ContinuousLinearMap.compL K (D [⋀^ι]→L[K] F)
    (X [⋀^ι]→L[K] F) (E [⋀^ι]→L[K] F)
      (ContinuousAlternatingMap.compContinuousLinearMapCLM I)).comp
    ((ContinuousLinearMap.compL K (D [⋀^ι]→L[K] F)
      (X [⋀^ι]→L[K] F) (X [⋀^ι]→L[K] F)).flip
        (ContinuousAlternatingMap.compContinuousLinearMapCLM P))

/-- Compression of the pullback by `g` is the pullback by `P ∘ g ∘ I`.-/
theorem formCompression_pullback (P : X →L[K] D) (I : E →L[K] X) (g : X →L[K] X) :
    formCompression (F := F) (ι := ι) P I
      (ContinuousAlternatingMap.compContinuousLinearMapCLM g) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM (P.comp (g.comp I)) := by
  ext m x
  simp [formCompression, Function.comp_def]

/-- If `P ∘ g(σ u) ∘ I = u` along an analytic slice `σ`, then nonanalyticity of the operator
obstruction at `u₀` gives nonanalyticity of `y ↦ g(y)^*` at `σ u₀`.-/
theorem not_analyticAt_pullback_of_slice (P : X →L[K] D) (I : E →L[K] X)
    (g : X → X →L[K] X) (σ : (E →L[K] D) → X) (u₀ : E →L[K] D)
    (hσ : AnalyticAt K σ u₀) (hg : ∀ u, P.comp ((g (σ u)).comp I) = u)
    (hA : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀) :
    ¬ AnalyticAt K
      (fun y : X =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (g y) :
          (X [⋀^ι]→L[K] F) →L[K] (X [⋀^ι]→L[K] F))) (σ u₀) := by
  intro ha
  have hc := (ContinuousLinearMap.analyticAt (𝕜 := K)
    (E := (X [⋀^ι]→L[K] F) →L[K] (X [⋀^ι]→L[K] F))
    (F := (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F)) (formCompression P I) _).comp
      (ha.comp hσ)
  apply hA
  simpa only [Function.comp_def, formCompression_pullback, hg] using hc

omit [NormedAddCommGroup F] [NormedSpace K F] in
/-- A pair of polynomial maps is polynomial.-/
theorem cpolynomialAt_pair {P A B : Type*} [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup A] [NormedSpace K A] [NormedAddCommGroup B] [NormedSpace K B]
    {f : P → A} {g : P → B} {x : P}
    (hf : CPolynomialAt K f x) (hg : CPolynomialAt K g x) :
    CPolynomialAt K (fun y => (f y, g y)) x := by
  have h := (((ContinuousLinearMap.inl K A B).cpolynomialAt (f x)).comp hf).add
    (((ContinuousLinearMap.inr K A B).cpolynomialAt (g x)).comp hg)
  change CPolynomialAt K (fun y => (f y, 0) + (0, g y)) x at h
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using h

omit [NormedAddCommGroup F] [NormedSpace K F] in
/-- A bounded bilinear map is polynomial.-/
theorem cpolynomialAt_bilinear {A B C : Type*} [NormedAddCommGroup A] [NormedSpace K A]
    [NormedAddCommGroup B] [NormedSpace K B] [NormedAddCommGroup C] [NormedSpace K C]
    (b : A →L[K] B →L[K] C) (x : A × B) :
    CPolynomialAt K (fun y : A × B => b y.1 y.2) x := by
  refine ⟨b.fpowerSeriesBilinear x, 3, ⊤, b.hasFPowerSeriesOnBall_bilinear x, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 m]
  exact b.fpowerSeriesBilinear_apply_add_three x m

end AlternatingAnalytic.TangentPullback
