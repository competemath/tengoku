import Tengoku.MobiusCpt.MobiusCPT.Wightman.Vtilde

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MobiusCPT

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], Definition 3.1; translating a point by a real number preserves membership in the
interior of the strip.-/
private theorem add_ofReal_mem_interior_strip_iff (τ : ℂ) (t : ℝ) (z : ℂ) :
    z + (t : ℂ) ∈ interior (strip τ) ↔ z ∈ interior (strip τ) := by
  simp only [interior_strip, Set.mem_ofPred_eq, Complex.add_im, Complex.ofReal_im,
    add_zero]

/-- [T26], Definition 3.1; translating the parameter by a real number translates the companion
vector by the corresponding boost, with the same continuation family: the strip does not move.
@isnad1 id=isboostc.1h10v.s7.1d1b04216e97 from=translated src=- shape=883cac19 vocab=fbb25a9e
-/
theorem IsBoostContinuation.add_ofReal {W : WightmanData G TF 𝓓 𝓕} {τ : ℂ} {Φ Ψ : 𝓓}
    {Gf : W.toWightmanStruct.Compat → ℂ → ℂ} (t : ℝ)
    (h : W.IsBoostContinuation τ Φ Ψ Gf) :
    W.IsBoostContinuation (τ + (t : ℂ)) Φ (W.boost t Ψ) Gf := by
  intro lam
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [strip_add_ofReal]
    exact (h lam).1
  · rw [strip_add_ofReal]
    exact (h lam).2.1
  · exact (h lam).2.2.1
  · intro s
    calc
      Gf lam ((τ + (t : ℂ)) + (s : ℂ)) =
          Gf lam (τ + ((t + s : ℝ) : ℂ)) := by
            rw [Complex.ofReal_add, add_assoc]
      _ = W.toWightmanStruct.compatApply lam (W.boost (t + s) Ψ) :=
        (h lam).2.2.2 (t + s)
      _ = W.toWightmanStruct.compatApply lam (W.boost s (W.boost t Ψ)) := by
        rw [add_comm t s, W.boost_add]

/-- [T26], Definition 3.1; a continuation at `τ + t` for `Φ` is a continuation at `τ` for
`V_t Φ`, after translating the family.
@isnad1 id=isboostc.1h10v.s7.fb533b85f709 from=translated src=- shape=bb47bda6 vocab=fbb25a9e
-/
theorem IsBoostContinuation.precomp_boost
    {W : WightmanData G TF 𝓓 𝓕} {τ : ℂ} {Φ Ψ : 𝓓}
    {Gf : W.toWightmanStruct.Compat → ℂ → ℂ} (t : ℝ)
    (h : W.IsBoostContinuation (τ + (t : ℂ)) Φ Ψ Gf) :
    W.IsBoostContinuation τ (W.boost t Φ) Ψ (fun lam z => Gf lam (z + (t : ℂ))) := by
  intro lam
  have hcont : ContinuousOn (fun z : ℂ => z + (t : ℂ)) (strip τ) :=
    (continuous_id.add continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun z : ℂ => z + (t : ℂ)) (strip τ)
      (strip (τ + (t : ℂ))) := by
    intro z hz
    rw [strip_add_ofReal]
    exact (add_ofReal_mem_strip_iff τ t z).2 hz
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z + (t : ℂ))
      (interior (strip τ)) :=
    (differentiable_id.add_const (t : ℂ)).differentiableOn
  have hmaps' : Set.MapsTo (fun z : ℂ => z + (t : ℂ))
      (interior (strip τ)) (interior (strip (τ + (t : ℂ)))) := by
    intro z hz
    rw [strip_add_ofReal]
    exact (add_ofReal_mem_interior_strip_iff τ t z).2 hz
  refine ⟨(h lam).1.comp' hcont hmaps, (h lam).2.1.fun_comp hdiff hmaps', ?_, ?_⟩
  · intro s
    change Gf lam ((s : ℂ) + (t : ℂ)) =
      W.toWightmanStruct.compatApply lam (W.boost s (W.boost t Φ))
    calc
      Gf lam ((s : ℂ) + (t : ℂ)) = Gf lam ((s + t : ℝ) : ℂ) := by
        rw [Complex.ofReal_add]
      _ = W.toWightmanStruct.compatApply lam (W.boost (s + t) Φ) :=
        (h lam).2.2.1 (s + t)
      _ = W.toWightmanStruct.compatApply lam (W.boost s (W.boost t Φ)) := by
        rw [W.boost_add]
  · intro s
    change Gf lam ((τ + (s : ℂ)) + (t : ℂ)) =
      W.toWightmanStruct.compatApply lam (W.boost s Ψ)
    calc
      Gf lam ((τ + (s : ℂ)) + (t : ℂ)) =
          Gf lam ((τ + (t : ℂ)) + (s : ℂ)) := by
            rw [add_right_comm]
      _ = W.toWightmanStruct.compatApply lam (W.boost s Ψ) :=
        (h lam).2.2.2 s

/-- [T26], Definition 3.1; the converse translation.
@isnad1 id=isboostc.1h10v.s7.b86b57549378 from=translated src=- shape=81da55c5 vocab=e87b22c1
-/
theorem IsBoostContinuation.postcomp_boost
    {W : WightmanData G TF 𝓓 𝓕} {τ : ℂ} {Φ Ψ : 𝓓}
    {Gf : W.toWightmanStruct.Compat → ℂ → ℂ} (t : ℝ)
    (h : W.IsBoostContinuation τ (W.boost t Φ) Ψ Gf) :
    W.IsBoostContinuation (τ + (t : ℂ)) Φ Ψ (fun lam z => Gf lam (z - (t : ℂ))) := by
  intro lam
  have hcont : ContinuousOn (fun z : ℂ => z - (t : ℂ))
      (strip (τ + (t : ℂ))) :=
    (continuous_id.sub continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun z : ℂ => z - (t : ℂ))
      (strip (τ + (t : ℂ))) (strip τ) := by
    intro z hz
    have hz' : z ∈ strip τ := by
      simpa only [strip_add_ofReal] using hz
    simpa only [sub_eq_add_neg, Complex.ofReal_neg] using
      (add_ofReal_mem_strip_iff τ (-t) z).2 hz'
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z - (t : ℂ))
      (interior (strip (τ + (t : ℂ)))) :=
    (differentiable_id.sub_const (t : ℂ)).differentiableOn
  have hmaps' : Set.MapsTo (fun z : ℂ => z - (t : ℂ))
      (interior (strip (τ + (t : ℂ)))) (interior (strip τ)) := by
    intro z hz
    have hz' : z ∈ interior (strip τ) := by
      simpa only [strip_add_ofReal] using hz
    simpa only [sub_eq_add_neg, Complex.ofReal_neg] using
      (add_ofReal_mem_interior_strip_iff τ (-t) z).2 hz'
  refine ⟨(h lam).1.comp' hcont hmaps, (h lam).2.1.fun_comp hdiff hmaps', ?_, ?_⟩
  · intro s
    change Gf lam ((s : ℂ) - (t : ℂ)) =
      W.toWightmanStruct.compatApply lam (W.boost s Φ)
    calc
      Gf lam ((s : ℂ) - (t : ℂ)) = Gf lam ((s - t : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub]
      _ = W.toWightmanStruct.compatApply lam
          (W.boost (s - t) (W.boost t Φ)) := (h lam).2.2.1 (s - t)
      _ = W.toWightmanStruct.compatApply lam (W.boost s Φ) := by
        rw [W.boost_add, sub_add_cancel]
  · intro s
    change Gf lam (((τ + (t : ℂ)) + (s : ℂ)) - (t : ℂ)) =
      W.toWightmanStruct.compatApply lam (W.boost s Ψ)
    calc
      Gf lam (((τ + (t : ℂ)) + (s : ℂ)) - (t : ℂ)) =
          Gf lam (τ + (s : ℂ)) := by
            congr 1
            rw [add_right_comm τ (t : ℂ) (s : ℂ), add_sub_cancel_right]
      _ = W.toWightmanStruct.compatApply lam (W.boost s Ψ) :=
        (h lam).2.2.2 s

/-- [T26], Definition 3.1; the domain is unchanged by a real translation of the parameter.
@isnad1 id=iff.0h8v.s6.c1ea354c4b12 from=translated src=- shape=568be196 vocab=f0a2e477
-/
theorem vtildeDom_add_ofReal_iff (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (t : ℝ)
    (Φ : 𝓓) :
    W.VtildeDom (τ + (t : ℂ)) Φ ↔ W.VtildeDom τ Φ := by
  constructor
  · rintro ⟨Ψ, Gf, hGf⟩
    refine ⟨W.boost (-t) Ψ, Gf, ?_⟩
    simpa only [Complex.ofReal_neg, add_neg_cancel_right] using
      (IsBoostContinuation.add_ofReal (W := W) (-t) hGf)
  · rintro ⟨Ψ, Gf, hGf⟩
    exact ⟨W.boost t Ψ, Gf, IsBoostContinuation.add_ofReal t hGf⟩

/-- [T26], Definition 3.1 and footnote 7; the domain of `Ṽ_{τ+t}` is the domain of the
composite `Ṽ_τ V_t`.
@isnad1 id=iff.0h8v.s7.ec5e4e0ba621 from=translated src=- shape=74ee9d6e vocab=7ed64d9c
-/
theorem vtildeDom_add_ofReal_iff_boost (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (t : ℝ)
    (Φ : 𝓓) :
    W.VtildeDom (τ + (t : ℂ)) Φ ↔ W.VtildeDom τ (W.boost t Φ) := by
  constructor
  · rintro ⟨Ψ, Gf, hGf⟩
    exact ⟨Ψ, _, IsBoostContinuation.precomp_boost t hGf⟩
  · rintro ⟨Ψ, Gf, hGf⟩
    exact ⟨Ψ, _, IsBoostContinuation.postcomp_boost t hGf⟩

/-- [T26], Definition 3.1 and footnote 7; the real-translation law
`Ṽ_{τ+t} = V_t Ṽ_τ = Ṽ_τ V_t`, with the domain clauses the source's "as partially defined
operators" requires. Regularity is the precise separation-of-points hypothesis needed to pin the
values; `IsWightmanCFT` would be stronger than necessary.
@isnad1 id=and.1h8v.s9.497ee0886623 from=translated src=- shape=3659ce6d vocab=fe407ecd
-/
theorem vtilde_translation (W : WightmanData G TF 𝓓 𝓕) :
    W.toWightmanStruct.ActsRegularly →
      ∀ (τ : ℂ) (t : ℝ) (Φ : 𝓓),
      (W.VtildeDom (τ + (t : ℂ)) Φ ↔ W.VtildeDom τ (W.boost t Φ)) ∧
        (W.VtildeDom (τ + (t : ℂ)) Φ ↔ W.VtildeDom τ Φ) ∧
          (W.VtildeDom (τ + (t : ℂ)) Φ →
            W.VtildeDom τ Φ →
              W.vtildeMap (τ + (t : ℂ)) Φ = W.boost t (W.vtildeMap τ Φ)) ∧
          (W.VtildeDom τ (W.boost t Φ) →
            W.vtildeMap (τ + (t : ℂ)) Φ = W.vtildeMap τ (W.boost t Φ)) := by
  intro hreg τ t Φ
  refine ⟨W.vtildeDom_add_ofReal_iff_boost τ t Φ,
    W.vtildeDom_add_ofReal_iff τ t Φ, ?_, ?_⟩
  · intro _ hdom
    obtain ⟨Gf, hGf⟩ := W.vtildeVal_vtildeMap hreg hdom
    apply W.vtildeMap_eq hreg
    exact ⟨Gf, IsBoostContinuation.add_ofReal t hGf⟩
  · intro hdom
    obtain ⟨Gf, hGf⟩ := W.vtildeVal_vtildeMap hreg hdom
    apply W.vtildeMap_eq hreg
    exact ⟨fun lam z => Gf lam (z - (t : ℂ)),
      IsBoostContinuation.postcomp_boost t hGf⟩

end WightmanData

end MobiusCPT
