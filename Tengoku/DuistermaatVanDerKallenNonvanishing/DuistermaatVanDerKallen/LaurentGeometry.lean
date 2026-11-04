import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentEvaluation
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolynomialGradient
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.TransportControl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The analytic transport objects for the exact `MultiLaurent` representation
used in the main nonvanishing targets. All norms use the closed affine torus. -/

open scoped BigOperators Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- The original Laurent polynomial evaluated on the closed torus model.-/
def laurentOnAffineTorus {d : ℕ} (f : MultiLaurent d) (x : affineTorus d) : ℂ :=
  ambientEval (laurentRepresentative f) x.val

/-- Restricted differential norm, computed by the true torus partials.-/
def laurentDifferentialNorm {d : ℕ} (f : MultiLaurent d) (x : affineTorus d) : ℝ :=
  ambientDifferentialNorm (torusPartial (laurentRepresentative f)) x.val

/-- The actual scalar transport vector field for a Laurent polynomial.-/
def laurentVectorField {d : ℕ} (f : MultiLaurent d) (a : ℂ) (z : Fin d → ℂ) : Fin d → ℂ :=
  polynomialVectorField (laurentRepresentative f) a z

/-- Its regular open domain, including nonvanishing of every torus coordinate.-/
def laurentRegularDomain {d : ℕ} (f : MultiLaurent d) : Set (Fin d → ℂ) :=
  polynomialRegularDomain (laurentRepresentative f)

/--
@isnad1 id=eq.1h3v.s5.04bb6cdc1fb9 from=translated src=- shape=b3f67b89 vocab=105d675c
-/
@[simp] theorem laurentOnAffineTorus_embed {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    laurentOnAffineTorus f ⟨torusEmbed z, embed_mem hz⟩ = laurentEval f z :=
  laurentRepresentative_eval f z

/--
@isnad1 id=contdiff.1h3v.s6.693dfd21c87e from=translated src=- shape=0ab3b14d vocab=e96de8db
-/
theorem laurentEval_contDiffAt {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) : ContDiffAt ℝ ⊤ (laurentEval f) z := by
  rw [laurentEval_eq_polynomial_restriction]
  exact (ambientEval_contDiff_real (laurentRepresentative f)).contDiffAt.comp z
    (torusEmbed_contDiffAt_real hz)

/--
@isnad1 id=continuo.0h2v.s6.8c96ad002248 from=translated src=- shape=618a1ea7 vocab=1e789f82
-/
theorem laurentOnAffineTorus_continuous {d : ℕ} (f : MultiLaurent d) :
    Continuous (laurentOnAffineTorus f) :=
  (ambientEval_continuous (laurentRepresentative f)).comp continuous_subtype_val

/--
@isnad1 id=continuo.0h2v.s6.a5e909807cd6 from=translated src=- shape=618a1ea7 vocab=22ccf5e5
-/
theorem laurentDifferentialNorm_continuous {d : ℕ} (f : MultiLaurent d) :
    Continuous (laurentDifferentialNorm f) :=
  (ambientDifferentialNorm_continuous _).comp continuous_subtype_val

/--
@isnad1 id=le.0h3v.s4.83fc16a857bb from=translated src=- shape=e45ec8fa vocab=0d5419dc
-/
theorem laurentDifferentialNorm_nonneg {d : ℕ} (f : MultiLaurent d)
    (x : affineTorus d) : 0 ≤ laurentDifferentialNorm f x := Real.sqrt_nonneg _

/-- Manuscript `lem:uniform-gradient` for the original Laurent polynomials.
Finiteness of the two excluded sets is a separate theorem, not a premise here.
@isnad1 id=ex.2h3v.s8.34d5665a5a5c from=translated src=- shape=e128e314 vocab=fb436c47
-/
theorem laurent_uniform_gradient {d : ℕ} (f : MultiLaurent d)
    (Q : Set ℂ) (hQ : IsCompact Q)
    (hgood : ∀ c ∈ Q, c ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) :
    ∃ c > (0 : ℝ), ∀ x : affineTorus d, laurentOnAffineTorus f x ∈ Q →
      c ≤ (1 + ‖x.val‖) * laurentDifferentialNorm f x :=
  affineTorus_uniform_gradient _ _ (laurentOnAffineTorus_continuous f)
    (laurentDifferentialNorm_continuous f) (laurentDifferentialNorm_nonneg f) Q hQ hgood

/--
@isnad1 id=isopen.0h2v.s5.85c0a7939692 from=translated src=- shape=6b40eb30 vocab=7b473be3
-/
theorem laurentRegularDomain_isOpen {d : ℕ} (f : MultiLaurent d) :
    IsOpen (laurentRegularDomain f) := polynomialRegularDomain_isOpen _

/--
@isnad1 id=contdiff.1h4v.s7.4db1399aba50 from=translated src=- shape=9b2cc065 vocab=51d2f7e9
-/
theorem laurentVectorField_contDiffAt {d : ℕ} (f : MultiLaurent d)
    {a : ℂ} {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → ℂ) => laurentVectorField f az.1 az.2) (a, z) :=
  polynomialVectorField_contDiffAt _ hz

/--
@isnad1 id=eq.1h4v.s9.95793c6caeb7 from=translated src=- shape=dc412bfb vocab=d23d0fc4
-/
theorem laurentVectorField_embedded_norm {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ‖torusTangentMap z (laurentVectorField f a z)‖ =
      ‖a‖ / laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz.1⟩ :=
  polynomialVectorField_embedded_norm _ a hz

/-- Squared norm identity used to recognize the regular ODE domain.
@isnad1 id=eq.1h3v.s6.72be7b5fd659 from=translated src=- shape=d2505f00 vocab=5a8357f3
-/
theorem laurentDifferentialNorm_sq {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz⟩ ^ 2 =
      polynomialTorusNormSq (laurentRepresentative f) z := by
  unfold laurentDifferentialNorm
  rw [ambientDifferentialNorm_eq_restricted, restrictedDifferential_norm_sq]
  rfl

/--
@isnad1 id=lt.1h3v.s6.48536ad758a1 from=translated src=- shape=a4093699 vocab=58a4ff00
-/
theorem laurentDifferentialNorm_pos {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    0 < laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz.1⟩ := by
  change 0 < ambientDifferentialNorm _ (torusEmbed z)
  rw [ambientDifferentialNorm_eq_restricted]
  exact restrictedDifferential_norm_pos _ _ hz.2

/-- The coordinate-space region controlled by a proper radius and a compact base.-/
def laurentControlledRegion {d : ℕ} (f : MultiLaurent d) (Q : Set ℂ) (R : ℝ) :
    Set (Fin d → ℂ) :=
  {z | (∀ i, z i ≠ 0) ∧ ‖torusEmbed z‖ ≤ R ∧ laurentEval f z ∈ Q}

/-- Proper affine compactness transfers to the actual coordinate ODE domain.
In particular, a bounded proper radius prevents coordinates from approaching zero.
@isnad1 id=iscompac.1h4v.s5.faa494ea8f65 from=translated src=- shape=55019f10 vocab=3fd85484
-/
theorem laurentControlledRegion_isCompact {d : ℕ} (f : MultiLaurent d)
    (Q : Set ℂ) (hQ : IsCompact Q) (R : ℝ) :
    IsCompact (laurentControlledRegion f Q R) := by
  have hc : IsCompact {x : affineTorus d | ‖x.val‖ ≤ R ∧ laurentOnAffineTorus f x ∈ Q} :=
    (affineTorus_sublevel_isCompact d R).inter_right
      (hQ.isClosed.preimage (laurentOnAffineTorus_continuous f))
  have hp : Continuous (fun x : affineTorus d => fun i : Fin d => x.val (.inl i)) :=
    continuous_pi fun i => (PiLp.continuous_apply 2 (fun _ : Fin d ⊕ Fin d => ℂ) (.inl i)).comp continuous_subtype_val
  convert hc.image hp using 1
  ext z
  constructor
  · intro hz
    refine ⟨⟨torusEmbed z, embed_mem hz.1⟩, ?_, rfl⟩
    exact ⟨hz.2.1, (laurentOnAffineTorus_embed f hz.1).symm ▸ hz.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨affineTorus_coordinate_ne_zero x.property, ?_, ?_⟩
    · simpa only [embed_coordinates x.property] using hx.1
    · rw [← laurentRepresentative_eval, embed_coordinates x.property]
      exact hx.2

/-- The controlled compact set is separated from the critical locus and is
contained in the regular domain, not just bounded in the proper radius.
@isnad1 id=and.3h6v.s8.cc7e5fd5eebd from=translated src=- shape=bb3f106a vocab=3afe8e4b
-/
theorem laurentControlledRegion_regular {d : ℕ} (f : MultiLaurent d)
    (Q : Set ℂ) {c R : ℝ} (hc : 0 < c)
    (hbound : ∀ x : affineTorus d, laurentOnAffineTorus f x ∈ Q →
      c ≤ (1 + ‖x.val‖) * laurentDifferentialNorm f x) :
    ∀ z ∈ laurentControlledRegion f Q R, z ∈ laurentRegularDomain f ∧
      ∀ hz : ∀ i, z i ≠ 0,
        0 < c / (1 + R) ∧
          c / (1 + R) ≤ laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz⟩ := by
  intro z hz
  let x : affineTorus d := ⟨torusEmbed z, embed_mem hz.1⟩
  have hb := regular_lower_bound_on_radius_sublevel hc (norm_nonneg x.val) hz.2.1
    (laurentDifferentialNorm_nonneg f x)
    (hbound x (by
      change ambientEval (laurentRepresentative f) (torusEmbed z) ∈ Q
      rw [laurentRepresentative_eval]
      exact hz.2.2))
  refine ⟨⟨hz.1, ?_⟩, fun _ => hb⟩
  have hpos : 0 < laurentDifferentialNorm f x := hb.1.trans_le hb.2
  intro hn
  have hs := sq_pos_of_pos hpos
  change 0 < laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz.1⟩ ^ 2 at hs
  rw [laurentDifferentialNorm_sq f hz.1, hn] at hs
  exact lt_irrefl 0 hs

/-- Linear growth in the proper embedded metric from the uniform gradient bound.
@isnad1 id=le.3h5v.s9.5ab2392c45f2 from=translated src=- shape=220ccf22 vocab=6dbb9893
-/
theorem laurentVectorField_linear_growth {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) {c : ℝ} (hc : 0 < c)
    (hbound : c ≤ (1 + ‖torusEmbed z‖) *
      laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz.1⟩) :
    ‖torusTangentMap z (laurentVectorField f a z)‖ ≤
      (‖a‖ / c) * (1 + ‖torusEmbed z‖) := by
  rw [laurentVectorField_embedded_norm f a hz]
  have hrec : 1 / laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz.1⟩ ≤
      (1 + ‖torusEmbed z‖) / c := by
    apply (div_le_div_iff₀ (laurentDifferentialNorm_pos f hz) hc).2
    simpa using hbound
  calc
    _ = ‖a‖ * (1 / laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz.1⟩) := by ring
    _ ≤ ‖a‖ * ((1 + ‖torusEmbed z‖) / c) :=
      mul_le_mul_of_nonneg_left hrec (norm_nonneg a)
    _ = _ := by ring

/-- The manuscript Gronwall estimate for an actual normalized-gradient curve.
Both the derivative and the radius are measured after the proper embedding.
@isnad1 id=le.6h8v.s9.0ee8e73b622c from=translated src=- shape=ffcc0527 vocab=2ace2f3c
-/
theorem laurent_integral_curve_radius_bound {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ : ℝ → (Fin d → ℂ)} {s b c : ℝ} (hc : 0 < c)
    (hγ : ContinuousOn γ (Set.Icc s b))
    (hz : ∀ t ∈ Set.Icc s b, γ t ∈ laurentRegularDomain f)
    (hd : ∀ t ∈ Set.Ico s b, HasDerivAt γ (laurentVectorField f a (γ t)) t)
    (hbound : ∀ t (ht : t ∈ Set.Ico s b),
      c ≤ (1 + ‖torusEmbed (γ t)‖) * laurentDifferentialNorm f
        ⟨torusEmbed (γ t), embed_mem (hz t (Set.Ico_subset_Icc_self ht)).1⟩) :
    ∀ t ∈ Set.Icc s b, 1 + ‖torusEmbed (γ t)‖ ≤
      (1 + ‖torusEmbed (γ s)‖) * Real.exp ((‖a‖ / c) * (t - s)) := by
  apply trajectory_radius_bound (x := torusEmbed ∘ γ)
    (v := fun t => torusTangentMap (γ t) (laurentVectorField f a (γ t)))
  · intro t ht
    exact (torusEmbed_contDiffAt_real (hz t ht).1).continuousAt.comp_continuousWithinAt (hγ t ht)
  · intro t ht
    exact (((torusEmbed_hasFDerivAt (hz t (Set.Ico_subset_Icc_self ht)).1).restrictScalars ℝ).comp_hasDerivAt t (hd t ht)).hasDerivWithinAt
  · intro t ht
    exact laurentVectorField_linear_growth f a (hz t (Set.Ico_subset_Icc_self ht)) hc (hbound t ht)

end
end DuistermaatVanDerKallen
