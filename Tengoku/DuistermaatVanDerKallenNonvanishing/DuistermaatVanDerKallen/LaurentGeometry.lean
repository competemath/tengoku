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

@[simp] theorem laurentOnAffineTorus_embed {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    laurentOnAffineTorus f ⟨torusEmbed z, embed_mem hz⟩ = laurentEval f z :=
  laurentRepresentative_eval f z

theorem laurentEval_contDiffAt {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) : ContDiffAt ℝ ⊤ (laurentEval f) z := by
  rw [laurentEval_eq_polynomial_restriction]
  exact (ambientEval_contDiff_real (laurentRepresentative f)).contDiffAt.comp z
    (torusEmbed_contDiffAt_real hz)

theorem laurentOnAffineTorus_continuous {d : ℕ} (f : MultiLaurent d) :
    Continuous (laurentOnAffineTorus f) :=
  (ambientEval_continuous (laurentRepresentative f)).comp continuous_subtype_val

theorem laurentDifferentialNorm_continuous {d : ℕ} (f : MultiLaurent d) :
    Continuous (laurentDifferentialNorm f) :=
  (ambientDifferentialNorm_continuous _).comp continuous_subtype_val

theorem laurentDifferentialNorm_nonneg {d : ℕ} (f : MultiLaurent d)
    (x : affineTorus d) : 0 ≤ laurentDifferentialNorm f x := Real.sqrt_nonneg _

/-- Manuscript `lem:uniform-gradient` for the original Laurent polynomials.
Finiteness of the two excluded sets is a separate theorem, not a premise here.-/
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

theorem laurentRegularDomain_isOpen {d : ℕ} (f : MultiLaurent d) :
    IsOpen (laurentRegularDomain f) := polynomialRegularDomain_isOpen _

theorem laurentVectorField_contDiffAt {d : ℕ} (f : MultiLaurent d)
    {a : ℂ} {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → ℂ) => laurentVectorField f az.1 az.2) (a, z) :=
  polynomialVectorField_contDiffAt _ hz

theorem laurentVectorField_embedded_norm {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ‖torusTangentMap z (laurentVectorField f a z)‖ =
      ‖a‖ / laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz.1⟩ :=
  polynomialVectorField_embedded_norm _ a hz

/-- Squared norm identity used to recognize the regular ODE domain.-/
theorem laurentDifferentialNorm_sq {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    laurentDifferentialNorm f ⟨torusEmbed z, embed_mem hz⟩ ^ 2 =
      polynomialTorusNormSq (laurentRepresentative f) z := by
  unfold laurentDifferentialNorm
  rw [ambientDifferentialNorm_eq_restricted, restrictedDifferential_norm_sq]
  rfl

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
In particular, a bounded proper radius prevents coordinates from approaching zero.-/
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
contained in the regular domain, not just bounded in the proper radius.-/
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

/-- Linear growth in the proper embedded metric from the uniform gradient bound.-/
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
Both the derivative and the radius are measured after the proper embedding.-/
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
