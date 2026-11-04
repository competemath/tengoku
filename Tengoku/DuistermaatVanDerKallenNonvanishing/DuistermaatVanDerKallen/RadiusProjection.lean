import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CommonRadiusSemialgebraic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact radius set is a coordinate projection of an explicitly proved
semialgebraic incidence set. Projection closure itself remains unproved. -/

namespace DuistermaatVanDerKallen
noncomputable section

abbrev RadiusIncidenceIndex (d : ℕ) := Fin 1 ⊕ AmbientRealIndex d

def radiusIncidencePoint {d : ℕ} (q : RadiusIncidenceIndex d → ℝ) : TorusAmbient d :=
  WithLp.toLp 2 (complexCoordinates (fun i => q (.inr i)))

def radiusIncidence {d : ℕ} (p : AmbientPolynomial d)
    (g : Fin d → AmbientPolynomial d) (c : ℂ) (ε δ : ℝ) :
    Set (RadiusIncidenceIndex d → ℝ) :=
  {q | 1 < q (.inl 0) ∧ radiusIncidencePoint q ∈ affineTorus d ∧
    ‖radiusIncidencePoint q‖ = q (.inl 0) ∧
    q (.inl 0) * ambientDifferentialNorm g (radiusIncidencePoint q) ≤ ε ∧
    dist (ambientEval p (radiusIncidencePoint q)) c < δ}

/-- The pre-projection set uses precisely the proper radius and restricted norm
of `radiusApproximationSet`, with no witnesses or constraints omitted.
@isnad1 id=issemial.2h6v.s5.c6f90e434790 from=translated src=- shape=adba0eae vocab=a31901d8
-/
theorem isSemialgebraic_radiusIncidence {d : ℕ} (p : AmbientPolynomial d)
    (g : Fin d → AmbientPolynomial d) (c : ℂ) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    IsSemialgebraic (RadiusIncidenceIndex d) (radiusIncidence p g c ε δ) := by
  let r : MvPolynomial (RadiusIncidenceIndex d) ℝ := MvPolynomial.X (.inl 0)
  let Z (i : AmbientRealIndex d) : MvPolynomial (RadiusIncidenceIndex d) ℝ := MvPolynomial.X (.inr i)
  have ht : IsSemialgebraic (AmbientRealIndex d)
      {x | WithLp.toLp 2 (complexCoordinates x) ∈ affineTorus d} :=
    isComplexSemialgebraic_affineTorus d
  have h := (IsSemialgebraic.lt 1 r).inter ((ht.polynomial_preimage Z).inter
    ((isSemialgebraic_euclidean_norm_eq Z r).inter
      ((isSemialgebraic_weighted_differential_bound g Z r (MvPolynomial.C ε)).inter
        (isSemialgebraic_polynomial_dist_lt p Z c (MvPolynomial.C δ)))))
  convert h using 1
  ext q
  simp only [radiusIncidence, radiusIncidencePoint, ambientEval,
    Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, r, Z,
    MvPolynomial.eval_X, MvPolynomial.eval_C, map_one]
  constructor
  · rintro ⟨hr, ht, hn, hg, hp⟩
    have hr0 := (lt_trans zero_lt_one hr).le
    exact ⟨hr, ht, ⟨hr0, hn⟩, ⟨hr0, hε, hg⟩, hδ, hp⟩
  · rintro ⟨hr, ht, ⟨_, hn⟩, ⟨_, _, hg⟩, _, hp⟩
    exact ⟨hr, ht, hn, hg, hp⟩

/-- Exact real-coordinate elimination formula for the original radius set.
@isnad1 id=iff.0h7v.s6.3f8365681ed9 from=translated src=- shape=34667b34 vocab=4732cd01
-/
theorem radiusApproximationSet_iff_projection {d : ℕ} (p : AmbientPolynomial d)
    (g : Fin d → AmbientPolynomial d) (c : ℂ) (ε δ R : ℝ) :
    R ∈ radiusApproximationSet p g c ε δ ↔
      ∃ x : AmbientRealIndex d → ℝ,
        Sum.elim (fun _ : Fin 1 => R) x ∈ radiusIncidence p g c ε δ := by
  constructor
  · rintro ⟨hR, y, hy, hn, hg, hp⟩
    refine ⟨realCoordinates (fun i => y i), ?_⟩
    have he : radiusIncidencePoint (Sum.elim (fun _ : Fin 1 => R)
        (realCoordinates (fun i => y i))) = y := by
      apply PiLp.ext
      intro i
      simp [radiusIncidencePoint]
    simpa only [radiusIncidence, Set.mem_ofPred_eq, Sum.elim_inl, he] using
      And.intro hR ⟨hy, hn, hg, hp⟩
  · rintro ⟨x, hR, hy, hn, hg, hp⟩
    exact ⟨hR, radiusIncidencePoint (Sum.elim (fun _ : Fin 1 => R) x), hy, hn, hg, hp⟩

/-- OPEN standard input: closure under real coordinate projection. This is a
proposition, not an axiom or a theorem instance.-/
def SemialgebraicProjectionObligation : Prop :=
  ∀ (ι κ : Type) [Finite ι] [Finite κ] (S : Set ((ι ⊕ κ) → ℝ)),
    IsSemialgebraic (ι ⊕ κ) S →
      IsSemialgebraic ι {x | ∃ y : κ → ℝ, Sum.elim x y ∈ S}

/-- Discharges the radius-tail obligation from exactly the stated projection
input, using the checked incidence set and univariate polynomial tail theorem.
@isnad1 id=radiusta.1h0v.s1.1955bfb0d3fe from=translated src=- shape=1d48f1ac vocab=939deca5
-/
theorem radiusTail_of_semialgebraic_projection
    (hproj : SemialgebraicProjectionObligation) : RadiusTailObligation := by
  intro d p g c ε δ hε hδ hU
  have hsa := hproj (Fin 1) (AmbientRealIndex d) (radiusIncidence p g c ε δ)
    (isSemialgebraic_radiusIncidence p g c hε.le hδ.le)
  have hU' : ∀ B : ℝ, ∃ t, B ≤ t ∧
      (fun _ : Fin 1 => t) ∈ {x | ∃ y : AmbientRealIndex d → ℝ,
        Sum.elim x y ∈ radiusIncidence p g c ε δ} := by
    intro B
    obtain ⟨t, ht, hBt⟩ := hU B
    exact ⟨t, hBt, (radiusApproximationSet_iff_projection p g c ε δ t).mp ht⟩
  obtain ⟨B, hB⟩ := hsa.contains_tail_of_unbounded hU'
  exact ⟨B, fun R hR => (radiusApproximationSet_iff_projection p g c ε δ R).mpr (hB R hR)⟩

end
end DuistermaatVanDerKallen
