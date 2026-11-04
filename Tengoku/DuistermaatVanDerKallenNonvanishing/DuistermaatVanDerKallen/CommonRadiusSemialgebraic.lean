import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolynomialSignFamilies
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Semialgebraic descriptions for the exact common-radius families. The
parameters remain coordinates; no component or path bound is inferred. -/

namespace DuistermaatVanDerKallen
noncomputable section

abbrev AmbientRealIndex (d : ℕ) := (Fin d ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)
abbrev RadiusFamilyIndex (d : ℕ) := Fin 2 ⊕ AmbientRealIndex d

def radiusFamilyPoint {d : ℕ} (q : RadiusFamilyIndex d → ℝ) : TorusAmbient d :=
  WithLp.toLp 2 (complexCoordinates (fun i => q (.inr i)))

def smallGradientTotalFamily {d : ℕ} (g : Fin d → AmbientPolynomial d) :
    Set (RadiusFamilyIndex d → ℝ) :=
  {q | 1 < q (.inl 0) ∧ 0 < q (.inl 1) ∧
    radiusFamilyPoint q ∈ smallGradientSphere g (q (.inl 0)) (q (.inl 1))}

/--
@isnad1 id=eq.0h3v.s6.52800d7041ee from=translated src=- shape=d92ba5c6 vocab=c333bd34
-/
theorem complexCoordinates_mul {ι : Type*} (x : (ι ⊕ ι) → ℝ) (R : ℝ) :
    complexCoordinates (fun i => R * x i) = R • complexCoordinates x := by
  funext i
  apply Complex.ext <;> simp [complexCoordinates]

/-- Both the radius and small-gradient threshold are free coordinates.
@isnad1 id=issemial.0h2v.s3.1c5e0b0c81f5 from=translated src=- shape=befff756 vocab=b509aae9
-/
theorem isSemialgebraic_smallGradientTotalFamily {d : ℕ} (g : Fin d → AmbientPolynomial d) :
    IsSemialgebraic (RadiusFamilyIndex d) (smallGradientTotalFamily g) := by
  let r : MvPolynomial (RadiusFamilyIndex d) ℝ := MvPolynomial.X (.inl 0)
  let e : MvPolynomial (RadiusFamilyIndex d) ℝ := MvPolynomial.X (.inl 1)
  let U (i : AmbientRealIndex d) : MvPolynomial (RadiusFamilyIndex d) ℝ := MvPolynomial.X (.inr i)
  let Z (i : AmbientRealIndex d) : MvPolynomial (RadiusFamilyIndex d) ℝ := r * U i
  have hscale (q : RadiusFamilyIndex d → ℝ) :
      WithLp.toLp 2 (complexCoordinates (fun i => MvPolynomial.eval q (Z i))) =
        q (.inl 0) • radiusFamilyPoint q := by
    apply PiLp.ext
    intro i
    simp only [Z, r, U, map_mul, MvPolynomial.eval_X, complexCoordinates_mul]
    rfl
  have ht : IsSemialgebraic (AmbientRealIndex d)
      {x | WithLp.toLp 2 (complexCoordinates x) ∈ affineTorus d} :=
    isComplexSemialgebraic_affineTorus d
  have hs : IsSemialgebraic (AmbientRealIndex d)
      {x | ‖WithLp.toLp 2 (complexCoordinates x)‖ = 1} :=
    isComplexSemialgebraic_euclidean_sphere (by norm_num : (0 : ℝ) ≤ 1)
  have h := (IsSemialgebraic.lt 1 r).inter ((IsSemialgebraic.lt 0 e).inter
    ((hs.polynomial_preimage U).inter ((ht.polynomial_preimage Z).inter
      (isSemialgebraic_weighted_differential_bound g Z r e))))
  convert h using 1
  ext q
  simp only [smallGradientTotalFamily, smallGradientSphere, Set.mem_ofPred_eq,
    Set.mem_inter_iff, Set.mem_preimage, r, e, U, MvPolynomial.eval_X, map_zero, map_one,
    hscale, radiusFamilyPoint]
  constructor
  · rintro ⟨hr, he, hnorm, ht, hg⟩
    exact ⟨hr, he, hnorm, ht, (lt_trans zero_lt_one hr).le, he.le, hg⟩
  · rintro ⟨hr, he, hnorm, ht, _, _, hg⟩
    exact ⟨hr, he, hnorm, ht, hg⟩

/-- Every admissible fiber is the original sphere family, with the induced
L2 ambient metric and both coordinate directions of escape.
@isnad1 id=iscomple.2h4v.s6.ab0f1d008b13 from=translated src=- shape=c2c1f0a9 vocab=01eae9bb
-/
theorem isComplexSemialgebraic_smallGradientSphere {d : ℕ}
    (g : Fin d → AmbientPolynomial d) {R ε : ℝ} (hR : 1 < R) (hε : 0 < ε) :
    IsComplexSemialgebraic {x : (Fin d ⊕ Fin d) → ℂ |
      WithLp.toLp 2 x ∈ smallGradientSphere g R ε} := by
  let P : RadiusFamilyIndex d → MvPolynomial (AmbientRealIndex d) ℝ :=
    Sum.elim (fun i : Fin 2 => MvPolynomial.C (if i = 0 then R else ε)) MvPolynomial.X
  have h := (isSemialgebraic_smallGradientTotalFamily g).polynomial_preimage P
  simpa [P, smallGradientTotalFamily, radiusFamilyPoint, IsComplexSemialgebraic, hR, hε] using h

end
end DuistermaatVanDerKallen
