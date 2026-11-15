import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

universe u v

variable {F : Type u} [Field F] (k : Type v) [Field k] [Algebra F k]

def evalEvalBC (p : F[X][Y]) (x y : k) : k :=
  (p.map (mapRingHom (algebraMap F k))).evalEval x y

variable [DecidableEq k]

def IsRationallyRepresented (W₁ W₂ : WeierstrassCurve F)
    (α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point) : Prop :=
  ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      evalEvalBC k dX x y ≠ 0 ∧ evalEvalBC k dY x y ≠ 0 ∧
        ∃ h', α (.some x y h) =
          .some (evalEvalBC k nX x y / evalEvalBC k dX x y)
            (evalEvalBC k nY x y / evalEvalBC k dY x y) h'

def rationalHomSet (W₁ W₂ : WeierstrassCurve F) :
    Set ((W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point) :=
  {α | α = 0 ∨ IsRationallyRepresented k W₁ W₂ α}

def rationalEndSubring (W : WeierstrassCurve F) :
    Subring (AddMonoid.End (W.baseChange k).toAffine.Point) :=
  Subring.closure (rationalHomSet k W W)

/--
@isnad1 id=mem.0h4v.s9.3c6b91ee280b from=translated src=- shape=12522fed vocab=a2bb40a4
-/
theorem zero_mem_rationalHomSet (W₁ W₂ : WeierstrassCurve F) :
    (0 : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point) ∈
      rationalHomSet k W₁ W₂ :=
  Or.inl rfl

/--
@isnad1 id=isration.0h3v.s6.6c1ed6e17519 from=translated src=- shape=dea975b8 vocab=8a073fd1
-/
theorem isRationallyRepresented_id (W : WeierstrassCurve F) :
    IsRationallyRepresented k W W (AddMonoidHom.id _) := by
  refine ⟨C X, 1, X, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  simp only [evalEvalBC, Polynomial.map_one, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_mapRingHom,
    evalEval_one, evalEval_C, eval_X, evalEval_X, ne_eq, one_ne_zero, not_false_eq_true, div_one,
    AddMonoidHom.id_apply, true_and]
  exact ⟨h, trivial⟩

/--
@isnad1 id=isration.1h5v.s7.d7d97d69fa26 from=translated src=- shape=e430143b vocab=15bc1b9e
-/
theorem isRationallyRepresented_map_of_pow (W : WeierstrassCurve F) (σ : k →ₐ[F] k) (q : ℕ)
    (hσ : ∀ x, σ x = x ^ q) :
    IsRationallyRepresented k W W (Affine.Point.map (W' := W) σ) := by
  refine ⟨C (X ^ q), 1, X ^ q, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : F[X][Y]) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C (X ^ q) : F[X][Y]) x y / evalEvalBC k (1 : F[X][Y]) x y = σ x := by
    simp [evalEvalBC, Polynomial.evalEval, hσ]
  have e2 : evalEvalBC k (X ^ q : F[X][Y]) x y / evalEvalBC k (1 : F[X][Y]) x y = σ y := by
    simp [evalEvalBC, Polynomial.evalEval, hσ]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : k, a = σ x → b = σ y →
      ∃ h', Affine.Point.map (W' := W) σ (.some x y h) = .some a b h' from H _ _ e1 e2
  rintro a b rfl rfl
  exact ⟨_, Affine.Point.map_some σ h⟩

/--
@isnad1 id=mem.1h5v.s9.f9c4580e2539 from=translated src=- shape=e68969cf vocab=8f19f9c7
-/
theorem map_mem_rationalEndSubring_of_pow (W : WeierstrassCurve F) (σ : k →ₐ[F] k) (q : ℕ)
    (hσ : ∀ x, σ x = x ^ q) :
    (Affine.Point.map (W' := W) σ : AddMonoid.End (W.baseChange k).toAffine.Point) ∈
      rationalEndSubring k W :=
  Subring.subset_closure (Or.inr (isRationallyRepresented_map_of_pow k W σ q hσ))

/--
@isnad1 id=mem.0h3v.s9.299409f2e58e from=translated src=- shape=94af060a vocab=97ccbaee
-/
theorem one_mem_rationalEndSubring (W : WeierstrassCurve F) :
    (1 : AddMonoid.End (W.baseChange k).toAffine.Point) ∈ rationalEndSubring k W :=
  Subring.one_mem _

/--
@isnad1 id=mem.0h3v.s8.f1229d44029f from=translated src=- shape=5757d42d vocab=3ad51163
-/
theorem id_mem_rationalHomSet (W : WeierstrassCurve F) :
    (AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  Or.inr (isRationallyRepresented_id k W)

end WeierstrassCurve

end
