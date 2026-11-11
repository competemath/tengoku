/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Seed.GroupTheory.Perm.Cycle.Type
public import Tengoku.Seed.LinearAlgebra.Matrix.Permutation
public import Tengoku.Aintlib.BernoulliRegular.GaussSum.SignInvariant.BlockDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Determinant bookkeeping for the block decomposition

This file reorganizes the `δ₀ +` character basis so that the normalized DFT is
monomial outside the surviving quadratic line. This packages the determinant
contribution of the trivial block and prepares the remaining non-self-dual
character-pair bookkeeping.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

local instance : DecidableEq (DirichletCharacter ℂ p) := Classical.decEq _
local instance : DecidableEq (Option (DirichletCharacter ℂ p)) := Classical.decEq _

/-- Replace the trivial Dirichlet character by the constant-`1` function, but
leave every other character unchanged.-/
def constOneDirichletCharacterFamily (χ : DirichletCharacter ℂ p) : ZMod p → ℂ :=
  by
    classical
    exact if hχ : χ = 1 then fun _ : ZMod p ↦ (1 : ℂ) else (χ : ZMod p → ℂ)

omit hp in
/--
@isnad1 id=eq.0h1v.s5.6c8d37b6450b from=translated src=- shape=5d438aaa vocab=52eabd48
-/
@[simp] theorem constOneDirichletCharacterFamily_one :
    constOneDirichletCharacterFamily (p := p) (1 : DirichletCharacter ℂ p) =
      (fun _ : ZMod p ↦ (1 : ℂ)) := by
  classical
  rw [constOneDirichletCharacterFamily]
  simp

omit hp in
/-- Away from the trivial character, the modified family is the character itself.
@isnad1 id=eq.1h2v.s6.71783661b957 from=translated src=- shape=230e590d vocab=f8f25253
-/
theorem constOneDirichletCharacterFamily_eq_character {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) :
    constOneDirichletCharacterFamily (p := p) χ = (χ : ZMod p → ℂ) := by
  classical
  rw [constOneDirichletCharacterFamily]
  simp [hχ]

/--
@isnad1 id=eq.0h1v.s8.3dc541b4d19f from=translated src=- shape=bc6d945d vocab=cb3239a5
-/
@[simp] theorem restrictUnits_deltaZero :
    restrictUnitsLinear (p := p) (deltaZeroFunction (p := p)) = 0 := by
  ext u
  have hu : ((u : (ZMod p)) ≠ 0) := Units.ne_zero u
  simp [restrictUnitsLinear, deltaZeroFunction, hu]

/--
@isnad1 id=eq.0h2v.s9.e8deec1c35d7 from=translated src=- shape=e2282992 vocab=a24246e6
-/
@[simp] theorem restrictUnits_constOneDirichletCharacterFamily
    (χ : DirichletCharacter ℂ p) :
    restrictUnitsLinear (p := p) (constOneDirichletCharacterFamily (p := p) χ) =
      (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ) := by
  classical
  by_cases hχ : χ = 1
  · subst hχ
    ext u
    rw [constOneDirichletCharacterFamily_one (p := p)]
    simp [restrictUnitsLinear, dirichletCharacterUnitMonoidHom]
  · ext u
    rw [constOneDirichletCharacterFamily_eq_character (p := p) hχ]
    simp [restrictUnitsLinear, dirichletCharacterUnitMonoidHom]

/-- The characters remain linearly independent after replacing the trivial
character by the constant-`1` function.
@isnad1 id=linearin.0h1v.s5.a1ddce8fb2ff from=translated src=- shape=bb94f6cd vocab=1eb2ecf9
-/
theorem linearIndependent_constOneDirichletCharacterFamily :
    LinearIndependent ℂ (constOneDirichletCharacterFamily (p := p)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha χ
  have h_units :
      ∑ ψ, a ψ • (dirichletCharacterUnitMonoidHom (p := p) ψ : (ZMod p)ˣ → ℂ) = 0 := by
    simpa using congrArg (restrictUnitsLinear (p := p)) ha
  exact
    (Fintype.linearIndependent_iff.mp
      (linearIndependent_dirichletCharactersOnUnits (p := p))) a h_units χ

/-- `δ₀` is not in the span of the modified character family.
@isnad1 id=not.0h1v.s7.e0fc471b1c3c from=translated src=- shape=b2074681 vocab=77ab2fa9
-/
theorem deltaZero_not_mem_span_constOneDirichletCharacterFamily :
    deltaZeroFunction (p := p) ∉
      Submodule.span ℂ
        (Set.range fun χ : DirichletCharacter ℂ p ↦
          constOneDirichletCharacterFamily (p := p) χ) := by
  intro hdelta
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (R := ℂ)
      (v := fun χ : DirichletCharacter ℂ p ↦
        constOneDirichletCharacterFamily (p := p) χ)).mp hdelta
  have h_units :
      ∑ χ, a χ • (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ) = 0 := by
    simpa using congrArg (restrictUnitsLinear (p := p)) ha
  have ha_zero : ∀ χ : DirichletCharacter ℂ p, a χ = 0 :=
    (Fintype.linearIndependent_iff.mp
      (linearIndependent_dirichletCharactersOnUnits (p := p))) a h_units
  have hone : (1 : ℂ) = 0 := by
    simpa [evalAtZeroLinear, deltaZeroFunction, constOneDirichletCharacterFamily,
      dirichletCharacter_apply_zero, ha_zero] using
      congrArg (evalAtZeroLinear (p := p)) ha
  exact one_ne_zero hone

/-- The ambient family for determinant computations: `δ₀`, the constant-`1`
function, and all nontrivial Dirichlet characters.-/
def deltaZeroConstOneDirichletCharacterFamily :
    Option (DirichletCharacter ℂ p) → (ZMod p → ℂ) :=
  fun o ↦ Option.casesOn' o (deltaZeroFunction (p := p))
    (constOneDirichletCharacterFamily (p := p))

/-- Adjoining `δ₀` to the modified family keeps it linearly independent.
@isnad1 id=linearin.0h1v.s5.dd6317281ec6 from=translated src=- shape=ed436806 vocab=2bfb9de4
-/
theorem linearIndependent_deltaZeroConstOneDirichletCharacterFamily :
    LinearIndependent ℂ (deltaZeroConstOneDirichletCharacterFamily (p := p)) := by
  change LinearIndependent ℂ
    (fun o ↦ Option.casesOn' o (deltaZeroFunction (p := p))
      (constOneDirichletCharacterFamily (p := p)))
  exact (linearIndependent_constOneDirichletCharacterFamily (p := p)).option
      (x := deltaZeroFunction (p := p))
      (deltaZero_not_mem_span_constOneDirichletCharacterFamily (p := p))

/-- A basis adapted to the trivial `δ₀/1` block: `δ₀`, the constant-`1`
function, and all nontrivial Dirichlet characters.-/
def deltaZeroConstOneDirichletCharacterBasis :
    Module.Basis (Option (DirichletCharacter ℂ p)) ℂ (ZMod p → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_deltaZeroConstOneDirichletCharacterFamily (p := p)) <| by
      rw [Fintype.card_option, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
        Nat.totient_prime hp.out]
      rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
      exact Nat.sub_add_cancel hp.out.one_le

/--
@isnad1 id=eq.0h1v.s7.a4c48ccf6bd2 from=translated src=- shape=b212168d vocab=e58f97fa
-/
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_none :
    deltaZeroConstOneDirichletCharacterBasis (p := p) none = deltaZeroFunction (p := p) := by
  rw [deltaZeroConstOneDirichletCharacterBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/--
@isnad1 id=eq.0h2v.s7.00c0b7e231fe from=translated src=- shape=eb9b77c8 vocab=7ed7194e
-/
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some
    (χ : DirichletCharacter ℂ p) :
    deltaZeroConstOneDirichletCharacterBasis (p := p) (some χ) =
      constOneDirichletCharacterFamily (p := p) χ := by
  rw [deltaZeroConstOneDirichletCharacterBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/--
@isnad1 id=eq.0h1v.s7.b144e1c179df from=translated src=- shape=c0272955 vocab=3acd4d5f
-/
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some_one :
    deltaZeroConstOneDirichletCharacterBasis (p := p)
        (some (1 : DirichletCharacter ℂ p)) =
      (fun _ : ZMod p ↦ (1 : ℂ)) := by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some, constOneDirichletCharacterFamily_one]

/-- On a nontrivial character, the adapted basis vector is that character.
@isnad1 id=eq.1h2v.s7.9484b49018d0 from=translated src=- shape=183a3e01 vocab=3acd4d5f
-/
theorem deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    deltaZeroConstOneDirichletCharacterBasis (p := p) (some χ) = (χ : ZMod p → ℂ) := by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some,
    constOneDirichletCharacterFamily_eq_character, hχ]

/-- The underlying involution on the adapted basis indices.-/
def normalizedDftConstOneBasisPermFun :
    Option (DirichletCharacter ℂ p) → Option (DirichletCharacter ℂ p) :=
  by
    classical
    exact fun
      | none => some 1
      | some χ => if hχ : χ = 1 then none else some χ⁻¹

/-- The permutation of the adapted basis induced by the normalized DFT.-/
def normalizedDftConstOneBasisPerm :
    Equiv.Perm (Option (DirichletCharacter ℂ p)) where
  toFun := normalizedDftConstOneBasisPermFun (p := p)
  invFun := normalizedDftConstOneBasisPermFun (p := p)
  left_inv := by
    classical
    intro i
    cases i with
    | none =>
        simp [normalizedDftConstOneBasisPermFun]
    | some χ =>
        by_cases hχ : χ = 1
        · subst hχ
          simp [normalizedDftConstOneBasisPermFun]
        · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
          simp [normalizedDftConstOneBasisPermFun, hχ, hχinv]
  right_inv := by
    classical
    intro i
    cases i with
    | none =>
        simp [normalizedDftConstOneBasisPermFun]
    | some χ =>
        by_cases hχ : χ = 1
        · subst hχ
          simp [normalizedDftConstOneBasisPermFun]
        · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
          simp [normalizedDftConstOneBasisPermFun, hχ, hχinv]

/-- The scalar attached to each basis vector under the normalized DFT.-/
def normalizedDftConstOneBasisScalar (i : Option (DirichletCharacter ℂ p)) : ℂ :=
  by
    classical
    exact match i with
    | none => (Real.sqrt p : ℂ)⁻¹
    | some χ =>
        if hχ : χ = 1 then ((Real.sqrt p : ℂ)⁻¹) * p
        else ((Real.sqrt p : ℂ)⁻¹) *
          (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p)))

/-- The normalized DFT is monomial in the adapted basis: it permutes the basis
vectors and rescales them.
@isnad1 id=eq.0h2v.s9.d93b4f8e90ca from=translated src=- shape=772dd6bc vocab=32cb5a07
-/
theorem normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm
    (i : Option (DirichletCharacter ℂ p)) :
    normalizedDft p (deltaZeroConstOneDirichletCharacterBasis (p := p) i) =
      normalizedDftConstOneBasisScalar (p := p) i •
        deltaZeroConstOneDirichletCharacterBasis (p := p)
          ((normalizedDftConstOneBasisPerm (p := p)) i) := by
  classical
  cases i with
  | none =>
      rw [deltaZeroConstOneDirichletCharacterBasis_apply_none,
        normalizedDft_deltaZero, normalizedDftConstOneBasisScalar]
      simp [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
  | some χ =>
      by_cases hχ : χ = 1
      · subst hχ
        rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_one, normalizedDft_constOne,
          normalizedDftConstOneBasisScalar]
        simp [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
      · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
        rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one (p := p) hχ]
        ext x
        rw [normalizedDft_apply]
        rw [congrFun (dft_eq_scalar_smul_inv_character (p := p) (χ := χ) hχ) x]
        simp [normalizedDftConstOneBasisScalar, normalizedDftConstOneBasisPerm,
          normalizedDftConstOneBasisPermFun, hχ, hχinv,
          deltaZeroConstOneDirichletCharacterBasis_apply_some,
          constOneDirichletCharacterFamily_eq_character, smul_eq_mul,
          mul_left_comm, mul_comm]

/-- Hence its matrix in the adapted basis is a permutation matrix times a diagonal.
@isnad1 id=eq.0h1v.s10.4d6a51e49cd8 from=translated src=- shape=ce13cb6e vocab=89f1c429
-/
theorem toMatrix_deltaZeroConstOneDirichletCharacterBasis_normalizedDft :
    LinearMap.toMatrix
        (deltaZeroConstOneDirichletCharacterBasis (p := p))
        (deltaZeroConstOneDirichletCharacterBasis (p := p))
        (normalizedDft p) =
      (((normalizedDftConstOneBasisPerm (p := p))⁻¹).permMatrix ℂ) *
        Matrix.diagonal (normalizedDftConstOneBasisScalar (p := p)) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm]
  by_cases hij : i = normalizedDftConstOneBasisPerm (p := p) j
  · subst hij
    simp [Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · have hneq : ((normalizedDftConstOneBasisPerm (p := p))⁻¹) i ≠ j := by
      intro h
      apply hij
      simpa using congrArg (normalizedDftConstOneBasisPerm (p := p)) h
    have hneq' : ¬ Equiv.symm (normalizedDftConstOneBasisPerm (p := p)) i = j := by
      simpa using hneq
    have hsingle :
        ((deltaZeroConstOneDirichletCharacterBasis (p := p)).repr
            (normalizedDftConstOneBasisScalar (p := p) j •
              (deltaZeroConstOneDirichletCharacterBasis (p := p))
                ((normalizedDftConstOneBasisPerm (p := p)) j))) i = 0 := by
      simp [Module.Basis.repr_self, hij]
    simpa only [Matrix.mul_diagonal, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Equiv.Perm.coe_inv, Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul, hneq',
      ite_false]
      using hsingle

/-- The determinant of that monomial matrix: the sign of the permutation times the
product of the scalars.
@isnad1 id=eq.0h1v.s10.9ace27ff5427 from=translated src=- shape=b020e4ac vocab=f942e9ee
-/
theorem det_normalizedDft_eq_sign_mul_prod_basisScalars :
    LinearMap.det (normalizedDft p) =
      (Equiv.Perm.sign (normalizedDftConstOneBasisPerm (p := p)) : ℂ) *
        ∏ i, normalizedDftConstOneBasisScalar (p := p) i := by
  classical
  rw [← LinearMap.det_toMatrix (deltaZeroConstOneDirichletCharacterBasis (p := p))
      (normalizedDft p),
    toMatrix_deltaZeroConstOneDirichletCharacterBasis_normalizedDft (p := p),
    Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal]
  simp

omit hp in
/-- The index permutation is an involution — it is `χ ↦ χ⁻¹` on the character slots.
@isnad1 id=eq.0h1v.s7.9bc1aeb6f25a from=translated src=- shape=76c19229 vocab=923d1b40
-/
theorem normalizedDftConstOneBasisPerm_sq :
    (normalizedDftConstOneBasisPerm (p := p)) ^ 2 = 1 := by
  ext i
  cases i with
  | none =>
      simp [pow_two, normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
  | some χ =>
      classical
      by_cases hχ : χ = 1
      · subst hχ
        simp [pow_two, normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
      · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
        simp [pow_two, normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun, hχ,
          hχinv]

/-- Its fixed points are exactly the self-dual indices: `none`, `1` and the quadratic
character.
@isnad1 id=iff.1h2v.s7.ee30a1fcf19f from=translated src=- shape=d45ec9c9 vocab=f0038359
-/
theorem mem_fixedPoints_normalizedDftConstOneBasisPerm_iff
    (hp₂ : p ≠ 2) (i : Option (DirichletCharacter ℂ p)) :
    i ∈ Function.fixedPoints (normalizedDftConstOneBasisPerm (p := p)) ↔
      i = some (quadraticCharComplex p) := by
  classical
  cases i with
  | none =>
      simp [Function.fixedPoints, Function.IsFixedPt, normalizedDftConstOneBasisPerm,
        normalizedDftConstOneBasisPermFun]
  | some χ =>
      by_cases hχ : χ = 1
      · subst hχ
        have hquad_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
          quadraticCharComplex_ne_one (p := p) hp₂
        constructor
        · intro hfix
          simp [Function.fixedPoints, Function.IsFixedPt, normalizedDftConstOneBasisPerm,
            normalizedDftConstOneBasisPermFun] at hfix
        · intro hquad
          exact False.elim (hquad_ne (Option.some.inj hquad).symm)
      · constructor
        · intro hfix
          have hself : χ⁻¹ = χ := by
            simpa [Function.fixedPoints, Function.IsFixedPt, normalizedDftConstOneBasisPerm,
              normalizedDftConstOneBasisPermFun, hχ] using hfix
          exact congrArg some
            (nontrivial_selfInverse_character_eq_quadratic (p := p) hp₂ hχ hself.symm)
        · intro hquad
          injection hquad with hχquad
          subst hχquad
          have hquad_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
            quadraticCharComplex_ne_one (p := p) hp₂
          change Function.IsFixedPt (normalizedDftConstOneBasisPerm (p := p))
            (some (quadraticCharComplex p))
          simp [Function.IsFixedPt, normalizedDftConstOneBasisPerm,
            normalizedDftConstOneBasisPermFun, hquad_ne, quadraticCharComplex_inv]

/-- There are exactly three such fixed points.
@isnad1 id=eq.1h1v.s8.ac1f0f339b0c from=translated src=- shape=9e89f76e vocab=6594acf9
-/
theorem card_fixedPoints_normalizedDftConstOneBasisPerm (hp₂ : p ≠ 2) :
    Fintype.card (Function.fixedPoints (normalizedDftConstOneBasisPerm (p := p))) = 1 := by
  classical
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨some (quadraticCharComplex p), ?_⟩, ?_⟩
  · exact (mem_fixedPoints_normalizedDftConstOneBasisPerm_iff (p := p) hp₂ _).2 rfl
  · intro x
    exact Subtype.ext <|
      (mem_fixedPoints_normalizedDftConstOneBasisPerm_iff (p := p) hp₂ x.1).1 x.2

/-- The sign of an involution is `(-1)` to the number of its transpositions, i.e. to
half the number of non-fixed points.
@isnad1 id=eq.1h1v.s8.530a4841241d from=translated src=- shape=6df0ae71 vocab=df3d2d5f
-/
theorem sign_normalizedDftConstOneBasisPerm (hp₂ : p ≠ 2) :
    (Equiv.Perm.sign (normalizedDftConstOneBasisPerm (p := p)) : ℂ) =
      (-1 : ℂ) ^ ((p - 1) / 2) := by
  classical
  rw [Equiv.Perm.sign_of_pow_two_eq_one (normalizedDftConstOneBasisPerm_sq (p := p)),
    card_fixedPoints_normalizedDftConstOneBasisPerm (p := p) hp₂,
    Fintype.card_option, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
    Nat.totient_prime hp.out]
  rw [Nat.sub_add_cancel hp.out.one_le]
  simp

/-- The determinant with the permutation sign evaluated.
@isnad1 id=eq.1h1v.s10.ab35b0b544c9 from=translated src=- shape=0ecbc6c9 vocab=bcc2e3e7
-/
theorem det_normalizedDft_eq_signContribution_mul_prod_basisScalars (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) ^ ((p - 1) / 2) * ∏ i, normalizedDftConstOneBasisScalar (p := p) i := by
  rw [det_normalizedDft_eq_sign_mul_prod_basisScalars (p := p),
    sign_normalizedDftConstOneBasisPerm (p := p) hp₂]

/-- The two scalars of a `(χ, χ⁻¹)` block multiply to `χ(-1)`; this is the block
determinant, up to sign.
@isnad1 id=eq.1h2v.s7.f9ecaa95d819 from=translated src=- shape=b5bc9cf3 vocab=0a0c7790
-/
theorem normalizedDftConstOneBasisScalar_mul_inv_eq_eval_neg_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    normalizedDftConstOneBasisScalar (p := p) (some χ) *
      normalizedDftConstOneBasisScalar (p := p) (some χ⁻¹) = χ (-1) := by
  classical
  have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
  have hχmap :=
    normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm
      (p := p) (i := some χ)
  have hχinvmap :=
    normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm
      (p := p) (i := some χ⁻¹)
  rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one (p := p) hχ] at hχmap
  rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one (p := p) hχinv] at hχinvmap
  have hχmap' :
      normalizedDft p (χ : ZMod p → ℂ) =
        normalizedDftConstOneBasisScalar (p := p) (some χ) •
          (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) := by
    simpa [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun, hχ, hχinv,
      constOneDirichletCharacterFamily_eq_character (p := p) hχinv] using hχmap
  have hχinvmap' :
      normalizedDft p (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) =
        normalizedDftConstOneBasisScalar (p := p) (some χ⁻¹) •
          ((χ : DirichletCharacter ℂ p) : ZMod p → ℂ) := by
    simpa [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun, hχinv, hχ,
      constOneDirichletCharacterFamily_eq_character (p := p) hχ] using hχinvmap
  have htwice :
      normalizedDft p (normalizedDft p (χ : ZMod p → ℂ)) =
        (normalizedDftConstOneBasisScalar (p := p) (some χ) *
          normalizedDftConstOneBasisScalar (p := p) (some χ⁻¹)) •
            (χ : ZMod p → ℂ) := by
    rw [hχmap', LinearMap.map_smul, hχinvmap']
    simp [smul_smul]
  have hsq :
      normalizedDft p (normalizedDft p (χ : ZMod p → ℂ)) =
        χ (-1) • (χ : ZMod p → ℂ) := by
    ext x
    rw [normalizedDft_sq_apply]
    by_cases hx : x = 0
    · subst hx
      simp [dirichletCharacter_apply_zero]
    · calc
        χ (-x) = χ ((-1 : ZMod p) * x) := by ring_nf
        _ = χ (-1) * χ x := by rw [map_mul]
        _ = (χ (-1) • (χ : ZMod p → ℂ)) x := by simp [smul_eq_mul]
  have hone : χ (1 : ZMod p) = 1 := MulChar.map_one χ
  have hcoeff := (congrFun htwice (1 : ZMod p)).symm.trans (congrFun hsq (1 : ZMod p))
  simpa [hone, smul_eq_mul] using hcoeff

/-- The nontrivial characters other than the quadratic character. For `p ≠ 2`,
these are exactly the non-self-dual characters.-/
def nonselfdualCharacterFinset : Finset (DirichletCharacter ℂ p) :=
  (Finset.univ.erase (1 : DirichletCharacter ℂ p)).erase (quadraticCharComplex p)

/-- The `δ₀` scalar times the trivial-character scalar is `1`: the normalisation
`(√p)⁻¹ · ((√p)⁻¹ · p) = 1`, using `√p ^ 2 = p`.
@isnad1 id=eq.0h1v.s6.58abe739227c from=translated src=- shape=12d1b4ae vocab=cf8f688f
-/
theorem normalizedDftConstOneBasisScalar_none_mul_some_one :
    normalizedDftConstOneBasisScalar (p := p) none *
      normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) = 1 := by
  have hp_nonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
  have hsq : ((Real.sqrt p : ℂ) ^ 2) = (p : ℂ) := by
    exact_mod_cast (Real.sq_sqrt hp_nonneg)
  simp [normalizedDftConstOneBasisScalar]
  field_simp [hsqrt_ne]
  simpa [pow_two, mul_assoc] using hsq.symm

/-- The product of the DFT scalars over all Dirichlet characters (in the `some`
slot), split off the trivial character `1` and the quadratic character: it equals
the scalar at `1`, times the scalar at the quadratic character, times the product
over the non-self-dual characters. Peels `χ = 1` and `χ = quadraticChar` off the
full character product via `Finset.mul_prod_erase`.
@isnad1 id=eq.1h1v.s7.f437869bc35f from=translated src=- shape=023dd749 vocab=073ed142
-/
theorem prod_someBasisScalars_eq_trivialScalar_mul_quadraticScalar_mul_prod_nonselfdualScalars
    (hp₂ : p ≠ 2) :
    ∏ χ : DirichletCharacter ℂ p, normalizedDftConstOneBasisScalar (p := p) (some χ) =
      normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterFinset (p := p))
            (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
  let q : DirichletCharacter ℂ p := quadraticCharComplex p
  have hq_ne : q ≠ (1 : DirichletCharacter ℂ p) := quadraticCharComplex_ne_one (p := p) hp₂
  let f : DirichletCharacter ℂ p → ℂ :=
    fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)
  have h1 :
      f 1 * Finset.prod (Finset.univ.erase (1 : DirichletCharacter ℂ p)) f = ∏ χ, f χ := by
    simpa [f] using
      (Finset.mul_prod_erase (Finset.univ : Finset (DirichletCharacter ℂ p)) f (by simp))
  have hq :
      f q * Finset.prod ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).erase q) f =
        Finset.prod (Finset.univ.erase (1 : DirichletCharacter ℂ p)) f := by
    simpa [f] using
      (Finset.mul_prod_erase
        ((Finset.univ : Finset (DirichletCharacter ℂ p)).erase (1 : DirichletCharacter ℂ p))
        f (by simp [hq_ne]))
  calc
    ∏ χ, f χ = f 1 * Finset.prod (Finset.univ.erase (1 : DirichletCharacter ℂ p)) f := by
      symm
      exact h1
    _ = f 1 * (f q * Finset.prod (nonselfdualCharacterFinset (p := p)) f) := by
      rw [← hq]
      simp [nonselfdualCharacterFinset, q]
    _ = normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) *
          (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
            Finset.prod (nonselfdualCharacterFinset (p := p))
              (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
        simp [f, q]

/-- Splitting the scalar product off the trivial and quadratic lines.
@isnad1 id=eq.1h1v.s7.45d791007cda from=translated src=- shape=9e9e2fde vocab=de34d728
-/
theorem prod_basisScalars_eq_quadraticScalar_mul_prod_nonselfdualScalars (hp₂ : p ≠ 2) :
    ∏ i, normalizedDftConstOneBasisScalar (p := p) i =
      normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
        Finset.prod (nonselfdualCharacterFinset (p := p))
          (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)) := by
  rw [Fintype.prod_option,
    prod_someBasisScalars_eq_trivialScalar_mul_quadraticScalar_mul_prod_nonselfdualScalars
      (p := p) hp₂,
    ← mul_assoc, normalizedDftConstOneBasisScalar_none_mul_some_one (p := p), one_mul]

/-- The determinant after that split.
@isnad1 id=eq.1h1v.s10.93be9ec2cd72 from=translated src=- shape=ee0d492c vocab=81ba57e9
-/
theorem det_normalizedDft_eq_quadraticScalar_mul_prod_nonselfdualScalars (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) ^ ((p - 1) / 2) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterFinset (p := p))
            (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
  rw [det_normalizedDft_eq_signContribution_mul_prod_basisScalars (p := p) hp₂,
    prod_basisScalars_eq_quadraticScalar_mul_prod_nonselfdualScalars (p := p) hp₂]

/-- A chosen indexing of Dirichlet characters by `Fin`, used to pick one
representative from each inverse-pair orbit.-/
noncomputable def characterIndexEquiv :
    DirichletCharacter ℂ p ≃ Fin (Fintype.card (DirichletCharacter ℂ p)) :=
  Fintype.equivFin (DirichletCharacter ℂ p)

/-- Membership in the non-self-dual characters.
@isnad1 id=iff.0h2v.s7.69e898319cf5 from=translated src=- shape=8a372bb2 vocab=5fb9c79a
-/
theorem mem_nonselfdualCharacterFinset_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ nonselfdualCharacterFinset (p := p) ↔
      χ ≠ 1 ∧ χ ≠ quadraticCharComplex p := by
  constructor
  · intro h
    have h' : χ ≠ quadraticCharComplex p ∧ χ ≠ 1 := by
      simpa [nonselfdualCharacterFinset] using h
    exact ⟨h'.2, h'.1⟩
  · intro h
    simp [nonselfdualCharacterFinset, h.1, h.2]

/-- The non-self-dual characters are stable under inversion.
@isnad1 id=mem.1h2v.s7.fe0d1968fd0c from=translated src=- shape=d814bd15 vocab=98b8cdb6
-/
theorem inv_mem_nonselfdualCharacterFinset {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ⁻¹ ∈ nonselfdualCharacterFinset (p := p) := by
  rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχ1, hχquad⟩
  rw [mem_nonselfdualCharacterFinset_iff (p := p)]
  refine ⟨inv_ne_one.2 hχ1, fun hχinvquad => hχquad ?_⟩
  calc
    χ = (χ⁻¹)⁻¹ := by simp
    _ = (quadraticCharComplex p)⁻¹ := by rw [hχinvquad]
    _ = quadraticCharComplex p := by simp [quadraticCharComplex_inv (p := p)]

/-- A non-self-dual character is, indeed, not its own inverse.
@isnad1 id=ne.2h2v.s6.70d13c0f3b5f from=translated src=- shape=f8b7994c vocab=98b8cdb6
-/
theorem ne_inv_of_mem_nonselfdualCharacterFinset (hp₂ : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ ≠ χ⁻¹ := by
  rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχ1, hχquad⟩
  intro hχself
  rcases selfInverse_character_eq_one_or_quadratic (p := p) hp₂ hχself with h | h
  · exact hχ1 h
  · exact hχquad h

/-- One representative from each non-self-dual inverse pair, chosen by the
fixed `Fin`-indexing on characters.-/
noncomputable def nonselfdualCharacterReps :
    Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterFinset (p := p)).filter
    fun χ ↦ characterIndexEquiv (p := p) χ < characterIndexEquiv (p := p) χ⁻¹

/-- Membership in the chosen representatives.
@isnad1 id=iff.0h2v.s8.f9886aa0b6cc from=translated src=- shape=0113a7ab vocab=1129d575
-/
theorem mem_nonselfdualCharacterReps_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ nonselfdualCharacterReps (p := p) ↔
      χ ∈ nonselfdualCharacterFinset (p := p) ∧
        characterIndexEquiv (p := p) χ < characterIndexEquiv (p := p) χ⁻¹ := by
  simp [nonselfdualCharacterReps]

/-- At most one of `χ`, `χ⁻¹` is a representative.
@isnad1 id=not.1h2v.s7.a15116342dfd from=translated src=- shape=291a5f4d vocab=94442266
-/
theorem inv_not_mem_nonselfdualCharacterReps {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterReps (p := p)) :
    χ⁻¹ ∉ nonselfdualCharacterReps (p := p) := by
  intro hχinv
  rcases (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχ with ⟨_, hlt⟩
  have hlt_inv :
      characterIndexEquiv (p := p) χ⁻¹ < characterIndexEquiv (p := p) χ := by
    simpa using ((mem_nonselfdualCharacterReps_iff (p := p) χ⁻¹).1 hχinv).2
  exact lt_irrefl _ (lt_trans hlt hlt_inv)

/-- …and at least one of them is.
@isnad1 id=or.2h2v.s7.f9255da0fe4b from=translated src=- shape=63b3ae2f vocab=1623206c
-/
theorem mem_reps_or_inv_mem_reps (hp₂ : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ ∈ nonselfdualCharacterReps (p := p) ∨ χ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
  have hne : χ ≠ χ⁻¹ :=
    ne_inv_of_mem_nonselfdualCharacterFinset (p := p) hp₂ hχ
  have hij :
      characterIndexEquiv (p := p) χ ≠ characterIndexEquiv (p := p) χ⁻¹ := fun hidx ↦
    hne <| (characterIndexEquiv (p := p)).injective hidx
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · left
    exact (mem_nonselfdualCharacterReps_iff (p := p) χ).2 ⟨hχ, hlt⟩
  · right
    exact (mem_nonselfdualCharacterReps_iff (p := p) χ⁻¹).2
      ⟨inv_mem_nonselfdualCharacterFinset (p := p) hχ, by simpa using hgt⟩

/-- So the non-self-dual characters are the representatives together with their
inverses.
@isnad1 id=eq.1h1v.s6.50f4750bc96b from=translated src=- shape=077ac455 vocab=ad0f3aca
-/
theorem nonselfdualCharacterFinset_eq_union_reps_image_inv (hp₂ : p ≠ 2) :
    nonselfdualCharacterFinset (p := p) =
      nonselfdualCharacterReps (p := p) ∪
        (nonselfdualCharacterReps (p := p)).image fun χ ↦ χ⁻¹ := by
  ext χ
  constructor
  · intro hχ
    rcases mem_reps_or_inv_mem_reps (p := p) hp₂ hχ with hrep | hinvrep
    · exact Finset.mem_union.mpr (Or.inl hrep)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨χ⁻¹, hinvrep, by simp⟩))
  · intro hχ
    rcases Finset.mem_union.mp hχ with hrep | himage
    · exact (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hrep |>.1
    · rcases Finset.mem_image.mp himage with ⟨ψ, hψrep, hψ⟩
      have hψnon : ψ ∈ nonselfdualCharacterFinset (p := p) :=
        (mem_nonselfdualCharacterReps_iff (p := p) ψ).1 hψrep |>.1
      simpa [← hψ] using inv_mem_nonselfdualCharacterFinset (p := p) hψnon

/-- …and that union is disjoint.
@isnad1 id=disjoint.0h1v.s6.c498fe9091af from=translated src=- shape=356fe337 vocab=0a6c08ad
-/
theorem disjoint_nonselfdualCharacterReps_image_inv :
    Disjoint (nonselfdualCharacterReps (p := p))
      ((nonselfdualCharacterReps (p := p)).image fun χ ↦ χ⁻¹) := by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, hψ⟩
  have hψinv : ψ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
    simpa [hψ] using hχrep
  exact (inv_not_mem_nonselfdualCharacterReps (p := p) hψrep) hψinv

/-- Pairing the scalars up: the product over all non-self-dual characters is the
product of the pair block determinants `-χ(-1)` over the representatives.
@isnad1 id=eq.1h1v.s7.596fb75cbc31 from=translated src=- shape=e7d4d4e2 vocab=72b62315
-/
theorem prod_nonselfdualScalars_eq_prod_reps_eval_neg_one (hp₂ : p ≠ 2) :
    Finset.prod (nonselfdualCharacterFinset (p := p))
      (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)) =
        Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ ↦ χ (-1)) := by
  let reps := nonselfdualCharacterReps (p := p)
  let f : DirichletCharacter ℂ p → ℂ :=
    fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)
  have hsplit := nonselfdualCharacterFinset_eq_union_reps_image_inv (p := p) hp₂
  have hdisj := disjoint_nonselfdualCharacterReps_image_inv (p := p)
  have hinj : Set.InjOn (fun χ : DirichletCharacter ℂ p ↦ χ⁻¹) ↑reps := by
    intro χ hχ ψ hψ hEq
    simpa using congrArg Inv.inv hEq
  calc
    Finset.prod (nonselfdualCharacterFinset (p := p)) f
        = Finset.prod reps f * Finset.prod (reps.image fun χ ↦ χ⁻¹) f := by
            rw [hsplit, Finset.prod_union hdisj]
    _ = Finset.prod reps f * Finset.prod reps (fun χ ↦ f (χ⁻¹)) := by
          rw [Finset.prod_image hinj]
    _ = Finset.prod reps (fun χ ↦ f χ * f (χ⁻¹)) := by
          rw [← Finset.prod_mul_distrib]
    _ = Finset.prod reps (fun χ ↦ χ (-1)) := by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          have hχnon : χ ∈ nonselfdualCharacterFinset (p := p) :=
            (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχ |>.1
          exact normalizedDftConstOneBasisScalar_mul_inv_eq_eval_neg_one (p := p)
            ((mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχnon).1

/-- The number of non-self-dual pairs.
@isnad1 id=eq.1h1v.s5.114984ca8fbc from=translated src=- shape=6a00d6f6 vocab=470100b5
-/
theorem card_nonselfdualCharacterReps (hp₂ : p ≠ 2) :
    (nonselfdualCharacterReps (p := p)).card = (p - 3) / 2 := by
  let reps := nonselfdualCharacterReps (p := p)
  let q : DirichletCharacter ℂ p := quadraticCharComplex p
  have hq_ne : q ≠ (1 : DirichletCharacter ℂ p) := quadraticCharComplex_ne_one (p := p) hp₂
  have hq_mem : q ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ p) :
      Finset (DirichletCharacter ℂ p)) := by
    simp [Finset.mem_erase, q, hq_ne]
  have hcard_nonself :
      (nonselfdualCharacterFinset (p := p)).card = p - 3 := by
    rw [nonselfdualCharacterFinset, Finset.card_erase_of_mem hq_mem,
      Finset.card_erase_of_mem (by simp),
      Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
      Nat.totient_prime hp.out]
    omega
  have hsplit :
      (nonselfdualCharacterFinset (p := p)).card =
        reps.card + reps.card := by
    rw [nonselfdualCharacterFinset_eq_union_reps_image_inv (p := p) hp₂,
      Finset.card_union_of_disjoint (disjoint_nonselfdualCharacterReps_image_inv (p := p)),
      Finset.card_image_of_injective _ (fun χ ψ hEq ↦ by simpa using congrArg Inv.inv hEq)]
  have hp₂le : 2 ≤ p := hp.out.two_le
  have hp₃ : 3 ≤ p := by
    omega
  have htwice : p - 3 = reps.card * 2 := by
    omega
  exact (Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) htwice).symm

/-- **The block determinant formula**: the determinant of the normalized DFT is the
trivial `δ₀/1` block determinant `-1`, times the quadratic-line scalar, times the
product of the pair block determinants.
@isnad1 id=eq.1h1v.s10.fb07d740822e from=translated src=- shape=bcf4c011 vocab=fc7e829a
-/
theorem det_normalizedDft_eq_trivialBlock_mul_quadraticScalar_mul_prod_pairBlockDeterminants
    (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ ↦ -(χ (-1)))) := by
  let reps := nonselfdualCharacterReps (p := p)
  let qScalar : ℂ :=
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p))
  have hprod :
      Finset.prod (nonselfdualCharacterFinset (p := p))
        (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)) =
          Finset.prod reps (fun χ ↦ χ (-1)) :=
    prod_nonselfdualScalars_eq_prod_reps_eval_neg_one (p := p) hp₂
  have hexp : ((p - 1) / 2 : ℕ) = 1 + reps.card := by
    have hreps : reps.card = (p - 3) / 2 := by
      simpa [reps] using card_nonselfdualCharacterReps (p := p) hp₂
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp₂
    have hreps' : reps.card = k - 1 := by
      rw [hreps, hk]
      omega
    have hleft : ((p - 1) / 2 : ℕ) = k := by
      rw [hk]
      omega
    have hright : 1 + reps.card = k := by
      rw [hreps']
      have hp₂le : 2 ≤ p := hp.out.two_le
      have hkpos : 0 < k := by
        omega
      simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hkpos
    calc
      ((p - 1) / 2 : ℕ) = k := hleft
      _ = 1 + reps.card := hright.symm
  have hnegprod :
      Finset.prod reps (fun χ ↦ -(χ (-1))) =
        (-1 : ℂ) ^ reps.card * Finset.prod reps (fun χ ↦ χ (-1)) := by
    rw [show (fun χ : DirichletCharacter ℂ p ↦ -(χ (-1))) =
        fun χ ↦ (-1 : ℂ) * χ (-1) by
          funext χ
          ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  calc
    LinearMap.det (normalizedDft p)
        = (-1 : ℂ) ^ ((p - 1) / 2) *
            (qScalar * Finset.prod reps (fun χ ↦ χ (-1))) := by
            simp [reps, qScalar, hprod,
              det_normalizedDft_eq_quadraticScalar_mul_prod_nonselfdualScalars (p := p) hp₂]
    _ = ((-1 : ℂ) * (-1 : ℂ) ^ reps.card) *
          (qScalar * Finset.prod reps (fun χ ↦ χ (-1))) := by
          rw [hexp, pow_add]
          simp
    _ = (-1 : ℂ) *
          (qScalar * ((-1 : ℂ) ^ reps.card * Finset.prod reps (fun χ ↦ χ (-1)))) := by
            ring
    _ = (-1 : ℂ) * (qScalar * Finset.prod reps (fun χ ↦ -(χ (-1)))) := by
          rw [← hnegprod]

end SignInvariant

end BernoulliRegular
