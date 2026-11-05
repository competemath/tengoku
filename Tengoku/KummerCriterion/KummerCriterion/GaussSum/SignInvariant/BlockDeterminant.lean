module

public import Tengoku.Seed.LinearAlgebra.Matrix.Permutation
public import Tengoku.KummerCriterion.KummerCriterion.GaussSum.Basic
public import Tengoku.Seed.NumberTheory.DirichletCharacter.Orthogonality
import Tengoku.KummerCriterion.KummerCriterion.GaussSum.SignInvariant.Trace
public import Tengoku.KummerCriterion.KummerCriterion.GaussSum.SignInvariant.Operator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Determinant-ready block decomposition for quadratic Gauss sums

This file packages the ambient `δ₀ +` character basis used to reorganize the
normalized finite Fourier transform into the trivial block, non-self-dual
character-pair blocks, and the surviving quadratic line.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

/-- The delta function supported at `0`.-/
def deltaZeroFunction : ZMod p → ℂ :=
  Pi.basisFun ℂ (ZMod p) (0 : ZMod p)

/-- Restrict a function on `ZMod p` to the unit group.-/
def restrictUnitsLinear : (ZMod p → ℂ) →ₗ[ℂ] ((ZMod p)ˣ → ℂ) where
  toFun Φ u := Φ u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- View a Dirichlet character as a monoid homomorphism on the unit group with
values in `ℂ`.-/
def dirichletCharacterUnitMonoidHom (χ : DirichletCharacter ℂ p) : (ZMod p)ˣ →* ℂ :=
  (Units.coeHom ℂ).comp χ.toUnitHom

/--
@isnad1 id=injectiv.0h1v.s6.6d25aa52eb6e from=translated src=- shape=0c8b67aa vocab=8cd6d3f4
-/
theorem dirichletCharacterUnitMonoidHom_injective :
    Function.Injective (dirichletCharacterUnitMonoidHom (p := p)) := fun χ ψ hχψ =>
  (DirichletCharacter.toUnitHom_inj χ ψ).mp
    (MonoidHom.ext fun u => Units.ext (DFunLike.congr_fun hχψ u))

/-- Dirichlet characters are linearly independent on the unit group.
@isnad1 id=linearin.0h1v.s8.2259abe878c9 from=translated src=- shape=74b93aac vocab=c787f0b8
-/
theorem linearIndependent_dirichletCharactersOnUnits :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ p =>
      (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ)) :=
  (linearIndependent_monoidHom ((ZMod p)ˣ) ℂ).comp
      (dirichletCharacterUnitMonoidHom (p := p))
      (dirichletCharacterUnitMonoidHom_injective (p := p))

/-- Evaluation at `0`.-/
def evalAtZeroLinear : (ZMod p → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ := Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h2v.s6.d6b7adc3d3ad from=translated src=- shape=e8789427 vocab=64907573
-/
@[simp] theorem dirichletCharacter_apply_zero (χ : DirichletCharacter ℂ p) :
    χ (0 : ZMod p) = 0 :=
  MulChar.map_zero χ

/--
@isnad1 id=eq.0h1v.s7.762f57c86a08 from=translated src=- shape=823fb799 vocab=8c9998d6
-/
theorem normalizedDft_deltaZero :
    normalizedDft p (deltaZeroFunction (p := p)) =
      (Real.sqrt p : ℂ)⁻¹ • (fun _ : ZMod p => (1 : ℂ)) := by
  ext x
  rw [normalizedDft_apply, deltaZeroFunction, dft_deltaZero_eq_constOne]
  simp [smul_eq_mul]

/--
@isnad1 id=eq.0h1v.s7.eb227bbc2580 from=translated src=- shape=44cdcb36 vocab=13ba4b2c
-/
theorem normalizedDft_constOne :
    normalizedDft p (fun _ : ZMod p => (1 : ℂ)) =
      (((Real.sqrt p : ℂ)⁻¹) * p) • deltaZeroFunction (p := p) := by
  ext x
  rw [normalizedDft_apply, congrFun (dft_constOne_eq_prime_smul_deltaZero (p := p)) x]
  simp [deltaZeroFunction, smul_eq_mul, mul_assoc]

end SignInvariant

end KummerCriterion

/-!
# Determinant bookkeeping for the block decomposition

This file reorganizes the `δ₀ +` character basis so that the normalized DFT is
monomial outside the surviving quadratic line. This packages the determinant
contribution of the trivial block and prepares the remaining non-self-dual
character-pair bookkeeping.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

local instance : DecidableEq (DirichletCharacter ℂ p) := Classical.decEq _
local instance : DecidableEq (Option (DirichletCharacter ℂ p)) := Classical.decEq _

/-- Replace the trivial Dirichlet character by the constant-`1` function, but
leave every other character unchanged.-/
def constOneDirichletCharacterFamily (χ : DirichletCharacter ℂ p) : ZMod p → ℂ := by
  classical
  exact if hχ : χ = 1 then fun _ : ZMod p => (1 : ℂ) else (χ : ZMod p → ℂ)

omit hp in
/--
@isnad1 id=eq.0h1v.s5.95f2f6c602d0 from=translated src=- shape=5d438aaa vocab=289693b6
-/
@[simp] theorem constOneDirichletCharacterFamily_one :
    constOneDirichletCharacterFamily (p := p) (1 : DirichletCharacter ℂ p) =
      (fun _ : ZMod p => (1 : ℂ)) := by
  classical
  rw [constOneDirichletCharacterFamily]
  simp

omit hp in
/--
@isnad1 id=eq.1h2v.s6.0f8c2ab06c83 from=translated src=- shape=230e590d vocab=babf5bf4
-/
theorem constOneDirichletCharacterFamily_eq_character {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) :
    constOneDirichletCharacterFamily (p := p) χ = (χ : ZMod p → ℂ) := by
  classical
  rw [constOneDirichletCharacterFamily]
  simp [hχ]

/--
@isnad1 id=eq.0h1v.s8.69d94837ae34 from=translated src=- shape=bc6d945d vocab=1e5aaade
-/
@[simp] theorem restrictUnits_deltaZero :
    restrictUnitsLinear (p := p) (deltaZeroFunction (p := p)) = 0 := by
  ext u
  have hu : ((u : (ZMod p)) ≠ 0) := Units.ne_zero u
  simp [restrictUnitsLinear, deltaZeroFunction, hu]

/--
@isnad1 id=eq.0h2v.s9.46bdc055567f from=translated src=- shape=e2282992 vocab=6afea7f9
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
@isnad1 id=linearin.0h1v.s5.0c99250daff1 from=translated src=- shape=bb94f6cd vocab=57bce4ff
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

/--
@isnad1 id=not.0h1v.s7.ef6421db5bbc from=translated src=- shape=b2074681 vocab=1210a046
-/
theorem deltaZero_not_mem_span_constOneDirichletCharacterFamily :
    deltaZeroFunction (p := p) ∉
      Submodule.span ℂ
        (Set.range fun χ : DirichletCharacter ℂ p =>
          constOneDirichletCharacterFamily (p := p) χ) := by
  intro hdelta
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (R := ℂ)
      (v := fun χ : DirichletCharacter ℂ p =>
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
  fun o => Option.casesOn' o (deltaZeroFunction (p := p))
    (constOneDirichletCharacterFamily (p := p))

/--
@isnad1 id=linearin.0h1v.s5.da53a1f4d45f from=translated src=- shape=ed436806 vocab=37261e55
-/
theorem linearIndependent_deltaZeroConstOneDirichletCharacterFamily :
    LinearIndependent ℂ (deltaZeroConstOneDirichletCharacterFamily (p := p)) := by
  simpa [deltaZeroConstOneDirichletCharacterFamily] using!
    (linearIndependent_constOneDirichletCharacterFamily (p := p)).option
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
@isnad1 id=eq.0h1v.s7.e9146803bed2 from=translated src=- shape=b212168d vocab=98233a60
-/
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_none :
    deltaZeroConstOneDirichletCharacterBasis (p := p) none = deltaZeroFunction (p := p) := by
  rw [deltaZeroConstOneDirichletCharacterBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/--
@isnad1 id=eq.0h2v.s7.8d6a1dd840b8 from=translated src=- shape=eb9b77c8 vocab=1143ea02
-/
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some
    (χ : DirichletCharacter ℂ p) :
    deltaZeroConstOneDirichletCharacterBasis (p := p) (some χ) =
      constOneDirichletCharacterFamily (p := p) χ := by
  rw [deltaZeroConstOneDirichletCharacterBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/--
@isnad1 id=eq.0h1v.s7.3e9437fb6bad from=translated src=- shape=c0272955 vocab=8ab7a870
-/
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some_one :
    deltaZeroConstOneDirichletCharacterBasis (p := p)
        (some (1 : DirichletCharacter ℂ p)) =
      (fun _ : ZMod p => (1 : ℂ)) := by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some, constOneDirichletCharacterFamily_one]

/--
@isnad1 id=eq.1h2v.s7.b3cb1696244d from=translated src=- shape=183a3e01 vocab=8ab7a870
-/
theorem deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    deltaZeroConstOneDirichletCharacterBasis (p := p) (some χ) = (χ : ZMod p → ℂ) := by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some,
    constOneDirichletCharacterFamily_eq_character, hχ]

/-- The underlying involution on the adapted basis indices.-/
def normalizedDftConstOneBasisPermFun :
    Option (DirichletCharacter ℂ p) → Option (DirichletCharacter ℂ p) := by
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
        · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := by
            intro hχinv
            apply hχ
            calc
              χ = (χ⁻¹)⁻¹ := by simp
              _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [hχinv]
              _ = 1 := by simp
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
        · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := by
            intro hχinv
            apply hχ
            calc
              χ = (χ⁻¹)⁻¹ := by simp
              _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [hχinv]
              _ = 1 := by simp
          simp [normalizedDftConstOneBasisPermFun, hχ, hχinv]

/-- The scalar attached to each basis vector under the normalized DFT.-/
def normalizedDftConstOneBasisScalar (i : Option (DirichletCharacter ℂ p)) : ℂ := by
  classical
  exact match i with
  | none => (Real.sqrt p : ℂ)⁻¹
  | some χ =>
      if hχ : χ = 1 then ((Real.sqrt p : ℂ)⁻¹) * p
      else ((Real.sqrt p : ℂ)⁻¹) *
        (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p)))

/--
@isnad1 id=eq.0h2v.s9.016550c9a775 from=translated src=- shape=772dd6bc vocab=407163c8
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
      · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := by
          intro hχinv
          apply hχ
          calc
            χ = (χ⁻¹)⁻¹ := by simp
            _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [hχinv]
            _ = 1 := by simp
        rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one (p := p) hχ]
        ext x
        rw [normalizedDft_apply]
        rw [congrFun (dft_eq_scalar_smul_inv_character (p := p) (χ := χ) hχ) x]
        simp [normalizedDftConstOneBasisScalar, normalizedDftConstOneBasisPerm,
          normalizedDftConstOneBasisPermFun, hχ, hχinv,
          deltaZeroConstOneDirichletCharacterBasis_apply_some,
          constOneDirichletCharacterFamily_eq_character, smul_eq_mul,
          mul_left_comm, mul_comm]

/--
@isnad1 id=eq.0h1v.s10.be5a12241c35 from=translated src=- shape=ce13cb6e vocab=a89dee3c
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
      ite_false] using hsingle

/--
@isnad1 id=eq.0h1v.s10.cb24325e3dae from=translated src=- shape=b020e4ac vocab=e0b5d20d
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
/--
@isnad1 id=eq.0h1v.s7.488e21d1fc34 from=translated src=- shape=76c19229 vocab=9d4000f3
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
      · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := by
          intro hχinv
          apply hχ
          calc
            χ = (χ⁻¹)⁻¹ := by simp
            _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [hχinv]
            _ = 1 := by simp
        simp [pow_two, normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun, hχ,
          hχinv]

/--
@isnad1 id=iff.1h2v.s7.bd4569eb79fa from=translated src=- shape=d45ec9c9 vocab=39717890
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

/--
@isnad1 id=eq.1h1v.s8.0e5ff6362954 from=translated src=- shape=9e89f76e vocab=231753c7
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

/--
@isnad1 id=eq.1h1v.s8.4b6b8fd78cfa from=translated src=- shape=6df0ae71 vocab=1298bc40
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

/--
@isnad1 id=eq.1h1v.s10.ab58875e4263 from=translated src=- shape=0ecbc6c9 vocab=a4092348
-/
theorem det_normalizedDft_eq_signContribution_mul_prod_basisScalars (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) ^ ((p - 1) / 2) * ∏ i, normalizedDftConstOneBasisScalar (p := p) i := by
  rw [det_normalizedDft_eq_sign_mul_prod_basisScalars (p := p),
    sign_normalizedDftConstOneBasisPerm (p := p) hp₂]

/--
@isnad1 id=eq.1h2v.s7.71889aeccc58 from=translated src=- shape=b5bc9cf3 vocab=0521a427
-/
theorem normalizedDftConstOneBasisScalar_mul_inv_eq_eval_neg_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    normalizedDftConstOneBasisScalar (p := p) (some χ) *
      normalizedDftConstOneBasisScalar (p := p) (some χ⁻¹) = χ (-1) := by
  classical
  have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := by
    intro hχinv
    apply hχ
    calc
      χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [hχinv]
      _ = 1 := by simp
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

/--
@isnad1 id=eq.1h1v.s7.313098a15674 from=translated src=- shape=9e9e2fde vocab=bf871a3e
-/
theorem prod_basisScalars_eq_quadraticScalar_mul_prod_nonselfdualScalars (hp₂ : p ≠ 2) :
    ∏ i, normalizedDftConstOneBasisScalar (p := p) i =
      normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
        Finset.prod (nonselfdualCharacterFinset (p := p))
          (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)) := by
  rw [Fintype.prod_option]
  let q : DirichletCharacter ℂ p := quadraticCharComplex p
  have hq_ne : q ≠ (1 : DirichletCharacter ℂ p) := quadraticCharComplex_ne_one (p := p) hp₂
  have htriv :
      normalizedDftConstOneBasisScalar (p := p) none *
        normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) = 1 := by
    have hp_nonneg : (0 : ℝ) ≤ p := by
      exact_mod_cast Nat.zero_le p
    have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
    have hsq : ((Real.sqrt p : ℂ) ^ 2) = (p : ℂ) := by
      exact_mod_cast (Real.sq_sqrt hp_nonneg)
    simp [normalizedDftConstOneBasisScalar]
    field_simp [hsqrt_ne]
    simpa [pow_two, mul_assoc] using hsq.symm
  have hprod_chars :
      ∏ χ : DirichletCharacter ℂ p, normalizedDftConstOneBasisScalar (p := p) (some χ) =
        normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) *
          (normalizedDftConstOneBasisScalar (p := p) (some q) *
            Finset.prod (nonselfdualCharacterFinset (p := p))
              (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
    let f : DirichletCharacter ℂ p → ℂ :=
      fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)
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
            (normalizedDftConstOneBasisScalar (p := p) (some q) *
              Finset.prod (nonselfdualCharacterFinset (p := p))
                (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
          simp [f]
  have hstep1 :
      normalizedDftConstOneBasisScalar (p := p) none *
          ∏ i, normalizedDftConstOneBasisScalar (p := p) (some i) =
        normalizedDftConstOneBasisScalar (p := p) none *
          (normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) *
            (normalizedDftConstOneBasisScalar (p := p) (some q) *
              Finset.prod (nonselfdualCharacterFinset (p := p))
                (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)))) :=
    congrArg (fun z => normalizedDftConstOneBasisScalar (p := p) none * z) hprod_chars
  calc
    normalizedDftConstOneBasisScalar (p := p) none *
        ∏ i, normalizedDftConstOneBasisScalar (p := p) (some i)
        = normalizedDftConstOneBasisScalar (p := p) none *
            (normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) *
              (normalizedDftConstOneBasisScalar (p := p) (some q) *
                Finset.prod (nonselfdualCharacterFinset (p := p))
                  (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)))) := hstep1
    _ = (normalizedDftConstOneBasisScalar (p := p) none *
          normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p))) *
            (normalizedDftConstOneBasisScalar (p := p) (some q) *
              Finset.prod (nonselfdualCharacterFinset (p := p))
                (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
            ring_nf
    _ = normalizedDftConstOneBasisScalar (p := p) (some q) *
          Finset.prod (nonselfdualCharacterFinset (p := p))
            (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)) := by
            rw [htriv]
            simp
    _ = normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterFinset (p := p))
            (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)) := by
            simp [q]

/--
@isnad1 id=eq.1h1v.s10.492e1830fce2 from=translated src=- shape=ee0d492c vocab=1365dc0d
-/
theorem det_normalizedDft_eq_quadraticScalar_mul_prod_nonselfdualScalars (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) ^ ((p - 1) / 2) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterFinset (p := p))
            (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
  rw [det_normalizedDft_eq_signContribution_mul_prod_basisScalars (p := p) hp₂,
    prod_basisScalars_eq_quadraticScalar_mul_prod_nonselfdualScalars (p := p) hp₂]

/-- A chosen indexing of Dirichlet characters by `Fin`, used to pick one
representative from each inverse-pair orbit.-/
noncomputable def characterIndexEquiv :
    DirichletCharacter ℂ p ≃ Fin (Fintype.card (DirichletCharacter ℂ p)) :=
  Fintype.equivFin (DirichletCharacter ℂ p)

/--
@isnad1 id=iff.0h2v.s7.f3680cb6307a from=translated src=- shape=8a372bb2 vocab=3a81334f
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

/--
@isnad1 id=mem.1h2v.s7.f8a4af233a3b from=translated src=- shape=d814bd15 vocab=f26528d6
-/
theorem inv_mem_nonselfdualCharacterFinset {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ⁻¹ ∈ nonselfdualCharacterFinset (p := p) := by
  rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχ1, hχquad⟩
  rw [mem_nonselfdualCharacterFinset_iff (p := p)]
  constructor
  · intro hχinv
    apply hχ1
    calc
      χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [hχinv]
      _ = 1 := by simp
  · intro hχinvquad
    apply hχquad
    calc
      χ = (χ⁻¹)⁻¹ := by simp
      _ = (quadraticCharComplex p)⁻¹ := by rw [hχinvquad]
      _ = quadraticCharComplex p := by simp [quadraticCharComplex_inv (p := p)]

/--
@isnad1 id=ne.2h2v.s6.26396b4cf700 from=translated src=- shape=f8b7994c vocab=f26528d6
-/
theorem ne_inv_of_mem_nonselfdualCharacterFinset {hp₂ : p ≠ 2} {χ : DirichletCharacter ℂ p}
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
    fun χ => characterIndexEquiv (p := p) χ < characterIndexEquiv (p := p) χ⁻¹

/--
@isnad1 id=iff.0h2v.s8.23e9f0d0f651 from=translated src=- shape=0113a7ab vocab=153d677e
-/
theorem mem_nonselfdualCharacterReps_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ nonselfdualCharacterReps (p := p) ↔
      χ ∈ nonselfdualCharacterFinset (p := p) ∧
        characterIndexEquiv (p := p) χ < characterIndexEquiv (p := p) χ⁻¹ := by
  simp [nonselfdualCharacterReps]

/--
@isnad1 id=not.1h2v.s7.65655d866887 from=translated src=- shape=291a5f4d vocab=7cc6d393
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

/--
@isnad1 id=or.2h2v.s7.50ac363c3a76 from=translated src=- shape=63b3ae2f vocab=f5cc66b7
-/
theorem mem_reps_or_inv_mem_reps {hp₂ : p ≠ 2} {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ ∈ nonselfdualCharacterReps (p := p) ∨ χ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
  have hne : χ ≠ χ⁻¹ :=
    ne_inv_of_mem_nonselfdualCharacterFinset (p := p) (hp₂ := hp₂) hχ
  have hij :
      characterIndexEquiv (p := p) χ ≠ characterIndexEquiv (p := p) χ⁻¹ := fun hidx =>
    hne <| (characterIndexEquiv (p := p)).injective hidx
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · left
    exact (mem_nonselfdualCharacterReps_iff (p := p) χ).2 ⟨hχ, hlt⟩
  · right
    exact (mem_nonselfdualCharacterReps_iff (p := p) χ⁻¹).2
      ⟨inv_mem_nonselfdualCharacterFinset (p := p) hχ, by simpa using hgt⟩

/--
@isnad1 id=eq.1h1v.s6.c1f5ce032316 from=translated src=- shape=077ac455 vocab=785ed191
-/
theorem nonselfdualCharacterFinset_eq_union_reps_image_inv (hp₂ : p ≠ 2) :
    nonselfdualCharacterFinset (p := p) =
      nonselfdualCharacterReps (p := p) ∪
        (nonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹ := by
  ext χ
  constructor
  · intro hχ
    rcases mem_reps_or_inv_mem_reps (p := p) (hp₂ := hp₂) hχ with hrep | hinvrep
    · exact Finset.mem_union.mpr (Or.inl hrep)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨χ⁻¹, hinvrep, by simp⟩))
  · intro hχ
    rcases Finset.mem_union.mp hχ with hrep | himage
    · exact (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hrep |>.1
    · rcases Finset.mem_image.mp himage with ⟨ψ, hψrep, hψ⟩
      have hψnon : ψ ∈ nonselfdualCharacterFinset (p := p) :=
        (mem_nonselfdualCharacterReps_iff (p := p) ψ).1 hψrep |>.1
      simpa [← hψ] using inv_mem_nonselfdualCharacterFinset (p := p) hψnon

/--
@isnad1 id=disjoint.0h1v.s6.4802571a902a from=translated src=- shape=356fe337 vocab=f4717406
-/
theorem disjoint_nonselfdualCharacterReps_image_inv :
    Disjoint (nonselfdualCharacterReps (p := p))
      ((nonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹) := by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, hψ⟩
  have hψinv : ψ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
    simpa [hψ] using hχrep
  exact (inv_not_mem_nonselfdualCharacterReps (p := p) hψrep) hψinv

/--
@isnad1 id=eq.1h1v.s7.f32883fca60c from=translated src=- shape=e7d4d4e2 vocab=3ba577d4
-/
theorem prod_nonselfdualScalars_eq_prod_reps_eval_neg_one (hp₂ : p ≠ 2) :
    Finset.prod (nonselfdualCharacterFinset (p := p))
      (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)) =
        Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => χ (-1)) := by
  let reps := nonselfdualCharacterReps (p := p)
  let f : DirichletCharacter ℂ p → ℂ :=
    fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)
  have hsplit := nonselfdualCharacterFinset_eq_union_reps_image_inv (p := p) hp₂
  have hdisj := disjoint_nonselfdualCharacterReps_image_inv (p := p)
  have hinj : Set.InjOn (fun χ : DirichletCharacter ℂ p => χ⁻¹) ↑reps := by
    intro χ hχ ψ hψ hEq
    simpa using congrArg Inv.inv hEq
  calc
    Finset.prod (nonselfdualCharacterFinset (p := p)) f
        = Finset.prod reps f * Finset.prod (reps.image fun χ => χ⁻¹) f := by
            rw [hsplit, Finset.prod_union hdisj]
    _ = Finset.prod reps f * Finset.prod reps (fun χ => f (χ⁻¹)) := by
          rw [Finset.prod_image hinj]
    _ = Finset.prod reps (fun χ => f χ * f (χ⁻¹)) := by
          rw [← Finset.prod_mul_distrib]
    _ = Finset.prod reps (fun χ => χ (-1)) := by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          have hχnon : χ ∈ nonselfdualCharacterFinset (p := p) :=
            (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχ |>.1
          exact normalizedDftConstOneBasisScalar_mul_inv_eq_eval_neg_one (p := p)
            ((mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχnon).1

/--
@isnad1 id=eq.1h1v.s5.0041516c78a6 from=translated src=- shape=6a00d6f6 vocab=c2e4aadb
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
      Finset.card_image_of_injective _ (fun χ ψ hEq => by simpa using congrArg Inv.inv hEq)]
  have hp₂le : 2 ≤ p := hp.out.two_le
  have hp₃ : 3 ≤ p := by
    omega
  have htwice : p - 3 = reps.card * 2 := by
    omega
  exact (Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) htwice).symm

/--
@isnad1 id=eq.1h1v.s10.1664056d5a85 from=translated src=- shape=bcf4c011 vocab=899f15ab
-/
theorem det_normalizedDft_eq_trivialBlock_mul_quadraticScalar_mul_prod_pairBlockDeterminants
    (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1)))) := by
  let reps := nonselfdualCharacterReps (p := p)
  let qScalar : ℂ :=
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p))
  have hprod :
      Finset.prod (nonselfdualCharacterFinset (p := p))
        (fun χ => normalizedDftConstOneBasisScalar (p := p) (some χ)) =
          Finset.prod reps (fun χ => χ (-1)) :=
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
      Finset.prod reps (fun χ => -(χ (-1))) =
        (-1 : ℂ) ^ reps.card * Finset.prod reps (fun χ => χ (-1)) := by
    rw [show (fun χ : DirichletCharacter ℂ p => -(χ (-1))) =
        fun χ => (-1 : ℂ) * χ (-1) by
          funext χ
          ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  calc
    LinearMap.det (normalizedDft p)
        = (-1 : ℂ) ^ ((p - 1) / 2) *
            (qScalar * Finset.prod reps (fun χ => χ (-1))) := by
            simp [reps, qScalar, hprod,
              det_normalizedDft_eq_quadraticScalar_mul_prod_nonselfdualScalars (p := p) hp₂]
    _ = ((-1 : ℂ) * (-1 : ℂ) ^ reps.card) *
          (qScalar * Finset.prod reps (fun χ => χ (-1))) := by
          rw [hexp, pow_add]
          simp
    _ = (-1 : ℂ) *
          (qScalar * ((-1 : ℂ) ^ reps.card * Finset.prod reps (fun χ => χ (-1)))) := by
            ring
    _ = (-1 : ℂ) * (qScalar * Finset.prod reps (fun χ => -(χ (-1)))) := by
          rw [← hnegprod]

end SignInvariant

end KummerCriterion
