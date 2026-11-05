module

public import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
public import Tengoku.Seed.RingTheory.MvPolynomial.Basic
public import Tengoku.Seed.Data.Finsupp.Multiset
public import Tengoku.Seed.Data.Sym.Card
public import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
public import Tengoku.Seed.LinearAlgebra.Dimension.Finrank
public import Tengoku.Seed.LinearAlgebra.Quotient.Basic
public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Homogeneous polynomial spaces

The spaces and maps in this file use actual multivariate polynomials. The
monomial-basis construction and its dimension proof are adapted from
`Quartic.Homogeneous` in the local Fröberg formalization. The homogeneous
evaluation scaling proof is adapted from `OAI.Nagata.W16` in
`OAI.AlgebraicGeometry.PlaneCurves.Forms`. Both are reproduced here with their
proofs, so this module has no dependency on either manuscript's theorem.
-/

noncomputable section

namespace ChoppedPlane

open MvPolynomial Module

variable (K : Type*) [Field K] (n d : ℕ)

abbrev Poly := MvPolynomial (Fin n) K

abbrev Forms := MvPolynomial.homogeneousSubmodule (Fin n) K d

/-- Degree-`d` exponent vectors are multisets of `d` variable indices.-/
def exponentEquiv : Sym (Fin n) d ≃ {e : Fin n →₀ ℕ // e.degree = d} :=
  Sym.equivNatSum (Fin n) d

/-- The monomial basis of the genuine homogeneous polynomial subspace.-/
def formsBasis : Basis (Sym (Fin n) d) K (Forms K n d) := by
  rw [Forms, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (exponentEquiv n d).symm

private theorem basis_transport_val {M ι : Type*} [AddCommGroup M] [Module K M]
    {P Q : Submodule K M} (h : P = Q) (b : Basis ι K Q) (i : ι) :
    (Eq.mpr (congrArg (fun W : Submodule K M => Basis ι K W) h) b i).val = (b i).val := by
  subst P
  rfl

/-- The form basis consists of coefficient-one monomials, with exponent index
independent of the coefficient field.
@isnad1 id=eq.0h4v.s11.ac7a8926b81f from=translated src=- shape=99c5f660 vocab=9668818e
-/
theorem formsBasis_val_monomial (i : Sym (Fin n) d) :
    (formsBasis K n d i).val = monomial (exponentEquiv n d i).val 1 := by
  let b := (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (exponentEquiv n d).symm
  have h : Forms K n d = MvPolynomial.restrictSupport K {e : Fin n →₀ ℕ | e.degree = d} :=
    homogeneousSubmodule_eq_finsupp_supported (Fin n) K d
  have hval : (formsBasis K n d i).val = (b i).val :=
    basis_transport_val K h b i
  rw [hval]
  simp only [b, Basis.reindex_apply, Equiv.symm_symm]
  change ((AddMonoidAlgebra.supportedEquivFinsupp {e : Fin n →₀ ℕ | e.degree = d}).symm
    (Finsupp.single (exponentEquiv n d i) 1)).val = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp]
  rfl

/-- Coefficient maps preserve the chosen homogeneous monomial basis.
@isnad1 id=eq.0h6v.s11.b3cc13dddf03 from=translated src=- shape=7f1b31df vocab=b2f31bf6
-/
theorem formsBasis_map {L : Type*} [Field L] (k : K →+* L) (i : Sym (Fin n) d) :
    MvPolynomial.map k (formsBasis K n d i).val = (formsBasis L n d i).val := by
  rw [formsBasis_val_monomial, formsBasis_val_monomial]
  simp

/--
@isnad1 id=finite.0h3v.s8.425fa85e0b99 from=translated src=- shape=ef6e89bc vocab=100e649f
-/
instance formsFinite : Module.Finite K (Forms K n d) :=
  Module.Finite.of_basis (formsBasis K n d)

/-- Stars and bars as a dimension theorem for homogeneous forms.
@isnad1 id=eq.0h3v.s8.a9ac23bca2fc from=translated src=- shape=2fd06275 vocab=2f87eb79
-/
theorem finrank_forms : finrank K (Forms K n d) = (n + d - 1).choose d := by
  rw [Module.finrank_eq_card_basis (formsBasis K n d), Sym.card_sym_eq_choose]
  simp

/-- The dimension of ternary degree-`d` forms.
@isnad1 id=eq.0h2v.s9.58f19a7b47d7 from=translated src=- shape=9ddae480 vocab=23745a2b
-/
theorem finrank_plane_forms : finrank K (Forms K 3 d) = (d + 2).choose 2 := by
  rw [finrank_forms]
  have h : 3 + d - 1 = d + 2 := by omega
  rw [h, ← Nat.choose_symm (by omega : d ≤ d + 2)]
  simp

variable {K n d} {e : ℕ}

/-- Multiplication by a fixed form, with the correct homogeneous target.-/
def mulForm (f : Forms K n d) : Forms K n e →ₗ[K] Forms K n (d + e) where
  toFun a := ⟨f.val * a.val, f.property.mul a.property⟩
  map_add' a b := Subtype.ext (mul_add f.val a.val b.val)
  map_smul' k a := Subtype.ext (mul_smul_comm k f.val a.val)

/--
@isnad1 id=eq.0h6v.s11.f228afa052ad from=translated src=- shape=ef4c373a vocab=e7e9b33f
-/
@[simp] theorem mulForm_val (f : Forms K n d) (a : Forms K n e) :
    (mulForm f a).val = f.val * a.val := rfl

/-- A nonzero form multiplies injectively in a polynomial ring over a field.
@isnad1 id=injectiv.1h5v.s11.d0b4ec59cf37 from=translated src=- shape=60a141b3 vocab=805a1a06
-/
theorem mulForm_injective (f : Forms K n d) (hf : f.val ≠ 0) :
    Function.Injective (mulForm (e := e) f) := by
  intro a b hab
  apply Subtype.ext
  exact mul_left_cancel₀ hf (congrArg Subtype.val hab)

/-- All products of degree-`d` and degree-`e` forms span degree `d + e`.
@isnad1 id=eq.0h4v.s8.bf1399c83e30 from=translated src=- shape=6a69d5a3 vocab=bc6fc9a0
-/
theorem forms_mul_forms : Forms K n d * Forms K n e = Forms K n (d + e) := by
  calc
    Forms K n d * Forms K n e = Forms K n 1 ^ d * Forms K n 1 ^ e := by
      simp only [Forms, MvPolynomial.homogeneousSubmodule_one_pow]
    _ = Forms K n 1 ^ (d + e) := (pow_add _ d e).symm
    _ = Forms K n (d + e) := MvPolynomial.homogeneousSubmodule_one_pow K (d + e)

/-- Evaluation on a fixed homogeneous representative is a linear functional.-/
def evaluationLinear (K : Type*) [Field K] (n d : ℕ) (x : Fin n → K) :
    Forms K n d →ₗ[K] K where
  toFun f := MvPolynomial.eval x f.val
  map_add' f g := map_add _ _ _
  map_smul' c f := by simp

/--
@isnad1 id=eq.0h5v.s10.622dee9b93dc from=translated src=- shape=dc5572e2 vocab=218a42a7
-/
@[simp] theorem evaluationLinear_apply (x : Fin n → K) (f : Forms K n d) :
    evaluationLinear K n d x f = MvPolynomial.eval x f.val := rfl

section Scaling

/-- Homogeneous scaling after any coefficient-ring map.
@isnad1 id=eq.1h8v.s6.c8f44f2e8529 from=translated src=- shape=9c3fd8ae vocab=425e9cb1
-/
theorem homogeneous_eval₂_scale {σ R T : Type*} [CommSemiring R] [CommSemiring T]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (k : R →+* T) (x : σ → T) (a : T) :
    MvPolynomial.eval₂ k (fun i => a * x i) f =
      a ^ d * MvPolynomial.eval₂ k x f := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hf.degree_eq_sum_deg_support hu]
  ac_rfl

/-- Homogeneous evaluation commutes with scalar rescaling.
@isnad1 id=eq.1h6v.s7.bab21160c3f6 from=translated src=- shape=8fb0b415 vocab=f992872c
-/
theorem homogeneous_eval_scale {σ R : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (x : σ → R) (a : R) :
    MvPolynomial.eval (fun i => a * x i) f = a ^ d * MvPolynomial.eval x f := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hf.degree_eq_sum_deg_support hu]
  ac_rfl

/-- Vanishing of a homogeneous form is invariant under nonzero rescaling.
@isnad1 id=iff.2h6v.s8.c931efc048f8 from=translated src=- shape=bf8265ae vocab=f16842d6
-/
theorem homogeneous_eval_scale_eq_zero_iff {σ R : Type*} [CommRing R]
    [IsDomain R] {f : MvPolynomial σ R} {d : ℕ}
    (hf : f.IsHomogeneous d) (x : σ → R) {a : R} (ha : a ≠ 0) :
    MvPolynomial.eval (fun i => a * x i) f = 0 ↔ MvPolynomial.eval x f = 0 := by
  rw [homogeneous_eval_scale hf x a]
  simp only [mul_eq_zero, pow_ne_zero d ha, false_or]

end Scaling

end ChoppedPlane
