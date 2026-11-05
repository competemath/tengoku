import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.RingTheory.WeightedJetValuation
import Tengoku.Seed.Algebra.Polynomial.Eval.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordinary-degree scaling of weighted jet transitions

This file isolates the local algebra behind the first deformation.
The input is an actual pair of mutually inverse weighted polynomial substitutions.
The construction below only rescales the ordinary polynomial degree of each monomial;
it does not construct a chart atlas, a relative Proj, or a global family.

For a polynomial `p` over any commutative semiring, `polynomialScale p` has coefficients
in the genuine polynomial ring `R[λ]`: a monomial of positive ordinary degree `r` is
multiplied by `λ^(r-1)`. Its specialization at zero is exactly the degree-one part when
the constant term is absent. Positive weighted homogeneity supplies this absence.
The operation applies independently to any pair of actual polynomial substitutions;
an adapter consumes the shared field-valued `WeightedPolynomialEquiv` without replacing it.

The source is the transition formula (2.7) of the paper (§2) and the first
deformation in the proof of Proposition 2.4. All definitions in this file are local
polynomial algebra. Geometric gluing, inverse and cocycle identities after scaling, flatness, and
relative Proj are separate constructions.
-/

noncomputable section

open scoped Classical BigOperators

namespace MiyaokaMori.JetTransition

open MiyaokaMori.WeightedJets

variable {ι R : Type*} [CommSemiring R]

/-- The ordinary degree of a monomial exponent.-/
abbrev ordinaryDegree (d : ι →₀ ℕ) : ℕ := d.degree

/-- The ordinary-degree scaling factor used in the deformation parameter.-/
def ordinaryScaleFactor (lam : R) (d : ι →₀ ℕ) : R :=
  lam ^ (ordinaryDegree d - 1)

/-- Scale every monomial by `λ^(ordinary degree - 1)`.-/
def ordinaryScale (lam : R) (p : MvPolynomial ι R) : MvPolynomial ι R :=
  ∑ d ∈ p.support, MvPolynomial.monomial d
    (ordinaryScaleFactor lam d * p.coeff d)

/-- The degree-one part of a polynomial, written using its actual finite support.-/
def linearPart (p : MvPolynomial ι R) : MvPolynomial ι R :=
  ∑ d ∈ p.support.filter (fun d ↦ ordinaryDegree d = 1),
    MvPolynomial.monomial d (p.coeff d)

/-- The ordinary-degree scaling family with a genuine polynomial parameter.-/
def polynomialScale (p : MvPolynomial ι R) : MvPolynomial ι (Polynomial R) :=
  ∑ d ∈ p.support, MvPolynomial.monomial d
    (Polynomial.X ^ (ordinaryDegree d - 1) * Polynomial.C (p.coeff d))

/-- Specialize the parameter while preserving all jet-coordinate indeterminates.-/
def specializeParameter (lam : R) :
    MvPolynomial ι (Polynomial R) →+* MvPolynomial ι R :=
  MvPolynomial.map (Polynomial.evalRingHom lam)

/-- The polynomial-parameter family specializes to the explicit ordinary scaling.
@isnad1 id=eq.0h4v.s7.b18d350e7eb1 from=translated src=- shape=e3ba8354 vocab=3d387457
-/
@[simp]
theorem specializeParameter_polynomialScale (lam : R) (p : MvPolynomial ι R) :
    specializeParameter lam (polynomialScale p) = ordinaryScale lam p := by
  classical
  simp [specializeParameter, polynomialScale, ordinaryScale, ordinaryScaleFactor,
    MvPolynomial.map_monomial, mul_comm]

/--
@isnad1 id=eq.0h3v.s5.6773731cb994 from=translated src=- shape=4f90632b vocab=e9ff2b40
-/
@[simp]
theorem ordinaryScaleFactor_one (d : ι →₀ ℕ) : ordinaryScaleFactor (1 : R) d = 1 := by
  simp [ordinaryScaleFactor]

/--
@isnad1 id=eq.1h3v.s5.3a625626eeb3 from=translated src=- shape=42401083 vocab=f57131e2
-/
@[simp]
theorem ordinaryScaleFactor_zero_of_two_le (d : ι →₀ ℕ) (hd : 2 ≤ ordinaryDegree d) :
    ordinaryScaleFactor (0 : R) d = 0 := by
  rw [ordinaryScaleFactor]
  exact zero_pow (by omega)

/-- Scaling at one is the original polynomial, with no change to its coefficients.
@isnad1 id=eq.0h3v.s5.1add754cb85a from=translated src=- shape=b241e498 vocab=526ef712
-/
theorem ordinaryScale_one (p : MvPolynomial ι R) : ordinaryScale (1 : R) p = p := by
  classical
  simp only [ordinaryScale, ordinaryScaleFactor_one, one_mul]
  exact MvPolynomial.support_sum_monomial_coeff p

/-- Scaling preserves weighted homogeneity, since it only changes coefficients.
@isnad1 id=isweight.1h6v.s5.1ddd22f25576 from=translated src=- shape=4a7b8de2 vocab=6c68d82b
-/
theorem ordinaryScale_isWeightedHomogeneous {w : ι → ℕ} {q : ℕ}
    (lam : R) (p : MvPolynomial ι R)
    (hp : p.IsWeightedHomogeneous w q) :
    (ordinaryScale lam p).IsWeightedHomogeneous w q := by
  classical
  intro d hd
  rw [ordinaryScale, MvPolynomial.coeff_sum] at hd
  obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [MvPolynomial.coeff_monomial] at hne
  split_ifs at hne with h
  · subst e
    have hc : p.coeff d ≠ 0 := by
      intro hc
      simp [hc] at hne
    exact hp hc
  · contradiction

/-- The entire parameter-polynomial family preserves the original jet grading.
@isnad1 id=isweight.1h5v.s5.9cf73a513204 from=translated src=- shape=b24ab68e vocab=ffa560cc
-/
theorem polynomialScale_isWeightedHomogeneous {w : ι → ℕ} {q : ℕ}
    (p : MvPolynomial ι R) (hp : p.IsWeightedHomogeneous w q) :
    (polynomialScale p).IsWeightedHomogeneous w q := by
  classical
  intro d hd
  rw [polynomialScale, MvPolynomial.coeff_sum] at hd
  obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [MvPolynomial.coeff_monomial] at hne
  split_ifs at hne with h
  · subst e
    have hc : p.coeff d ≠ 0 := by
      intro hc
      simp [hc] at hne
    exact hp hc
  · contradiction

/-- If a polynomial has no constant monomial, the zero-parameter value is its
degree-one part. The hypothesis is deliberately local to the actual support.
@isnad1 id=eq.1h3v.s6.695ecab3ae0e from=translated src=- shape=06b6ace2 vocab=1181f9be
-/
theorem ordinaryScale_zero_eq_linearPart
    (p : MvPolynomial ι R)
    (hconstant : ∀ d ∈ p.support, ordinaryDegree d ≠ 0) :
    ordinaryScale (0 : R) p = linearPart p := by
  classical
  rw [ordinaryScale, linearPart, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hone : ordinaryDegree d = 1
  · simp [ordinaryScaleFactor, hone]
  · have hzero : ordinaryDegree d ≠ 0 := hconstant d hd
    have htwo : 2 ≤ ordinaryDegree d := by omega
    simp [hone, ordinaryScaleFactor_zero_of_two_le d htwo]

/-- A polynomial of positive weighted degree has no ordinary-degree-zero monomial.
@isnad1 id=ne.3h6v.s6.5950ef5d6285 from=translated src=- shape=6943f698 vocab=3e35dd22
-/
theorem ordinaryDegree_ne_zero_of_homogeneous {w : ι → ℕ} {q : ℕ}
    (p : MvPolynomial ι R) (hp : p.IsWeightedHomogeneous w q) (hq : q ≠ 0)
    (d : ι →₀ ℕ) (hd : d ∈ p.support) : ordinaryDegree d ≠ 0 := by
  intro hzero
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hzero
  have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [hd0, map_zero] at hweight
  exact hq hweight.symm

/-- Positive weighted degree alone gives the linear zero specialization.
@isnad1 id=eq.2h5v.s6.7b8d0027b1af from=translated src=- shape=7cacad3c vocab=2058c3c8
-/
theorem ordinaryScale_zero_of_homogeneous {w : ι → ℕ} {q : ℕ}
    (p : MvPolynomial ι R) (hp : p.IsWeightedHomogeneous w q) (hq : q ≠ 0) :
    ordinaryScale (0 : R) p = linearPart p :=
  ordinaryScale_zero_eq_linearPart p
    (ordinaryDegree_ne_zero_of_homogeneous p hp hq)

/-- The polynomial family recovers the original polynomial at parameter one.
@isnad1 id=eq.0h3v.s7.d54a447ad6cc from=translated src=- shape=df0e4102 vocab=45ab2545
-/
@[simp]
theorem polynomialScale_at_one (p : MvPolynomial ι R) :
    specializeParameter 1 (polynomialScale p) = p := by
  rw [specializeParameter_polynomialScale, ordinaryScale_one]

/-- The polynomial family has exactly the linear part at parameter zero.
@isnad1 id=eq.2h5v.s7.0bda8e67fa1d from=translated src=- shape=cc98722f vocab=7f01da1a
-/
theorem polynomialScale_at_zero {w : ι → ℕ} {q : ℕ}
    (p : MvPolynomial ι R) (hp : p.IsWeightedHomogeneous w q) (hq : q ≠ 0) :
    specializeParameter 0 (polynomialScale p) = linearPart p := by
  rw [specializeParameter_polynomialScale]
  exact ordinaryScale_zero_of_homogeneous p hp hq

/-- Evaluation of a scaled polynomial is the finite, actual monomial evaluation
formula. No formal or geometric evaluation is hidden in this definition.
@isnad1 id=eq.0h5v.s7.b4c55d6f256a from=translated src=- shape=cec4274e vocab=6df57841
-/
theorem eval_ordinaryScale (lam : R) (p : MvPolynomial ι R) (a : ι → R) :
    MvPolynomial.eval a (ordinaryScale lam p) =
      ∑ d ∈ p.support,
        (ordinaryScaleFactor lam d * p.coeff d) *
          d.prod (fun i e ↦ a i ^ e) := by
  classical
  simp [ordinaryScale, MvPolynomial.eval_sum, MvPolynomial.eval_monomial]

/-! ## Coefficientwise description of the scaling operators

`ordinaryScale` and `polynomialScale` are defined as sums over a support. The three `coeff_*`
lemmas below describe them one coefficient at a time and are the primitive ones —
everything else here follows from them by `ext`. -/

section Coefficientwise

variable (lam : R) (p q : MvPolynomial ι R) (d : ι →₀ ℕ) (a : R)

/--
@isnad1 id=eq.0h5v.s5.b2184e3d970d from=translated src=- shape=8da79215 vocab=cdb0c1d9
-/
@[simp] theorem coeff_ordinaryScale :
    (ordinaryScale lam p).coeff d = ordinaryScaleFactor lam d * p.coeff d := by
  classical
  simp only [ordinaryScale, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hd : d ∈ p.support
  · rw [Finset.sum_eq_single d (fun b _ hb ↦ ite_eq_right hb) (fun h ↦ absurd hd h), ite_eq_left rfl]
  · rw [MvPolynomial.notMem_support_iff.mp hd, mul_zero]
    refine Finset.sum_eq_zero fun b hb ↦ ite_eq_right ?_
    exact fun h ↦ hd (h ▸ hb)

/--
@isnad1 id=eq.0h4v.s7.feb31d693079 from=translated src=- shape=d4296aef vocab=3fc51d2e
-/
@[simp] theorem coeff_polynomialScale :
    (polynomialScale p).coeff d =
      Polynomial.X ^ (ordinaryDegree d - 1) * Polynomial.C (p.coeff d) := by
  classical
  simp only [polynomialScale, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hd : d ∈ p.support
  · rw [Finset.sum_eq_single d (fun b _ hb ↦ ite_eq_right hb) (fun h ↦ absurd hd h), ite_eq_left rfl]
  · rw [MvPolynomial.notMem_support_iff.mp hd, map_zero, mul_zero]
    refine Finset.sum_eq_zero fun b hb ↦ ite_eq_right ?_
    exact fun h ↦ hd (h ▸ hb)

/--
@isnad1 id=eq.0h4v.s6.26cd386ae18d from=translated src=- shape=9e98efdc vocab=1ddc867e
-/
@[simp] theorem coeff_linearPart :
    (linearPart p).coeff d = if ordinaryDegree d = 1 then p.coeff d else 0 := by
  classical
  simp only [linearPart, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hdeg : ordinaryDegree d = 1
  · rw [ite_eq_left hdeg]
    by_cases hd : d ∈ p.support
    · rw [Finset.sum_eq_single d (fun b _ hb ↦ ite_eq_right hb)
        (fun h ↦ absurd (Finset.mem_filter.mpr ⟨hd, hdeg⟩) h), ite_eq_left rfl]
    · rw [MvPolynomial.notMem_support_iff.mp hd]
      refine Finset.sum_eq_zero fun b hb ↦ ite_eq_right ?_
      exact fun h ↦ hd (h ▸ (Finset.mem_filter.mp hb).1)
  · rw [ite_eq_right hdeg]
    refine Finset.sum_eq_zero fun b hb ↦ ite_eq_right ?_
    exact fun h ↦ hdeg (h ▸ (Finset.mem_filter.mp hb).2)

/-- The scaling operators agree exactly when every coefficient does.
@isnad1 id=eq.1h4v.s5.6961007917b4 from=translated src=- shape=807d4f27 vocab=7608171b
-/
theorem ordinaryScale_ext {r r' : MvPolynomial ι R}
    (h : ∀ d, r.coeff d = r'.coeff d) : r = r' :=
  MvPolynomial.ext _ _ h

/--
@isnad1 id=eq.0h5v.s8.6cc855b33233 from=translated src=- shape=4d755e18 vocab=233a1b91
-/
@[simp] theorem ordinaryScale_monomial :
    ordinaryScale lam (MvPolynomial.monomial d a)
      = MvPolynomial.monomial d (ordinaryScaleFactor lam d * a) := by
  classical
  refine MvPolynomial.ext _ _ fun e ↦ ?_
  rw [coeff_ordinaryScale, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases h : d = e
  · subst h; simp
  · simp [h]

/--
@isnad1 id=eq.0h4v.s9.68233e6b69ca from=translated src=- shape=463fd1ec vocab=2c60ab5a
-/
@[simp] theorem polynomialScale_monomial :
    polynomialScale (MvPolynomial.monomial d a)
      = MvPolynomial.monomial d
          (Polynomial.X ^ (ordinaryDegree d - 1) * Polynomial.C a) := by
  classical
  refine MvPolynomial.ext _ _ fun e ↦ ?_
  rw [coeff_polynomialScale, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases h : d = e
  · subst h; simp
  · simp [h]

/--
@isnad1 id=eq.0h5v.s7.4dd3adbd35ef from=translated src=- shape=fd12fa87 vocab=a69c6fe0
-/
@[simp] theorem ordinaryScale_add :
    ordinaryScale lam (p + q) = ordinaryScale lam p + ordinaryScale lam q := by
  refine MvPolynomial.ext _ _ fun e ↦ ?_
  simp [mul_add]

/--
@isnad1 id=eq.0h4v.s7.4a8e6ec22b43 from=translated src=- shape=d3d7ee24 vocab=9857819d
-/
@[simp] theorem polynomialScale_add :
    polynomialScale (p + q) = polynomialScale p + polynomialScale q := by
  refine MvPolynomial.ext _ _ fun e ↦ ?_
  simp [mul_add]

/--
@isnad1 id=eq.0h3v.s6.36e7aba6b2fc from=translated src=- shape=1cd36439 vocab=89fc9610
-/
@[simp] theorem ordinaryScale_zero_poly :
    ordinaryScale lam (0 : MvPolynomial ι R) = 0 := by
  refine MvPolynomial.ext _ _ fun e ↦ ?_
  simp

/--
@isnad1 id=eq.0h2v.s7.be4f8a8ea4b3 from=translated src=- shape=623d31aa vocab=df88c8c5
-/
@[simp] theorem polynomialScale_zero_poly :
    polynomialScale (0 : MvPolynomial ι R) = 0 := by
  refine MvPolynomial.ext _ _ fun e ↦ ?_
  simp

/--
@isnad1 id=eq.0h5v.s7.c7ba71ae6508 from=translated src=- shape=c11c2b54 vocab=82f5cf67
-/
@[simp] theorem ordinaryScale_smul (c : R) :
    ordinaryScale lam (c • p) = c • ordinaryScale lam p := by
  refine MvPolynomial.ext _ _ fun e ↦ ?_
  simp only [MvPolynomial.coeff_smul, coeff_ordinaryScale, smul_eq_mul]
  ring

/-- `ordinaryScale lam` is an `R`-linear map; the library only had the bare function.-/
def ordinaryScaleHom : MvPolynomial ι R →ₗ[R] MvPolynomial ι R where
  toFun := ordinaryScale lam
  map_add' := ordinaryScale_add lam
  map_smul' := fun c r ↦ ordinaryScale_smul lam r c

/--
@isnad1 id=eq.0h4v.s7.8c866b1254c7 from=translated src=- shape=69e08ce1 vocab=81a52d4d
-/
@[simp] theorem ordinaryScaleHom_apply :
    ordinaryScaleHom lam p = ordinaryScale lam p := rfl

/-- `polynomialScale` is additive; it is not `R`-linear, because the parameter enters the
coefficient ring.-/
def polynomialScaleHom : MvPolynomial ι R →+ MvPolynomial ι (Polynomial R) where
  toFun := polynomialScale
  map_zero' := polynomialScale_zero_poly
  map_add' := polynomialScale_add

/--
@isnad1 id=eq.0h3v.s7.f430a6674c9a from=translated src=- shape=c42aaa01 vocab=8143f275
-/
@[simp] theorem polynomialScaleHom_apply :
    polynomialScaleHom p = polynomialScale p := rfl

/-- The support of a scaled polynomial is contained in the original support.
@isnad1 id=le.0h4v.s5.55fe9e80bc2c from=translated src=- shape=1db95164 vocab=297d455a
-/
theorem support_ordinaryScale_subset :
    (ordinaryScale lam p).support ⊆ p.support := by
  intro d hd
  by_contra h
  rw [MvPolynomial.mem_support_iff, coeff_ordinaryScale,
    MvPolynomial.notMem_support_iff.mp h, mul_zero] at hd
  exact hd rfl

end Coefficientwise

/-- A pair of scaled forward and inverse polynomial substitutions. The fields are
actual polynomials; inverse identities are retained as separate propositions so
that specialization at a nonzero parameter is not confused with a definition.-/
structure PolynomialPair (ι R : Type*) [CommSemiring R] where
  forward : ι → MvPolynomial ι R
  inverse : ι → MvPolynomial ι R

namespace PolynomialPair

/-- Apply ordinary scaling to both actual polynomial directions over any coefficient ring.-/
def scale (F : PolynomialPair ι R) (lam : R) : PolynomialPair ι R where
  forward := fun i ↦ ordinaryScale lam (F.forward i)
  inverse := fun i ↦ ordinaryScale lam (F.inverse i)

/-- Both directions form polynomial families over the same parameter ring.-/
def polynomialFamily (F : PolynomialPair ι R) : PolynomialPair ι (Polynomial R) where
  forward := fun i ↦ polynomialScale (F.forward i)
  inverse := fun i ↦ polynomialScale (F.inverse i)

/--
@isnad1 id=eq.0h5v.s7.40f352eb983d from=translated src=- shape=ed14ce64 vocab=fe83ca8f
-/
@[simp]
theorem polynomialFamily_forward_specialize (F : PolynomialPair ι R) (lam : R) (i : ι) :
    specializeParameter lam (F.polynomialFamily.forward i) = (F.scale lam).forward i :=
  specializeParameter_polynomialScale lam (F.forward i)

/--
@isnad1 id=eq.0h5v.s7.c9e1bc459a89 from=translated src=- shape=ed14ce64 vocab=8cc57b16
-/
@[simp]
theorem polynomialFamily_inverse_specialize (F : PolynomialPair ι R) (lam : R) (i : ι) :
    specializeParameter lam (F.polynomialFamily.inverse i) = (F.scale lam).inverse i :=
  specializeParameter_polynomialScale lam (F.inverse i)

/-- The zero-parameter forward family is linear for positive weighted transitions.
@isnad1 id=eq.1h5v.s7.758123665d03 from=translated src=- shape=fa72a9a7 vocab=af573ecf
-/
theorem polynomialFamily_forward_at_zero (F : PolynomialPair ι R) (w : ι → ℕ+)
    (hF : ∀ i, (F.forward i).IsWeightedHomogeneous (fun j ↦ (w j : ℕ)) (w i : ℕ))
    (i : ι) :
    specializeParameter 0 (F.polynomialFamily.forward i) = linearPart (F.forward i) :=
  polynomialScale_at_zero (F.forward i) (hF i) (w i).ne_zero

/-- The same zero specialization holds for the actual inverse polynomial direction.
@isnad1 id=eq.1h5v.s7.7135e6a1f2a6 from=translated src=- shape=fa72a9a7 vocab=f4603a44
-/
theorem polynomialFamily_inverse_at_zero (F : PolynomialPair ι R) (w : ι → ℕ+)
    (hF : ∀ i, (F.inverse i).IsWeightedHomogeneous (fun j ↦ (w j : ℕ)) (w i : ℕ))
    (i : ι) :
    specializeParameter 0 (F.polynomialFamily.inverse i) = linearPart (F.inverse i) :=
  polynomialScale_at_zero (F.inverse i) (hF i) (w i).ne_zero

/-- Evaluation of the forward member of a scale family at an actual tuple.-/
def evalForward (F : PolynomialPair ι R) (a : ι → R) : ι → R :=
  fun i ↦ MvPolynomial.eval a (F.forward i)

/-- Evaluation of the inverse member of a scale family at an actual tuple.-/
def evalInverse (F : PolynomialPair ι R) (a : ι → R) : ι → R :=
  fun i ↦ MvPolynomial.eval a (F.inverse i)

end PolynomialPair

namespace WeightedPolynomialEquiv

variable {K : Type*} [Field K] {w : ι → ℕ+}

/-- Ordinary-degree scaling of both polynomial directions of an actual weighted
polynomial equivalence.-/
def scaleFamily (G : WeightedPolynomialEquiv (K := K) w) (lam : K) : PolynomialPair ι K where
  forward := fun i ↦ ordinaryScale lam (G.forward i)
  inverse := fun i ↦ ordinaryScale lam (G.inverse i)

/--
@isnad1 id=eq.0h6v.s6.04645024ad25 from=translated src=- shape=b3019910 vocab=9ef173bd
-/
@[simp]
theorem scaleFamily_forward_apply (G : WeightedPolynomialEquiv (K := K) w) (lam : K) (i : ι) :
    (scaleFamily G lam).forward i = ordinaryScale lam (G.forward i) := rfl

/--
@isnad1 id=eq.0h6v.s6.cf893c4872db from=translated src=- shape=b3019910 vocab=7da8e11c
-/
@[simp]
theorem scaleFamily_inverse_apply (G : WeightedPolynomialEquiv (K := K) w) (lam : K) (i : ι) :
    (scaleFamily G lam).inverse i = ordinaryScale lam (G.inverse i) := rfl

/--
@isnad1 id=isweight.0h6v.s5.d02f8e48a243 from=translated src=- shape=77bf63cd vocab=cefb24e6
-/
theorem scaleFamily_forward_homogeneous (G : WeightedPolynomialEquiv (K := K) w)
    (lam : K) (i : ι) :
    ((scaleFamily G lam).forward i).IsWeightedHomogeneous
      (fun j ↦ (w j : ℕ)) (w i) :=
  ordinaryScale_isWeightedHomogeneous lam (G.forward i) (G.forward_homogeneous i)

/--
@isnad1 id=isweight.0h6v.s5.36b9537fc1a8 from=translated src=- shape=77bf63cd vocab=9f5be4e3
-/
theorem scaleFamily_inverse_homogeneous (G : WeightedPolynomialEquiv (K := K) w)
    (lam : K) (i : ι) :
    ((scaleFamily G lam).inverse i).IsWeightedHomogeneous
      (fun j ↦ (w j : ℕ)) (w i) :=
  ordinaryScale_isWeightedHomogeneous lam (G.inverse i) (G.inverse_homogeneous i)

/--
@isnad1 id=eq.0h5v.s6.90f15daed56f from=translated src=- shape=83374913 vocab=9f28968c
-/
@[simp]
theorem scaleFamily_forward_at_one (G : WeightedPolynomialEquiv (K := K) w) (i : ι) :
    (scaleFamily G 1).forward i = G.forward i := by
  simp [scaleFamily, ordinaryScale_one]

/--
@isnad1 id=eq.0h5v.s6.ec5740683360 from=translated src=- shape=83374913 vocab=ce66a426
-/
@[simp]
theorem scaleFamily_inverse_at_one (G : WeightedPolynomialEquiv (K := K) w) (i : ι) :
    (scaleFamily G 1).inverse i = G.inverse i := by
  simp [scaleFamily, ordinaryScale_one]

/--
@isnad1 id=eq.0h5v.s6.eafb2308641d from=translated src=- shape=1a427f03 vocab=593f4d8b
-/
theorem scaleFamily_forward_at_zero (G : WeightedPolynomialEquiv (K := K) w)
    (i : ι) :
    (scaleFamily G 0).forward i = linearPart (G.forward i) := by
  change ordinaryScale (0 : K) (G.forward i) = _
  exact ordinaryScale_zero_of_homogeneous (G.forward i) (G.forward_homogeneous i)
    (w i).ne_zero

/--
@isnad1 id=eq.0h5v.s6.040500a3f297 from=translated src=- shape=1a427f03 vocab=e03400d4
-/
theorem scaleFamily_inverse_at_zero (G : WeightedPolynomialEquiv (K := K) w)
    (i : ι) :
    (scaleFamily G 0).inverse i = linearPart (G.inverse i) := by
  change ordinaryScale (0 : K) (G.inverse i) = _
  exact ordinaryScale_zero_of_homogeneous (G.inverse i) (G.inverse_homogeneous i)
    (w i).ne_zero

/-- The forward scale family has the literal finite evaluation formula required
by the jet transition construction.
@isnad1 id=eq.0h7v.s7.15c3dda2c64b from=translated src=- shape=fc26ac8c vocab=bcaf6116
-/
theorem scaleFamily_evalForward (G : WeightedPolynomialEquiv (K := K) w)
    (lam : K) (a : ι → K) (i : ι) :
    (scaleFamily G lam).evalForward a i =
      ∑ d ∈ (G.forward i).support,
        (ordinaryScaleFactor lam d * (G.forward i).coeff d) *
          d.prod (fun j e ↦ a j ^ e) := by
  exact eval_ordinaryScale lam (G.forward i) a

/-- The inverse scale family has the same literal finite evaluation formula.
@isnad1 id=eq.0h7v.s7.fc4afbf68a63 from=translated src=- shape=fc26ac8c vocab=90789f4e
-/
theorem scaleFamily_evalInverse (G : WeightedPolynomialEquiv (K := K) w)
    (lam : K) (a : ι → K) (i : ι) :
    (scaleFamily G lam).evalInverse a i =
      ∑ d ∈ (G.inverse i).support,
        (ordinaryScaleFactor lam d * (G.inverse i).coeff d) *
          d.prod (fun j e ↦ a j ^ e) := by
  exact eval_ordinaryScale lam (G.inverse i) a

end WeightedPolynomialEquiv

end MiyaokaMori.JetTransition
