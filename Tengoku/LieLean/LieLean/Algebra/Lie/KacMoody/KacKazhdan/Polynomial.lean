/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.Seed.Algebra.MvPolynomial.Funext
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial functions on a dual space and leading terms of determinants

This file collects the (Lie-theory-free) algebra needed to study the Shapovalov determinant as a
polynomial function of the highest weight.

* The top homogeneous component of a product of multivariate polynomials `pᵢ` of total degree
  `≤ dᵢ` is the product of their components of degree `dᵢ`.
* The **leading term of a determinant**: if the entries of a matrix `M` of polynomials satisfy
  `deg Mᵢⱼ ≤ min(dᵢ, dⱼ)`, and the components of degree `dᵢ` of the off-diagonal entries `Mᵢⱼ` with
  `dᵢ = dⱼ` vanish, then `deg det M ≤ ∑ dᵢ` and the component of `det M` of degree `∑ dᵢ` is the
  product of the components of degree `dᵢ` of the diagonal entries.
* Polynomial functions on the dual `H*` of a finite-dimensional vector space `H`: the evaluation
  `Module.Dual.evalPoly` of polynomials in the coordinates of a fixed basis of `H`, the linear
  polynomials `Module.Dual.linPoly a` (`λ ↦ λ(a)`), the space `Module.Dual.polyLE d` of polynomial
  functions of degree `≤ d`, and the predicate `Module.Dual.HasTop d q F`: `F` is a polynomial
  function of degree `≤ d` whose homogeneous component of degree `d` is `q`.

## Main results

* `MvPolynomial.homogeneousComponent_mul_of_totalDegree_le`,
  `MvPolynomial.homogeneousComponent_prod_of_totalDegree_le`: top components of products.
* `MvPolynomial.homogeneousComponent_det`: the leading term of a determinant.
* `Module.Dual.evalPoly_injective`: over an infinite field, polynomials are determined by the
  functions they define on `H*`.

## References

Elementary commutative algebra, used for the leading term of the Shapovalov determinant
([KK]; [Kum] Thm. 2.3.4, proof, Step 2).

* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002.
-/

open Module

noncomputable section

namespace MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The component of degree `m + n` of `p * q`, where `deg p ≤ m` and `deg q ≤ n`, is the product
of the components of degree `m` of `p` and of degree `n` of `q`.
@isnad1 id=eq.2h6v.s9.b4c0066b6ffe from=translated src=- shape=ec58a891 vocab=ffc04f86
-/
theorem homogeneousComponent_mul_of_totalDegree_le {p q : MvPolynomial σ R} {m n : ℕ}
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    homogeneousComponent (m + n) (p * q) =
      homogeneousComponent m p * homogeneousComponent n q := by
  classical
  ext d
  have hhom := ((homogeneousComponent_isHomogeneous m p).mul
    (homogeneousComponent_isHomogeneous n q))
  rw [coeff_homogeneousComponent]
  split_ifs with hd
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun ab hab ↦ ?_
    rw [Finset.mem_antidiagonal] at hab
    have hdeg : ab.1.degree + ab.2.degree = m + n := by rw [← map_add, hab, hd]
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases h1 : ab.1.degree = m
    · have h2 : ab.2.degree = n := by omega
      simp [h1, h2]
    · simp only [h1, ↓reduceIte, zero_mul]
      rcases lt_or_gt_of_ne h1 with h1 | h1
      · have h2 : n < ab.2.degree := by omega
        rw [coeff_eq_zero_of_totalDegree_lt (hq.trans_lt h2), mul_zero]
      · rw [coeff_eq_zero_of_totalDegree_lt (hp.trans_lt h1), zero_mul]
  · exact (hhom.coeff_eq_zero hd).symm

/-- The component of degree `∑ dᵢ` of `∏ pᵢ`, where `deg pᵢ ≤ dᵢ`, is the product of the
components of degree `dᵢ` of the `pᵢ`.
@isnad1 id=eq.1h6v.s8.24f703ffb07e from=translated src=- shape=7ad548ce vocab=652ce768
-/
theorem homogeneousComponent_prod_of_totalDegree_le {κ : Type*} (s : Finset κ)
    (p : κ → MvPolynomial σ R) (d : κ → ℕ) (h : ∀ i ∈ s, (p i).totalDegree ≤ d i) :
    homogeneousComponent (∑ i ∈ s, d i) (∏ i ∈ s, p i) =
      ∏ i ∈ s, homogeneousComponent (d i) (p i) := by
  induction s using Finset.cons_induction with
  | empty => simp [homogeneousComponent_zero]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.prod_cons, Finset.prod_cons,
      homogeneousComponent_mul_of_totalDegree_le (h a (Finset.mem_cons_self a s)),
      ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi)]
    refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    exact h i (Finset.mem_cons_of_mem hi)

end CommSemiring

section CommRing

variable [CommRing R]

/-- **The leading term of a determinant.** Let `M` be a square matrix of polynomials and `d` a
function on its index set with `deg Mᵢⱼ ≤ min(dᵢ, dⱼ)`, such that the component of degree `dᵢ` of
`Mᵢⱼ` vanishes for `i ≠ j` with `dᵢ = dⱼ`. Then `deg det M ≤ ∑ dᵢ`, and the component of degree
`∑ dᵢ` of `det M` is the product of the components of degree `dᵢ` of the diagonal entries `Mᵢᵢ`.
@isnad1 id=and.2h5v.s9.d35a3b87f098 from=translated src=- shape=929655b9 vocab=8eeb3110
-/
theorem homogeneousComponent_det {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial σ R)) (d : n → ℕ)
    (hdeg : ∀ i j, (M i j).totalDegree ≤ min (d i) (d j))
    (htop : ∀ i j, i ≠ j → d i = d j → homogeneousComponent (d i) (M i j) = 0) :
    M.det.totalDegree ≤ ∑ i, d i ∧
      homogeneousComponent (∑ i, d i) M.det = ∏ i, homogeneousComponent (d i) (M i i) := by
  have hprod : ∀ τ : Equiv.Perm n,
      (∏ i, M (τ i) i).totalDegree ≤ ∑ i, min (d (τ i)) (d i) := fun τ ↦
    (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ ↦ hdeg (τ i) i)
  have hmin : ∀ τ : Equiv.Perm n, ∑ i, min (d (τ i)) (d i) ≤ ∑ i, d i := fun τ ↦
    Finset.sum_le_sum fun i _ ↦ min_le_right _ _
  have hterm : ∀ τ : Equiv.Perm n,
      (Equiv.Perm.sign τ • ∏ i, M (τ i) i).totalDegree ≤ ∑ i, d i := fun τ ↦ by
    rw [Units.smul_def, zsmul_eq_mul]
    refine (totalDegree_mul _ _).trans ?_
    rw [← map_intCast (C : R →+* MvPolynomial σ R), totalDegree_C, zero_add]
    exact (hprod τ).trans (hmin τ)
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_apply]
    exact (totalDegree_finsetSum _ _).trans (Finset.sup_le fun τ _ ↦ hterm τ)
  rw [Matrix.det_apply, map_sum, Finset.sum_eq_single (1 : Equiv.Perm n)]
  · simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.one_apply]
    exact homogeneousComponent_prod_of_totalDegree_le _ _ _ fun i _ ↦
      (hdeg i i).trans (min_le_right _ _)
  · intro τ _ hτ
    rw [map_zsmul_unit]
    by_cases hd : ∀ i, d (τ i) = d i
    · obtain ⟨i, hi⟩ : ∃ i, τ i ≠ i := by
        by_contra! h
        exact hτ (Equiv.ext h)
      rw [homogeneousComponent_prod_of_totalDegree_le _ _ _ fun i _ ↦
        (hdeg (τ i) i).trans (min_le_right _ _), Finset.prod_eq_zero (Finset.mem_univ i),
        smul_zero]
      rw [← hd i]
      exact htop (τ i) i hi (hd i)
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      have hlt : ∑ i, min (d (τ i)) (d i) < ∑ i, d i := by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact Finset.sum_lt_sum (fun j _ ↦ min_le_right _ _)
            ⟨i, Finset.mem_univ i, (min_le_left _ _).trans_lt hi⟩
        · -- some other index must go down
          have hsum : ∑ j, d (τ j) = ∑ j, d j := Equiv.sum_comp τ d
          obtain ⟨j, hj⟩ : ∃ j, d (τ j) < d j := by
            by_contra! h
            have := Finset.sum_lt_sum (fun j _ ↦ h j) ⟨i, Finset.mem_univ i, hi⟩
            omega
          exact Finset.sum_lt_sum (fun j _ ↦ min_le_right _ _)
            ⟨j, Finset.mem_univ j, (min_le_left _ _).trans_lt hj⟩
      rw [homogeneousComponent_eq_zero _ _ ((hprod τ).trans_lt hlt), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end CommRing

end MvPolynomial

/-! ### Polynomial functions on a dual space -/

namespace Module.Dual

variable (K H : Type*) [Field K] [AddCommGroup H] [Module K H]

/-- The index set of the chosen basis of `H`: polynomial functions on `H*` are polynomials in the
corresponding coordinates.-/
abbrev PolyIdx : Type _ := Module.Free.ChooseBasisIndex K H

/-- The evaluation of polynomials in the coordinates `λ ↦ λ(bⱼ)` of `H*` (with respect to the
chosen basis `(bⱼ)` of `H`), as an algebra morphism to the functions on `H*`.-/
def evalPoly : MvPolynomial (PolyIdx K H) K →ₐ[K] (Dual K H → K) :=
  AlgHom.pi fun Λ ↦ MvPolynomial.aeval fun j ↦ Λ (Module.Free.chooseBasis K H j)

/-- The linear polynomial `λ ↦ λ(a)` attached to `a ∈ H`.-/
def linPoly : H →ₗ[K] MvPolynomial (PolyIdx K H) K :=
  (Module.Free.chooseBasis K H).constr K MvPolynomial.X

variable {K H}

/--
@isnad1 id=eq.0h4v.s10.699eb14395ef from=translated src=- shape=23ceb6a8 vocab=b191a927
-/
lemma evalPoly_apply (p : MvPolynomial (PolyIdx K H) K) (Λ : Dual K H) :
    evalPoly K H p Λ = MvPolynomial.aeval (fun j ↦ Λ (Module.Free.chooseBasis K H j)) p := rfl

/--
@isnad1 id=eq.0h4v.s9.149e50a012c2 from=translated src=- shape=3d35e655 vocab=d99e52e3
-/
@[simp] lemma evalPoly_linPoly (a : H) (Λ : Dual K H) : evalPoly K H (linPoly K H a) Λ = Λ a := by
  have : (LinearMap.proj Λ ∘ₗ (evalPoly K H).toLinearMap) ∘ₗ
      linPoly K H = Λ := (Module.Free.chooseBasis K H).ext fun j ↦ by
    simp [linPoly, evalPoly_apply]
  exact LinearMap.congr_fun this a

/--
@isnad1 id=ishomoge.0h3v.s8.4ee6ebb0ae35 from=translated src=- shape=61ae5e4b vocab=84ece8a6
-/
lemma isHomogeneous_linPoly (a : H) : (linPoly K H a).IsHomogeneous 1 := by
  rw [linPoly, Basis.constr_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ ↦ ?_
  simp only [MvPolynomial.smul_eq_C_mul]
  simpa using (MvPolynomial.isHomogeneous_X K j).C_mul ((Module.Free.chooseBasis K H).repr a j)

/--
@isnad1 id=ne.1h3v.s8.6a07fab99e6b from=translated src=- shape=2658f16a vocab=f14c8d48
-/
lemma linPoly_ne_zero {a : H} (ha : a ≠ 0) : linPoly K H a ≠ 0 := by
  intro h
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Dual K H, Λ a ≠ 0 := by
    by_contra! h'
    exact ha ((Module.forall_dual_apply_eq_zero_iff K a).mp h')
  apply hΛ
  rw [← evalPoly_linPoly, h, map_zero, Pi.zero_apply]

/--
@isnad1 id=le.0h3v.s8.ef3811ba2f45 from=translated src=- shape=5716e2d5 vocab=de8d8f65
-/
lemma totalDegree_linPoly_le (a : H) : (linPoly K H a).totalDegree ≤ 1 :=
  (isHomogeneous_linPoly a).totalDegree_le

/-- Over an infinite field, a polynomial is determined by the function it defines on `H*`.
@isnad1 id=injectiv.0h2v.s8.edd003fe28d5 from=translated src=- shape=cee99aed vocab=8d538fff
-/
theorem evalPoly_injective [Infinite K] : Function.Injective (evalPoly K H) := by
  intro p q hpq
  refine MvPolynomial.funext fun x ↦ ?_
  have := congr_fun hpq ((Module.Free.chooseBasis K H).constr K x)
  simpa [evalPoly_apply, Basis.constr_basis, MvPolynomial.coe_aeval_eq_eval] using this

variable (K H) in
/-- The polynomial functions on `H*` of degree at most `d`.-/
def polyLE (d : ℕ) : Submodule K (Dual K H → K) :=
  (MvPolynomial.restrictTotalDegree (PolyIdx K H) K d).map (evalPoly K H).toLinearMap

/--
@isnad1 id=iff.0h4v.s9.2a6f10c1fc6e from=translated src=- shape=7b63c7ed vocab=878c42a6
-/
lemma mem_polyLE {d : ℕ} {F : Dual K H → K} :
    F ∈ polyLE K H d ↔ ∃ p : MvPolynomial (PolyIdx K H) K, p.totalDegree ≤ d ∧
      evalPoly K H p = F := by
  simp [polyLE, MvPolynomial.mem_restrictTotalDegree]

/--
@isnad1 id=le.1h4v.s9.23c7059460af from=translated src=- shape=79ec158d vocab=d8d35b7e
-/
lemma polyLE_mono {d e : ℕ} (h : d ≤ e) : polyLE K H d ≤ polyLE K H e := fun _ hF ↦ by
  obtain ⟨p, hp, rfl⟩ := mem_polyLE.mp hF
  exact mem_polyLE.mpr ⟨p, hp.trans h, rfl⟩

/--
@isnad1 id=mem.0h3v.s9.319344ec3467 from=translated src=- shape=ac0f28ed vocab=eab2555d
-/
lemma one_mem_polyLE (d : ℕ) : (1 : Dual K H → K) ∈ polyLE K H d :=
  mem_polyLE.mpr ⟨1, by simp, map_one _⟩

/--
@isnad1 id=mem.2h6v.s10.336dfe836b2d from=translated src=- shape=1e55dbf1 vocab=25d23558
-/
lemma mul_mem_polyLE {d e : ℕ} {F G : Dual K H → K} (hF : F ∈ polyLE K H d)
    (hG : G ∈ polyLE K H e) : F * G ∈ polyLE K H (d + e) := by
  obtain ⟨p, hp, rfl⟩ := mem_polyLE.mp hF
  obtain ⟨q, hq, rfl⟩ := mem_polyLE.mp hG
  exact mem_polyLE.mpr ⟨p * q, (MvPolynomial.totalDegree_mul _ _).trans (add_le_add hp hq),
    map_mul _ _ _⟩

/--
@isnad1 id=mem.0h3v.s9.8cb5260ee118 from=translated src=- shape=61b1719e vocab=487d5754
-/
lemma apply_mem_polyLE (a : H) : (fun Λ : Dual K H ↦ Λ a) ∈ polyLE K H 1 :=
  mem_polyLE.mpr ⟨linPoly K H a, totalDegree_linPoly_le a, funext (evalPoly_linPoly a)⟩

/-- `F` is a polynomial function on `H*` of degree at most `d` whose homogeneous component of
degree `d` is `q`.-/
def HasTop (d : ℕ) (q : MvPolynomial (PolyIdx K H) K) (F : Dual K H → K) : Prop :=
  ∃ p : MvPolynomial (PolyIdx K H) K, p.totalDegree ≤ d ∧
    MvPolynomial.homogeneousComponent d p = q ∧ evalPoly K H p = F

namespace HasTop

variable {d : ℕ} {q q' : MvPolynomial (PolyIdx K H) K} {F G : Dual K H → K}

/--
@isnad1 id=mem.1h5v.s8.a069eba5eb50 from=translated src=- shape=a541f4fc vocab=de94181d
-/
lemma mem_polyLE (h : HasTop d q F) : F ∈ polyLE K H d := by
  obtain ⟨p, hp, -, rfl⟩ := h
  exact Module.Dual.mem_polyLE.mpr ⟨p, hp, rfl⟩

/--
@isnad1 id=hastop.0h3v.s7.8a8b559f7ea3 from=translated src=- shape=f3c27f32 vocab=c3ef597d
-/
lemma zero (d : ℕ) : HasTop d 0 (0 : Dual K H → K) := ⟨0, by simp, map_zero _, map_zero _⟩

/--
@isnad1 id=hastop.2h7v.s8.0e73b2044e33 from=translated src=- shape=d430de21 vocab=8bdf212d
-/
lemma add (hF : HasTop d q F) (hG : HasTop d q' G) : HasTop d (q + q') (F + G) := by
  obtain ⟨p, hp, rfl, rfl⟩ := hF
  obtain ⟨p', hp', rfl, rfl⟩ := hG
  exact ⟨p + p', (MvPolynomial.totalDegree_add _ _).trans (max_le hp hp'), map_add _ _ _,
    map_add _ _ _⟩

/--
@isnad1 id=hastop.1h6v.s8.19a7887a86b9 from=translated src=- shape=73cf6648 vocab=f74c3dcb
-/
lemma smul (c : K) (hF : HasTop d q F) : HasTop d (c • q) (c • F) := by
  obtain ⟨p, hp, rfl, rfl⟩ := hF
  exact ⟨c • p, (MvPolynomial.totalDegree_smul_le _ _).trans hp, map_smul _ _ _,
    map_smul _ _ _⟩

/--
@isnad1 id=hastop.1h7v.s7.8d9d634af0f8 from=translated src=- shape=e59edc9b vocab=96796ad7
-/
lemma sum {κ : Type*} (s : Finset κ) {q : κ → MvPolynomial (PolyIdx K H) K}
    {F : κ → Dual K H → K} (h : ∀ i ∈ s, HasTop d (q i) (F i)) :
    HasTop d (∑ i ∈ s, q i) (∑ i ∈ s, F i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using zero d
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (h a (Finset.mem_cons_self a s)).add (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))

/--
@isnad1 id=hastop.2h5v.s9.fe6d71bda295 from=translated src=- shape=334765e0 vocab=c07ab4ae
-/
lemma of_mem_polyLE {e : ℕ} (hF : F ∈ polyLE K H e) (h : e < d) : HasTop d 0 F := by
  obtain ⟨p, hp, rfl⟩ := Module.Dual.mem_polyLE.mp hF
  exact ⟨p, hp.trans h.le, MvPolynomial.homogeneousComponent_eq_zero _ _ (hp.trans_lt h), rfl⟩

/--
@isnad1 id=hastop.1h4v.s8.77e176331541 from=translated src=- shape=0aa3af01 vocab=eb2348dd
-/
lemma of_isHomogeneous (hq : q.IsHomogeneous d) : HasTop d q (evalPoly K H q) :=
  ⟨q, hq.totalDegree_le, MvPolynomial.homogeneousComponent_eq_self hq, rfl⟩

/--
@isnad1 id=hastop.2h8v.s8.d2327fd4f5af from=translated src=- shape=852a7677 vocab=71b68631
-/
lemma mul {e : ℕ} (hF : HasTop d q F) (hG : HasTop e q' G) : HasTop (d + e) (q * q') (F * G) := by
  obtain ⟨p, hp, rfl, rfl⟩ := hF
  obtain ⟨p', hp', rfl, rfl⟩ := hG
  exact ⟨p * p', (MvPolynomial.totalDegree_mul _ _).trans (add_le_add hp hp'),
    MvPolynomial.homogeneousComponent_mul_of_totalDegree_le hp hp', map_mul _ _ _⟩

/--
@isnad1 id=hastop.2h6v.s6.9726a44e5fb1 from=translated src=- shape=b11c4c6e vocab=46717140
-/
lemma congr_fun (hF : HasTop d q F) (h : F = G) : HasTop d q G := h ▸ hF

/-- If the top component is nonzero, the polynomial function has degree exactly `d`.
@isnad1 id=ex.2h5v.s9.a5413dca1f62 from=translated src=- shape=bb7ea14c vocab=e333485b
-/
lemma exists_totalDegree_eq (h : HasTop d q F) (hq : q ≠ 0) :
    ∃ p : MvPolynomial (PolyIdx K H) K, p.totalDegree = d ∧ evalPoly K H p = F := by
  obtain ⟨p, hp, rfl, rfl⟩ := h
  refine ⟨p, le_antisymm hp (not_lt.mp fun hlt ↦ hq ?_), rfl⟩
  exact MvPolynomial.homogeneousComponent_eq_zero _ _ hlt

/--
@isnad1 id=eq.2h6v.s6.a4d2f251be2f from=translated src=- shape=65f0d1ce vocab=d9ab6ec0
-/
lemma unique [Infinite K] (hF : HasTop d q F) (hF' : HasTop d q' F) : q = q' := by
  obtain ⟨p, -, rfl, hp⟩ := hF
  obtain ⟨p', -, rfl, hp'⟩ := hF'
  rw [evalPoly_injective (hp.trans hp'.symm)]

end HasTop

end Module.Dual
