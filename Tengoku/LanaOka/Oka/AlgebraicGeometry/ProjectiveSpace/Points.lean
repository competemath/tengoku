/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.LanaOka.Oka.AlgebraicGeometry.ProjectiveSpace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Points of projective space with values in a field

Let `φ : R →+* K` be a ring map to a field. A vector `z ∈ Kⁿ` gives the point `evalPoint φ z` of
`𝔸ⁿ_R = Spec R[Y₀, …, Yₙ₋₁]`, the kernel of evaluation at `z`. For `v ∈ Kⁿ⁺¹` with `vᵢ ≠ 0`, the
standard chart `i` sends the point of the dehomogenised vector `(v_{i.succAbove m} / vᵢ)ₘ` to a
point of `ℙ(n; R)` which lies in `U j` exactly when `vⱼ ≠ 0`
(`chart_base_evalPoint_mem_U_iff`), and which does not depend on the chart
(`chart_base_evalPoint_eq`): these are the chart transition maps `z ↦ (zₖ / zⱼ)` in coordinates.

The proof of independence goes through the degree-zero localisation at `Xᵢ Xⱼ`: evaluation at
`v` is defined on `A_(x)` for every `x` not vanishing at `v` (`awayEval`), and it is compatible
with `HomogeneousLocalization.awayMap`, so both charts factor through `Spec A_(Xᵢ Xⱼ)`
(`Proj.SpecMap_awayMap_awayι`).
-/

open CategoryTheory MvPolynomial HomogeneousLocalization

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : ℕ} {R : Type u} [CommRing R] {K : Type*} [Field K] (φ : R →+* K)

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

/-- The point of `𝔸ⁿ_R = Spec R[Y₀, …, Yₙ₋₁]` given by `z ∈ Kⁿ`: the kernel of evaluation at `z`
(through `φ : R →+* K`). -/
noncomputable def evalPoint (z : Fin n → K) : Spec (.of (MvPolynomial (Fin n) R)) :=
  show PrimeSpectrum (MvPolynomial (Fin n) R) from
    ⟨RingHom.ker (eval₂Hom φ z), RingHom.ker_isPrime _⟩

/--
@isnad1 id=eq.0h5v.s8.2adb3a43def4 from=translated src=- shape=368ad005 vocab=e86707df
-/
lemma evalPoint_asIdeal (z : Fin n → K) :
    (show PrimeSpectrum (MvPolynomial (Fin n) R) from evalPoint φ z).asIdeal =
      RingHom.ker (eval₂Hom φ z) :=
  rfl

/--
@isnad1 id=iff.0h6v.s8.3cacc6140999 from=translated src=- shape=5761ac21 vocab=e764122c
-/
lemma mem_evalPoint_asIdeal_iff (z : Fin n → K) (p : MvPolynomial (Fin n) R) :
    p ∈ (show PrimeSpectrum (MvPolynomial (Fin n) R) from evalPoint φ z).asIdeal ↔
      eval₂ φ z p = 0 :=
  RingHom.mem_ker

/-- For surjective `φ`, distinct vectors give distinct points of `𝔸ⁿ_R`.
@isnad1 id=injectiv.1h4v.s6.714190806f2a from=translated src=- shape=ed4eb33c vocab=8203482a
-/
lemma evalPoint_injective (hφ : Function.Surjective φ) :
    Function.Injective (evalPoint (n := n) φ) := by
  intro z z' h
  funext m
  obtain ⟨r, hr⟩ := hφ (z m)
  have h1 : X m - C r ∈ (show PrimeSpectrum (MvPolynomial (Fin n) R) from evalPoint φ z).asIdeal :=
    (mem_evalPoint_asIdeal_iff φ z _).2 (by simp [hr])
  rw [h, mem_evalPoint_asIdeal_iff] at h1
  simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
  rw [← hr]
  exact (sub_eq_zero.1 h1).symm

/-- The dehomogenisation `(v_{i.succAbove m} / vᵢ)ₘ` of `v ∈ Kⁿ⁺¹` at the index `i`. -/
def dehomogenizeVec (i : Fin (n + 1)) (v : Fin (n + 1) → K) : Fin n → K :=
  fun m ↦ v (i.succAbove m) / v i

/--
@isnad1 id=eq.1h5v.s7.1768f0de133e from=translated src=- shape=696ba01d vocab=be065cea
-/
lemma dehomogenizeVec_smul (i : Fin (n + 1)) (v : Fin (n + 1) → K) {c : K} (hc : c ≠ 0) :
    dehomogenizeVec i (c • v) = dehomogenizeVec i v := by
  funext m
  simp only [dehomogenizeVec, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

/--
@isnad1 id=eq.0h4v.s6.e7c65782375c from=translated src=- shape=1251124c vocab=e6f2d5ce
-/
@[simp]
lemma dehomogenizeVec_insertNth (i : Fin (n + 1)) (z : Fin n → K) :
    dehomogenizeVec i (Fin.insertNth i 1 z) = z := by
  funext m
  simp [dehomogenizeVec]

/-- Evaluating the dehomogenisation of `Xⱼ` at the dehomogenised vector gives `vⱼ / vᵢ`.
@isnad1 id=eq.1h7v.s9.f1edad05b3e2 from=translated src=- shape=1624119c vocab=68da1ccb
-/
lemma eval₂_dehomogenize_X (i j : Fin (n + 1)) (v : Fin (n + 1) → K) (hi : v i ≠ 0) :
    eval₂ φ (dehomogenizeVec i v) (dehomogenize R i (X j)) = v j / v i := by
  obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simp [div_self hi]
  · simp [dehomogenizeVec]

/-- **The chart `i` sends the point of `v` into `U j` exactly when `vⱼ ≠ 0`.**
@isnad1 id=iff.1h7v.s9.b406bd8bc0e7 from=translated src=- shape=749f6a6c vocab=df516ad9
-/
lemma chart_base_evalPoint_mem_U_iff (i j : Fin (n + 1)) (v : Fin (n + 1) → K) (hi : v i ≠ 0) :
    (chart (R := R) i).base (evalPoint φ (dehomogenizeVec i v)) ∈ U n R j ↔ v j ≠ 0 := by
  change evalPoint φ (dehomogenizeVec i v) ∈ chart i ⁻¹ᵁ U n R j ↔ _
  rw [chart_preimage_U]
  change dehomogenize R i (X j) ∉
      (show PrimeSpectrum (MvPolynomial (Fin n) R) from
        evalPoint φ (dehomogenizeVec i v)).asIdeal ↔ _
  rw [mem_evalPoint_asIdeal_iff, eval₂_dehomogenize_X φ i j v hi]
  simp [hi]

variable {φ}

/-- Evaluation at `v` on the degree-zero localisation `A_(x)`, for `x` not vanishing at `v`. -/
noncomputable def awayEval (v : Fin (n + 1) → K) (x : MvPolynomial (Fin (n + 1)) R)
    (hx : eval₂ φ v x ≠ 0) : Away 𝒜 x →+* K :=
  (Localization.awayLift (eval₂Hom φ v) x (by simpa using hx.isUnit)).comp
    (algebraMap (Away 𝒜 x) (Localization.Away x))

/-- The point of `Spec A_(x)` given by evaluation at `v`. -/
noncomputable def awayPoint (v : Fin (n + 1) → K) (x : MvPolynomial (Fin (n + 1)) R)
    (hx : eval₂ φ v x ≠ 0) : PrimeSpectrum (Away 𝒜 x) :=
  ⟨RingHom.ker (awayEval v x hx), RingHom.ker_isPrime _⟩

/--
@isnad1 id=eq.4h9v.s12.f823b7ec0f58 from=translated src=- shape=039175f0 vocab=38f0a841
-/
lemma awayEval_comp_awayMap (v : Fin (n + 1) → K) {f g x : MvPolynomial (Fin (n + 1)) R}
    {e : ℕ} (hg : g ∈ 𝒜 e) (hx : x = f * g) (hf : eval₂ φ v f ≠ 0)
    (hx' : eval₂ φ v x ≠ 0) :
    (awayEval v x hx').comp (awayMap 𝒜 hg hx) = awayEval v f hf := by
  have key : (Localization.awayLift (eval₂Hom φ v) x (by simpa using hx'.isUnit)).comp
      (Localization.awayLift (algebraMap _ (Localization.Away x)) f
        (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x))) =
      Localization.awayLift (eval₂Hom φ v) f (by simpa using hf.isUnit) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    ext b
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
  ext a
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, val_awayMap]
  exact congrArg (fun F : Localization.Away f →+* K ↦ F a.val) key

/--
@isnad1 id=eq.1h6v.s10.3a5c447cd271 from=translated src=- shape=27d4519d vocab=ca497047
-/
lemma awayEval_comp_toAwayX (v : Fin (n + 1) → K) (i : Fin (n + 1)) (hi : eval₂ φ v (X i) ≠ 0) :
    (awayEval v (X i) hi).comp (toAwayX R i) = eval₂Hom φ (dehomogenizeVec i v) := by
  have hi' : v i ≠ 0 := by simpa using hi
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun m ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, toAwayX_C, awayEval, awayXBase,
      HomogeneousLocalization.algebraMap_apply, coe_eval₂Hom, eval₂_C]
    change Localization.awayLift _ _ _ (Localization.mk _ 1) = _
    rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]
    simp [MvPolynomial.algebraMap_eq]
  · simp only [RingHom.coe_comp, Function.comp_apply, toAwayX_X, awayEval,
      HomogeneousLocalization.algebraMap_apply, val_awayXDiv, coe_eval₂Hom, eval₂_X]
    rw [Localization.awayLift_mk (v := (v i)⁻¹) (hv := by simp [hi'])]
    simp [dehomogenizeVec, div_eq_mul_inv]

/--
@isnad1 id=eq.1h6v.s11.a301cd9b237b from=translated src=- shape=856e0be8 vocab=913a1402
-/
lemma eval₂Hom_comp_fromAwayX (v : Fin (n + 1) → K) (i : Fin (n + 1))
    (hi : eval₂ φ v (X i) ≠ 0) :
    (eval₂Hom φ (dehomogenizeVec i v)).comp (fromAwayX R i) = awayEval v (X i) hi := by
  rw [← awayEval_comp_toAwayX v i hi]
  ext a
  simp

/-- The chart `i` at the point of `v` is the image of `awayPoint v (X i)` under `Proj.awayι`.
@isnad1 id=eq.1h6v.s13.6ab1e54073ed from=translated src=- shape=7e9ba295 vocab=49bb981c
-/
lemma chart_base_evalPoint (v : Fin (n + 1) → K) (i : Fin (n + 1)) (hi : eval₂ φ v (X i) ≠ 0) :
    (chart (R := R) i).base (evalPoint φ (dehomogenizeVec i v)) =
      (Proj.awayι 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos).base
        (awayPoint v (X i) hi) := by
  rw [chart, Scheme.Hom.comp_apply]
  congr 1
  refine PrimeSpectrum.ext ?_
  change Ideal.comap _ (RingHom.ker _) = RingHom.ker _
  rw [RingHom.comap_ker, ← eval₂Hom_comp_fromAwayX v i hi]
  congr 2
  ext a
  simp

variable (φ)

end AlgebraicGeometry.ProjectiveSpace
