import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.RingTheory.GradedRing.GradedTensorBaseChange
import Tengoku.Seed.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The extended Rees deformation: the ring-level construction

Let `A` be a commutative `R`-algebra with an internal grading `𝒜 : ℕ → Submodule R A`, `B` a
commutative `R`-algebra and `t : B` (the parameter `λ`). Write `𝒜₊ = ⊕_{j>0} 𝒜 j` (Mathlib
`HomogeneousIdeal.irrelevant`) for the irrelevant ideal, and

* `ReesAlgebra.irrPow 𝒜 p j := (𝒜₊)^p ⊓ 𝒜 j`: the `j`-th piece `I^{(p)}_j` of the `p`-th power of the
  irrelevant ideal. This is entirely ring-theoretic: `I^{(p)}` is a power of an ideal, no
  `Limits.image` is involved.
* `ReesAlgebra.lam t := 1 ⊗ₜ t : A ⊗[R] B`;
* `ReesAlgebra.reesPiece 𝒜 t j := ⨆ e : ℕ, λ^e · (I^{(j-e)}_j ⊗ B) ⊆ A ⊗[R] B`
  (`j - e` is truncated subtraction in `ℕ`; for `e ≥ j`, `I^{(0)}_j = 𝒜 j`, which gives
  `R_j ⊇ λ^{j} 𝒜 j · B`, so `R_j` is a `B`-submodule and `R_0 = 𝒜 0 ⊗ B`).

Main results:
* `ReesAlgebra.gradedMonoid`: `SetLike.GradedMonoid (reesPiece 𝒜 t)`, i.e. `1 ∈ R_0` and
  `R_j · R_k ⊆ R_{j+k}`. Closure under multiplication is
  `λ^e I^{(j-e)}_j · λ^f I^{(k-f)}_k ⊆ λ^{e+f} I^{(j+k-e-f)}_{j+k}`, by `Ideal.mul_mem_mul` +
  `pow_add` + `Ideal.pow_le_pow_right` (since `(j-e)+(k-f) ≥ (j+k)-(e+f)`).
* `ReesAlgebra.reesPiece_le_tensorGrading`: `R_j ⊆ (A ⊗ B)_j` (the `j`-th piece of the base change),
  the precise form of "`R_j ⊆ S_j[λ]`".
* `ReesAlgebra.map_mem_reesPiece`: functoriality along the tensor product map with change of base ring
  `GradedBaseChange.map φ ψ χ` (`ψ` grading-preserving, `χ t = t'` ⇒ `R_j` is preserved), needed for
  the restriction maps on the scheme side.

Since everything is at the ring level, powers of ideals are ideals, `⊓` is a submodule, and
multiplication is the ring multiplication, so the monoid laws come from `CommRing` and no obligation
is left in the data.

Sources: Stacks 052P (extended Rees algebra); §2 of the paper (the Rees deformation of the weighted
jet algebra).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace ReesAlgebra

/-! ## 1. The image of a submodule under the tensor product -/

section TensorSub

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The image of `M ⊗ B` in `A ⊗[R] B`. For `M = 𝒜 m` this is `GradedBaseChange.tensorGrading 𝒜 m`.-/
def tensorSub (M : Submodule R A) : Submodule R (A ⊗[R] B) := (M.subtype.rTensor B).range

/--
@isnad1 id=iff.0h5v.s11.c86dd7f9a40e from=translated src=- shape=3548d056 vocab=d43a91d8
-/
theorem mem_tensorSub {M : Submodule R A} {x : A ⊗[R] B} :
    x ∈ tensorSub (B := B) M ↔ ∃ y : M ⊗[R] B, (M.subtype.rTensor B) y = x := Iff.rfl

/--
@isnad1 id=eq.0h5v.s7.caadb84fabc5 from=translated src=- shape=3a3df9b7 vocab=e90fc8ab
-/
theorem tensorSub_eq_tensorGrading (𝒜 : ℕ → Submodule R A) (m : ℕ) :
    tensorSub (B := B) (𝒜 m) = GradedBaseChange.tensorGrading 𝒜 (B := B) m := rfl

/--
@isnad1 id=mem.1h6v.s9.3a0e4ec3f72a from=translated src=- shape=d88757f4 vocab=ecac8b25
-/
theorem tmul_mem_tensorSub {M : Submodule R A} {a : A} (ha : a ∈ M) (b : B) :
    a ⊗ₜ[R] b ∈ tensorSub (B := B) M :=
  ⟨(⟨a, ha⟩ : M) ⊗ₜ[R] b, by rw [LinearMap.rTensor_tmul]; rfl⟩

/--
@isnad1 id=le.1h5v.s9.82181ce10b70 from=translated src=- shape=b8e4b5d3 vocab=59e1bbcf
-/
theorem tensorSub_mono {M N : Submodule R A} (h : M ≤ N) :
    tensorSub (B := B) M ≤ tensorSub (B := B) N := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | tmul a b => rw [LinearMap.rTensor_tmul]; exact tmul_mem_tensorSub (h a.2) b

/-- Lifting a pointwise multiplicativity condition to `tensorSub`.
@isnad1 id=mem.3h8v.s11.01521d9e3e0f from=translated src=- shape=8bbfbd84 vocab=4210a3d6
-/
theorem tensorSub_mul {M N P : Submodule R A}
    (h : ∀ a ∈ M, ∀ b ∈ N, a * b ∈ P) {x y : A ⊗[R] B}
    (hx : x ∈ tensorSub (B := B) M) (hy : y ∈ tensorSub (B := B) N) :
    x * y ∈ tensorSub (B := B) P := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | add u₁ u₂ h₁ h₂ => rw [map_add, add_mul]; exact Submodule.add_mem _ h₁ h₂
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
    | add v₁ v₂ h₁ h₂ => rw [map_add, mul_add]; exact Submodule.add_mem _ h₁ h₂
    | tmul a' b' =>
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_tensorSub (h _ a.2 _ a'.2) _

end TensorSub

/-! ## 2. Graded pieces of the powers of the irrelevant ideal -/

section IrrPow

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The irrelevant ideal `𝒜₊ = ⊕_{j>0} 𝒜 j`.-/
def irrelevant : Ideal A := (HomogeneousIdeal.irrelevant 𝒜).toIdeal

/-- `I^{(p)}_j := (𝒜₊)^p ∩ 𝒜 j`.-/
def irrPow (p j : ℕ) : Submodule R A :=
  Submodule.restrictScalars R ((irrelevant 𝒜) ^ p) ⊓ 𝒜 j

/--
@isnad1 id=iff.0h6v.s8.f2cbf9ca75c1 from=translated src=- shape=f155014d vocab=b65b6ea2
-/
theorem mem_irrPow {p j : ℕ} {x : A} :
    x ∈ irrPow 𝒜 p j ↔ x ∈ (irrelevant 𝒜) ^ p ∧ x ∈ 𝒜 j := Iff.rfl

/--
@isnad1 id=le.0h5v.s7.d8caee90d9e2 from=translated src=- shape=51214c52 vocab=ac2f3242
-/
theorem irrPow_le (p j : ℕ) : irrPow 𝒜 p j ≤ 𝒜 j := fun _ hx => hx.2

/--
@isnad1 id=eq.0h4v.s6.0f58e1369c94 from=translated src=- shape=1be2e861 vocab=238090f2
-/
theorem irrPow_zero (j : ℕ) : irrPow 𝒜 0 j = 𝒜 j := by
  refine le_antisymm (irrPow_le 𝒜 0 j) fun x hx => ?_
  exact ⟨by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top, hx⟩

/--
@isnad1 id=le.1h6v.s7.fb2abeb98cb0 from=translated src=- shape=2db21d67 vocab=ac2f3242
-/
theorem irrPow_anti {p q j : ℕ} (h : q ≤ p) : irrPow 𝒜 p j ≤ irrPow 𝒜 q j :=
  fun _ hx => ⟨Ideal.pow_le_pow_right h hx.1, hx.2⟩

/--
@isnad1 id=mem.0h3v.s7.0fe7bdd50594 from=translated src=- shape=b12fcae1 vocab=95558292
-/
theorem one_mem_irrPow : (1 : A) ∈ irrPow 𝒜 0 0 := by
  rw [irrPow_zero]
  exact SetLike.one_mem_graded 𝒜

/--
@isnad1 id=mem.2h9v.s8.0864d19d0d47 from=translated src=- shape=64c9ed01 vocab=54b1fe81
-/
theorem irrPow_mul {p q j k : ℕ} {x y : A} (hx : x ∈ irrPow 𝒜 p j) (hy : y ∈ irrPow 𝒜 q k) :
    x * y ∈ irrPow 𝒜 (p + q) (j + k) :=
  ⟨by rw [pow_add]; exact Ideal.mul_mem_mul hx.1 hy.1,
    SetLike.mul_mem_graded hx.2 hy.2⟩

end IrrPow

/-! ## 3. The pieces of the extended Rees deformation -/

section Rees

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (t : B)

/-- `λ = 1 ⊗ t ∈ A ⊗[R] B`.-/
def lam : A ⊗[R] B := (1 : A) ⊗ₜ[R] t

/-- **The `j`-th piece of the extended Rees deformation** `R_j = Σ_e λ^e · (I^{(j-e)}_j ⊗ B)`.-/
def reesPiece (j : ℕ) : Submodule R (A ⊗[R] B) :=
  ⨆ e : ℕ, (tensorSub (B := B) (irrPow 𝒜 (j - e) j)).map
    (LinearMap.mulLeft R (lam (A := A) t ^ e))

/--
@isnad1 id=mem.1h8v.s10.c984f3848fd8 from=translated src=- shape=78c5d818 vocab=1d131a4d
-/
theorem mem_reesPiece_of {e j : ℕ} {x : A ⊗[R] B}
    (hx : x ∈ tensorSub (B := B) (irrPow 𝒜 (j - e) j)) :
    lam (A := A) t ^ e * x ∈ reesPiece 𝒜 t j :=
  Submodule.mem_iSup_of_mem e ⟨x, hx, rfl⟩

/--
@isnad1 id=mem.0h5v.s9.4520423780ce from=translated src=- shape=7da88033 vocab=39e1da69
-/
theorem one_mem_reesPiece : (1 : A ⊗[R] B) ∈ reesPiece 𝒜 t 0 := by
  have h : (1 : A ⊗[R] B) = lam (A := A) t ^ 0 * ((1 : A) ⊗ₜ[R] (1 : B)) := by
    rw [pow_zero, one_mul]; rfl
  rw [h]
  exact mem_reesPiece_of 𝒜 t (tmul_mem_tensorSub (one_mem_irrPow 𝒜) 1)

/--
@isnad1 id=mem.2h9v.s10.461233b4247e from=translated src=- shape=036cd579 vocab=202311dd
-/
theorem mul_mem_reesPiece {j k : ℕ} {x y : A ⊗[R] B}
    (hx : x ∈ reesPiece 𝒜 t j) (hy : y ∈ reesPiece 𝒜 t k) :
    x * y ∈ reesPiece 𝒜 t (j + k) := by
  refine Submodule.iSup_induction (motive := fun z => z * y ∈ reesPiece 𝒜 t (j + k)) _ hx ?_ ?_ ?_
  · rintro e _ ⟨u, hu, rfl⟩
    refine Submodule.iSup_induction
      (motive := fun z => lam (A := A) t ^ e * u * z ∈ reesPiece 𝒜 t (j + k)) _ hy ?_ ?_ ?_
    · rintro f _ ⟨v, hv, rfl⟩
      have key : lam (A := A) t ^ e * u * (lam (A := A) t ^ f * v) =
            lam (A := A) t ^ (e + f) * (u * v) := by
        rw [pow_add]; ring
      show lam (A := A) t ^ e * u * (lam (A := A) t ^ f * v) ∈ _
      rw [key]
      refine mem_reesPiece_of 𝒜 t (tensorSub_mul ?_ hu hv)
      intro a ha b hb
      refine irrPow_anti 𝒜 (by omega) (irrPow_mul 𝒜 ha hb)
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb

/--
@isnad1 id=eq.0h5v.s8.9dea1fbf35c5 from=translated src=- shape=18165f96 vocab=feb74531
-/
theorem lam_pow (e : ℕ) : lam (A := A) t ^ e = (1 : A) ⊗ₜ[R] (t ^ e) := by
  show (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) t) ^ e = _
  rw [← map_pow]
  rfl

/--
@isnad1 id=mem.0h6v.s9.53df48645485 from=translated src=- shape=beca8221 vocab=c522103f
-/
theorem lam_pow_mem (e : ℕ) : lam (A := A) t ^ e ∈ tensorSub (B := B) (𝒜 0) := by
  rw [lam_pow]
  exact tmul_mem_tensorSub (SetLike.one_mem_graded 𝒜) (t ^ e)

/-- `R_j ⊆ (A ⊗ B)_j`: the `j`-th Rees piece lies in the `j`-th piece of the base change (i.e.
"`R_j ⊆ S_j[λ]`").
@isnad1 id=le.0h6v.s9.97e93f3a6642 from=translated src=- shape=867e243c vocab=d674c04a
-/
theorem reesPiece_le_tensorGrading (j : ℕ) :
    reesPiece 𝒜 t j ≤ GradedBaseChange.tensorGrading 𝒜 (B := B) j := by
  intro x hx
  show x ∈ tensorSub (B := B) (𝒜 j)
  refine Submodule.iSup_induction (motive := fun z => z ∈ tensorSub (B := B) (𝒜 j)) _ hx ?_ ?_ ?_
  · rintro e _ ⟨u, hu, rfl⟩
    show lam (A := A) t ^ e * u ∈ _
    refine tensorSub_mul ?_ (lam_pow_mem 𝒜 t e) (tensorSub_mono (irrPow_le 𝒜 _ j) hu)
    intro a ha b hb
    have h := SetLike.mul_mem_graded (A := 𝒜) ha hb
    rwa [zero_add] at h
  · exact Submodule.zero_mem _
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

end Rees

/-! ## 4. Functoriality along tensor product maps with change of base ring -/

section Map

variable {R R' A A' B B' : Type*}
  [CommRing R] [CommRing R'] [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (𝒜' : ℕ → Submodule R' A') [GradedAlgebra 𝒜']
  (φ : R →+* R') (ψ : A →+* A') (χ : B →+* B')
  (hψ : ∀ r : R, ψ (algebraMap R A r) = algebraMap R' A' (φ r))
  (hχ : ∀ r : R, χ (algebraMap R B r) = algebraMap R' B' (φ r))

/-- A grading-preserving ring map sends `tensorSub M` into `tensorSub M'`.
@isnad1 id=mem.4h12v.s11.cc063af53b53 from=translated src=- shape=9cd7647e vocab=a4cd2bda
-/
theorem map_mem_tensorSub {M : Submodule R A} {M' : Submodule R' A'}
    (h : ∀ a ∈ M, ψ a ∈ M') {x : A ⊗[R] B} (hx : x ∈ tensorSub (B := B) M) :
    GradedBaseChange.map φ ψ χ hψ hχ x ∈ tensorSub (B := B') M' := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add u v hu hv => rw [map_add, map_add]; exact Submodule.add_mem _ hu hv
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, GradedBaseChange.map_tmul]
    exact tmul_mem_tensorSub (h _ a.2) _

variable (hgr : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ψ a ∈ 𝒜' m)

include hgr in
/-- Preserving the grading ⇒ preserving the irrelevant ideal.
@isnad1 id=mem.2h8v.s9.ac3ae5a09235 from=translated src=- shape=cc586de6 vocab=d33517b2
-/
theorem map_mem_irrelevant {x : A} (hx : x ∈ irrelevant 𝒜) : ψ x ∈ irrelevant 𝒜' := by
  have hle : irrelevant 𝒜 ≤ Ideal.comap ψ (irrelevant 𝒜') := by
    refine (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr fun i hi a ha => ?_
    exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜' hi (hgr i a ha)
  exact hle hx

include hgr in
/-- Preserving the grading ⇒ preserving the powers of the irrelevant ideal.
@isnad1 id=mem.2h9v.s9.1afdd0b52906 from=translated src=- shape=158433c1 vocab=606bff81
-/
theorem map_mem_irrelevant_pow {p : ℕ} {x : A} (hx : x ∈ (irrelevant 𝒜) ^ p) :
    ψ x ∈ (irrelevant 𝒜') ^ p := by
  have hle0 : irrelevant 𝒜 ≤ Ideal.comap ψ (irrelevant 𝒜') := by
    refine (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr fun i hi a ha => ?_
    exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜' hi (hgr i a ha)
  have hle : (irrelevant 𝒜) ^ p ≤ Ideal.comap ψ ((irrelevant 𝒜') ^ p) :=
    le_trans (pow_le_pow_left' hle0 p) (Ideal.le_comap_pow _ p)
  exact hle hx

include hgr in
/--
@isnad1 id=mem.2h10v.s9.00f7a68aedd8 from=translated src=- shape=46a85642 vocab=92d436c9
-/
theorem map_mem_irrPow {p j : ℕ} {x : A} (hx : x ∈ irrPow 𝒜 p j) : ψ x ∈ irrPow 𝒜' p j :=
  ⟨map_mem_irrelevant_pow 𝒜 𝒜' ψ hgr hx.1, hgr j x hx.2⟩

include hgr in
/-- **Functoriality of the Rees pieces**: if `ψ` preserves the grading and `χ t = t'`, the base-change
map sends `R_j` into `R'_j`.
@isnad1 id=mem.5h15v.s11.3f9a45d943b9 from=translated src=- shape=a95c0a1f vocab=929d05ed
-/
theorem map_mem_reesPiece {t : B} {t' : B'} (ht : χ t = t') {j : ℕ} {x : A ⊗[R] B}
    (hx : x ∈ reesPiece 𝒜 t j) :
    GradedBaseChange.map φ ψ χ hψ hχ x ∈ reesPiece 𝒜' t' j := by
  have hlam : GradedBaseChange.map φ ψ χ hψ hχ (lam (A := A) t) = lam (A := A') t' := by
    show GradedBaseChange.map φ ψ χ hψ hχ ((1 : A) ⊗ₜ[R] t) = _
    rw [GradedBaseChange.map_tmul, map_one, ht]; rfl
  refine Submodule.iSup_induction
    (motive := fun z => GradedBaseChange.map φ ψ χ hψ hχ z ∈ reesPiece 𝒜' t' j) _ hx ?_ ?_ ?_
  · rintro e _ ⟨u, hu, rfl⟩
    show GradedBaseChange.map φ ψ χ hψ hχ (lam (A := A) t ^ e * u) ∈ _
    rw [map_mul, map_pow, hlam]
    exact mem_reesPiece_of 𝒜' t'
      (map_mem_tensorSub φ ψ χ hψ hχ (fun a ha => map_mem_irrPow 𝒜 𝒜' ψ hgr ha) hu)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

end Map

end ReesAlgebra

end
