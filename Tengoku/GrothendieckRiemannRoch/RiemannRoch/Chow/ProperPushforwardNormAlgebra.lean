/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.Length
import Tengoku.Seed.RingTheory.LocalRing.Length
import Tengoku.Seed.LinearAlgebra.Matrix.Transvection
import Tengoku.Seed.RingTheory.OrderOfVanishing.Noetherian
import Tengoku.Seed.LinearAlgebra.Quotient.Pi
import Tengoku.Seed.RingTheory.Norm.Basic
import Tengoku.Seed.RingTheory.Spectrum.Prime.Noetherian
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization
import Tengoku.Seed.RingTheory.Localization.Finiteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fulton's Appendix A.2/A.3: orders of norms over one-dimensional local domains

Commutative-algebra core of the norm formula for proper pushforward of principal divisors
(Fulton, *Intersection theory*, Prop. 1.4(b) and Example A.3.1).

* `ecoker_eq_ord_det` (Fulton A.2, free case): over a Noetherian domain `A` of dimension `≤ 1`,
  `ℓ_A(Aⁿ / M Aⁿ) = ord_A (det M)` for every matrix `M` with `det M ≠ 0`.  The length of the
  cokernel is extended to `GL_n(Frac A)`, and checked on diagonal matrices and transvections.
* `length_quot_eq_ordFrac_norm` (Fulton A.3): for a finite `A`-algebra `B` inside a finite
  extension `L` of `K = Frac A`, spanning `L`, `ℓ_A(B / b B) = ord_A (N_{L/K} b)`.
* `krullDimLE_one_of_finite` (light Krull–Akizuki): a domain between `A` and a finite extension
  of `Frac A` has dimension `≤ 1`.
* `length_eq_sum_localizations`: Chinese remainder theorem for lengths of Artinian quotients.
* `local_formula`: for a finite extension `R → S` of domains, a height-one prime `p` of `R`, its
  localization `A = R_p` and the localizations `D_t = S_{Q_t}` at the primes over `p`,
  `ord_A (N b) = Σ_t ℓ_A (D_t / b)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module

namespace RiemannRoch.ProperPushforwardNorm

section Coker

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- Cokernel lengths add along a composition `f ∘ g` with `f` injective:
`0 → M/gM → M/fgM → M/fM → 0`.-/
theorem length_quot_range_comp (f g : M →ₗ[A] M) (hf : Function.Injective f) :
    Module.length A (M ⧸ LinearMap.range (f ∘ₗ g)) =
      Module.length A (M ⧸ LinearMap.range g) + Module.length A (M ⧸ LinearMap.range f) := by
  have h1 : LinearMap.range g ≤ (LinearMap.range (f ∘ₗ g)).comap f := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have h2 : LinearMap.range (f ∘ₗ g) ≤ LinearMap.range f := LinearMap.range_comp_le_range g f
  refine Module.length_eq_add_of_exact (Submodule.mapQ _ _ f h1) (Submodule.factor h2) ?_
    (Submodule.factor_surjective h2) ?_
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy⟩ := hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨y, hf (by simpa using hy)⟩
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro hx
        have hx' : Submodule.Quotient.mk (p := LinearMap.range f) x = 0 := by
          rw [← hx]; exact (Submodule.factor_mk h2 x).symm
        rw [Submodule.Quotient.mk_eq_zero] at hx'
        obtain ⟨w, rfl⟩ := hx'
        exact ⟨Submodule.Quotient.mk w, rfl⟩
      · rintro ⟨w, hw⟩
        induction w using Submodule.Quotient.induction_on with
        | H w =>
          rw [← hw, Submodule.mapQ_apply]
          have := Submodule.factor_mk h2 (f w)
          simp only [Submodule.mkQ_apply] at this
          rw [this, Submodule.Quotient.mk_eq_zero]
          exact ⟨w, rfl⟩

end Coker

section Matrix

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Length of the cokernel of a square matrix.-/
def ecoker (M : Matrix ι ι A) : ℕ∞ :=
  Module.length A ((ι → A) ⧸ LinearMap.range M.mulVecLin)

theorem mulVecLin_injective_of_det_ne_zero [IsDomain A] {M : Matrix ι ι A} (h : M.det ≠ 0) :
    Function.Injective M.mulVecLin := by
  intro v w hvw
  have hvw' : M.mulVec v = M.mulVec w := hvw
  have := congrArg (fun u ↦ M.adjugate *ᵥ u) hvw'
  simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec] at this
  exact smul_right_injective _ h this

theorem ecoker_mul [IsDomain A] (M N : Matrix ι ι A) (hM : M.det ≠ 0) :
    ecoker (M * N) = ecoker N + ecoker M := by
  unfold ecoker
  rw [Matrix.mulVecLin_mul]
  exact length_quot_range_comp _ _ (mulVecLin_injective_of_det_ne_zero hM)

theorem range_mulVecLin_diagonal (d : ι → A) :
    LinearMap.range (diagonal d).mulVecLin =
      Submodule.pi Set.univ (fun i ↦ (Ideal.span {d i} : Submodule A A)) := by
  ext v
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ,
    true_implies]
  constructor
  · rintro ⟨w, rfl⟩ i
    rw [mulVec_diagonal]
    exact Ideal.mem_span_singleton'.mpr ⟨w i, mul_comm _ _⟩
  · intro hv
    choose w hw using fun i ↦ Ideal.mem_span_singleton'.mp (hv i)
    refine ⟨w, funext fun i ↦ ?_⟩
    rw [mulVec_diagonal, mul_comm]
    exact hw i

theorem ecoker_diagonal (d : ι → A) : ecoker (diagonal d) = ∑ i, Ring.ord A (d i) := by
  unfold ecoker
  rw [range_mulVecLin_diagonal,
    LinearEquiv.length_eq (Submodule.quotientPi (R := A) (Ms := fun _ : ι ↦ A)
      (fun i ↦ (Ideal.span {d i} : Submodule A A))),
    Module.length_pi_of_fintype]
  rfl

theorem ecoker_eq_zero_of_mul_eq_one {M N : Matrix ι ι A} (h : M * N = 1) : ecoker M = 0 := by
  unfold ecoker
  have : LinearMap.range M.mulVecLin = ⊤ := by
    rw [eq_top_iff]
    intro v _
    refine ⟨N *ᵥ v, ?_⟩
    simp [mulVec_mulVec, h]
  rw [this]
  exact Module.length_eq_zero

variable [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem ecoker_ne_top {M : Matrix ι ι A} (h : M.det ≠ 0) : ecoker M ≠ ⊤ := by
  have hmul : M * M.adjugate = diagonal (fun _ ↦ M.det) := by
    rw [mul_adjugate, smul_one_eq_diagonal]
  have key := ecoker_mul M M.adjugate h
  rw [hmul, ecoker_diagonal] at key
  have hfin : (∑ _i : ι, Ring.ord A M.det) ≠ ⊤ := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _)
      (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr h))
  intro htop
  rw [htop, add_top] at key
  exact hfin key

end Matrix

section Good

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cokernel length of an integral matrix, as an element of `ℤᵐ⁰`.-/
def ordE (M : Matrix ι ι A) : WithZero (Multiplicative ℤ) :=
  ((Multiplicative.ofAdd ((ecoker M).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

theorem ordE_ne_zero (M : Matrix ι ι A) : ordE M ≠ 0 := WithZero.coe_ne_zero

theorem ordE_mul (M N : Matrix ι ι A) (hM : M.det ≠ 0) (hN : N.det ≠ 0) :
    ordE (M * N) = ordE M * ordE N := by
  unfold ordE
  rw [ecoker_mul M N hM, ENat.toNat_add (ecoker_ne_top hN) (ecoker_ne_top hM)]
  push_cast
  rw [ofAdd_add, WithZero.coe_mul, mul_comm]

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem ordMonoidWithZeroHom_eq_ofAdd_toNat [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {a : A} (ha : a ≠ 0) :
    Ring.ordMonoidWithZeroHom A a =
      ((Multiplicative.ofAdd ((Ring.ord A a).toNat : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) :=
  Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr ha))).symm

theorem ordE_diagonal (d : ι → A) (hd : ∀ i, d i ≠ 0) :
    ordE (diagonal d) = ∏ i, Ring.ordFrac A (algebraMap A K (d i)) := by
  unfold ordE
  rw [ecoker_diagonal]
  simp_rw [Ring.ordFrac_eq_ord A (hd _), ordMonoidWithZeroHom_eq_ofAdd_toNat (hd _)]
  have hsum : (∑ i, Ring.ord A (d i)).toNat = ∑ i, (Ring.ord A (d i)).toNat := by
    rw [← ENat.toNat_natCast (∑ i, (Ring.ord A (d i)).toNat), Nat.cast_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦
      (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr (hd i)))).symm
  rw [hsum]
  push_cast
  rw [ofAdd_sum]
  exact map_prod (WithZero.coeMonoidHom : Multiplicative ℤ →* WithZero (Multiplicative ℤ)) _ _

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsFractionRing A K] in
theorem det_map_algebraMap (M : Matrix ι ι A) :
    (M.map (algebraMap A K)).det = algebraMap A K M.det := by
  rw [RingHom.map_det]; rfl

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem det_map_ne_zero {M : Matrix ι ι A} (h : M.det ≠ 0) :
    (M.map (algebraMap A K)).det ≠ 0 := by
  rw [det_map_algebraMap]
  exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr h

/-- `(d, M)` represents the rational matrix `N`: `M = d • N` with `d ≠ 0`.-/
def IsRep (N : Matrix ι ι K) (d : A) (M : Matrix ι ι A) : Prop :=
  d ≠ 0 ∧ ∀ i j, algebraMap A K (M i j) = algebraMap A K d * N i j

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem exists_rep (N : Matrix ι ι K) : ∃ d M, IsRep (A := A) N d M := by
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors A) (fun p : ι × ι ↦ N p.1 p.2)
  choose a ha using fun p ↦ hint p
  refine ⟨b, Matrix.of fun i j ↦ a (i, j), nonZeroDivisors.ne_zero hb, fun i j ↦ ?_⟩
  simp only [Matrix.of_apply]
  rw [ha (i, j)]
  simp [Algebra.smul_def]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem IsRep.det_ne_zero {N : Matrix ι ι K} {d : A} {M : Matrix ι ι A} (h : IsRep N d M)
    (hN : N.det ≠ 0) : M.det ≠ 0 := by
  intro h0
  have hmap : M.map (algebraMap A K) = algebraMap A K d • N := by
    ext i j; simp [h.2 i j]
  have := RingHom.map_det (algebraMap A K) M
  rw [h0, map_zero] at this
  change (0 : K) = (M.map (algebraMap A K)).det at this
  rw [hmap, det_smul] at this
  have hd : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr h.1
  exact (mul_ne_zero (pow_ne_zero _ hd) hN) this.symm

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem det_map_eq {N : Matrix ι ι K} {d : A} {M : Matrix ι ι A} (h : IsRep N d M) :
    algebraMap A K M.det = algebraMap A K d ^ Fintype.card ι * N.det := by
  have hmap : M.map (algebraMap A K) = algebraMap A K d • N := by
    ext i j; simp [h.2 i j]
  rw [RingHom.map_det]
  change (M.map (algebraMap A K)).det = _
  rw [hmap, det_smul]

theorem ordE_smul (c : A) (hc : c ≠ 0) (M : Matrix ι ι A) (hM : M.det ≠ 0) :
    ordE (c • M) = Ring.ordFrac A (algebraMap A K c) ^ Fintype.card ι * ordE M := by
  rw [smul_eq_diagonal_mul, ordE_mul _ _ (by simp [det_diagonal, hc]) hM,
    ordE_diagonal (K := K) _ (fun _ ↦ hc), Finset.prod_const, Finset.card_univ]

/-- Well-definedness of the rational extension of `ordE`.-/
theorem rep_wd {N : Matrix ι ι K} (hN : N.det ≠ 0) {d d' : A} {M M' : Matrix ι ι A}
    (h : IsRep N d M) (h' : IsRep N d' M') :
    Ring.ordFrac A (algebraMap A K d') ^ Fintype.card ι * ordE M =
      Ring.ordFrac A (algebraMap A K d) ^ Fintype.card ι * ordE M' := by
  have heq : d' • M = d • M' := by
    ext i j
    apply IsFractionRing.injective A K
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h.2 i j, h'.2 i j]
    ring
  rw [← ordE_smul d' h'.1 M (h.det_ne_zero hN), ← ordE_smul d h.1 M' (h'.det_ne_zero hN), heq]

/-- The rational matrices for which `ordE` is `ord ∘ det`.-/
def Good (N : Matrix ι ι K) : Prop :=
  ∀ d M, IsRep N d M → ordE M = Ring.ordFrac A (algebraMap A K d) ^ Fintype.card ι *
    Ring.ordFrac A N.det

theorem good_of_exists {N : Matrix ι ι K} (hN : N.det ≠ 0) {d : A} {M : Matrix ι ι A}
    (h : IsRep N d M)
    (hM : ordE M = Ring.ordFrac A (algebraMap A K d) ^ Fintype.card ι * Ring.ordFrac A N.det) :
    Good (A := A) N := by
  intro d' M' h'
  have hw := rep_wd hN h h'
  rw [hM] at hw
  have hd : Ring.ordFrac A (algebraMap A K d) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero _).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr h.1))
  apply mul_left_cancel₀ hd
  rw [← hw]
  simp only [mul_comm, mul_assoc, mul_left_comm]

theorem good_mul {N₁ N₂ : Matrix ι ι K} (h₁ : N₁.det ≠ 0) (h₂ : N₂.det ≠ 0)
    (g₁ : Good (A := A) N₁) (g₂ : Good (A := A) N₂) : Good (A := A) (N₁ * N₂) := by
  obtain ⟨d₁, M₁, r₁⟩ := exists_rep (A := A) N₁
  obtain ⟨d₂, M₂, r₂⟩ := exists_rep (A := A) N₂
  have r : IsRep (N₁ * N₂) (d₁ * d₂) (M₁ * M₂) := by
    refine ⟨mul_ne_zero r₁.1 r₂.1, fun i j ↦ ?_⟩
    simp only [mul_apply, map_sum, map_mul, r₁.2, r₂.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  refine good_of_exists (by rw [det_mul]; exact mul_ne_zero h₁ h₂) r ?_
  rw [ordE_mul _ _ (r₁.det_ne_zero h₁) (r₂.det_ne_zero h₂), g₁ d₁ M₁ r₁, g₂ d₂ M₂ r₂, det_mul,
    map_mul, map_mul, map_mul, mul_pow]
  simp only [mul_comm, mul_assoc, mul_left_comm]

theorem good_diagonal (D : ι → K) (hD : (diagonal D).det ≠ 0) : Good (A := A) (diagonal D) := by
  have hD' : ∀ i, D i ≠ 0 := by
    intro i h0
    apply hD
    rw [det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors A) D
  choose a ha using hint
  have ha' : ∀ i, algebraMap A K (a i) = algebraMap A K b * D i := fun i ↦ by
    rw [ha i]; simp [Algebra.smul_def]
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0
  have ha0 : ∀ i, a i ≠ 0 := fun i h0 ↦ by
    have := ha' i
    rw [h0, map_zero] at this
    exact mul_ne_zero hbK (hD' i) this.symm
  have r : IsRep (diagonal D) b (diagonal a) := by
    refine ⟨hb0, fun i j ↦ ?_⟩
    by_cases hij : i = j
    · subst hij; simp [ha']
    · simp [diagonal_apply_ne _ hij]
  refine good_of_exists hD r ?_
  rw [ordE_diagonal (K := K) a ha0, det_diagonal, map_prod]
  simp_rw [ha', map_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem isRep_map (M : Matrix ι ι A) : IsRep (M.map (algebraMap A K)) 1 M :=
  ⟨one_ne_zero, fun i j ↦ by simp⟩

theorem good_map_transvection (i j : ι) (hij : i ≠ j) (α : A) :
    Good (A := A) ((transvection i j α).map (algebraMap A K)) := by
  have hdet : (transvection i j α).det = 1 := det_transvection_of_ne i j hij α
  have hdetK : ((transvection i j α).map (algebraMap A K)).det = 1 := by
    rw [det_map_algebraMap, hdet, map_one]
  refine good_of_exists (by rw [hdetK]; exact one_ne_zero) (isRep_map _) ?_
  simp only [hdetK, map_one, one_pow, one_mul]
  unfold ordE
  rw [ecoker_eq_zero_of_mul_eq_one (N := transvection i j (-α))
    (by rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero])]
  rfl

theorem good_cancel (M₀ : Matrix ι ι A) (h₀ : M₀.det ≠ 0) {T : Matrix ι ι K} (hT : T.det ≠ 0)
    (g₀ : Good (A := A) (M₀.map (algebraMap A K)))
    (g : Good (A := A) (M₀.map (algebraMap A K) * T)) : Good (A := A) T := by
  obtain ⟨d, M, r⟩ := exists_rep (A := A) T
  have h₀K : (M₀.map (algebraMap A K)).det ≠ 0 := by
    exact det_map_ne_zero h₀
  have r' : IsRep (M₀.map (algebraMap A K) * T) d (M₀ * M) := by
    refine ⟨r.1, fun i j ↦ ?_⟩
    simp only [mul_apply, map_sum, map_mul, r.2, Finset.mul_sum, map_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have e1 := g d (M₀ * M) r'
  have e0 := g₀ 1 M₀ (isRep_map M₀)
  simp only [map_one, one_pow, one_mul] at e0
  rw [ordE_mul _ _ h₀ (r.det_ne_zero hT), e0, det_mul, map_mul] at e1
  refine good_of_exists hT r ?_
  have hne : Ring.ordFrac A (M₀.map (algebraMap A K)).det ≠ 0 := (map_ne_zero _).mpr h₀K
  apply mul_left_cancel₀ hne
  rw [e1]
  simp only [mul_comm, mul_assoc, mul_left_comm]

theorem good_transvection (t : TransvectionStruct ι K) : Good (A := A) t.toMatrix := by
  obtain ⟨α, β, hβ, hc⟩ := IsFractionRing.div_surjective (A := A) t.c
  have hβ0 : β ≠ 0 := nonZeroDivisors.ne_zero hβ
  have hβK : algebraMap A K β ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hβ0
  set δ : ι → A := fun k ↦ if k = t.i then β else 1 with hδ
  have hδ0 : ∀ k, δ k ≠ 0 := fun k ↦ by
    simp only [hδ]; split_ifs
    · exact hβ0
    · exact one_ne_zero
  have hdet0 : (diagonal δ).det ≠ 0 := by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ hδ0 k
  have hmapdiag : (diagonal δ).map (algebraMap A K) = diagonal (fun k ↦ algebraMap A K (δ k)) :=
    diagonal_map (map_zero _)
  have hdetK : (diagonal fun k ↦ algebraMap A K (δ k)).det ≠ 0 := by
    rw [← hmapdiag]; exact det_map_ne_zero hdet0
  have hTdet : t.toMatrix.det = 1 := by
    rw [TransvectionStruct.toMatrix]; exact det_transvection_of_ne _ _ t.hij _
  have key : (diagonal δ).map (algebraMap A K) * t.toMatrix =
      (transvection t.i t.j α).map (algebraMap A K) * (diagonal δ).map (algebraMap A K) := by
    rw [hmapdiag]
    ext k l
    rw [diagonal_mul, mul_diagonal]
    simp only [TransvectionStruct.toMatrix, transvection, Matrix.add_apply, one_apply, map_apply,
      Matrix.single_apply, hδ]
    obtain ⟨i, j, hij, c⟩ := t
    simp only at hc ⊢
    have hji : j ≠ i := hij.symm
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = j
      · subst hl
        simp [hij, hji, ← hc]
        field_simp
      · by_cases hkl : k = l
        · subst hkl; simp [hji]
        · simp [hkl, Ne.symm hl]
    · have hk' : i ≠ k := Ne.symm hk
      by_cases hkl : k = l
      · subst hkl; simp [hk, hk']
      · simp [hk, hkl, hk']
  have g₀ : Good (A := A) ((diagonal δ).map (algebraMap A K)) := by
    rw [hmapdiag]; exact good_diagonal _ hdetK
  have hTK : ((transvection t.i t.j α).map (algebraMap A K)).det ≠ 0 := by
    rw [det_map_algebraMap, det_transvection_of_ne _ _ t.hij, map_one]; exact one_ne_zero
  refine good_cancel (diagonal δ) hdet0 (by rw [hTdet]; exact one_ne_zero) g₀ ?_
  rw [key]
  refine good_mul hTK ?_ (good_map_transvection _ _ t.hij α) g₀
  rw [hmapdiag]; exact hdetK

theorem good_of_det_ne_zero (N : Matrix ι ι K) (hN : N.det ≠ 0) : Good (A := A) N :=
  diagonal_transvection_induction_of_det_ne_zero (fun N ↦ Good (A := A) N) N hN
    (fun D hD ↦ good_diagonal D hD) (fun t ↦ good_transvection t)
    (fun _ _ h₁ h₂ g₁ g₂ ↦ good_mul h₁ h₂ g₁ g₂)

end Good

section Main

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fulton A.2 (free case)**: over a one-dimensional Noetherian local domain — in fact over
any one-dimensional Noetherian domain — the cokernel of a square matrix with nonzero determinant
has length `ord (det M)`.-/
theorem ecoker_eq_ord_det (M : Matrix ι ι A) (h : M.det ≠ 0) : ecoker M = Ring.ord A M.det := by
  have g := good_of_det_ne_zero (A := A) (M.map (algebraMap A (FractionRing A)))
    (det_map_ne_zero h)
  have e := g 1 M (isRep_map M)
  rw [map_one, map_one, one_pow, one_mul, det_map_algebraMap,
    Ring.ordFrac_eq_ord A h, ordMonoidWithZeroHom_eq_ofAdd_toNat h] at e
  unfold ordE at e
  have e' : (ecoker M).toNat = (Ring.ord A M.det).toNat := by
    have := WithZero.coe_injective e
    simpa using this
  rw [← ENat.natCast_toNat (ecoker_ne_top h),
    ← ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr h)), e']

end Main

section Lattice

variable {A : Type*} [CommRing A]

theorem enat_cancel {a b c : ℕ∞} (hc : c ≠ ⊤) (h : a + c = b + c) : a = b := by
  lift c to ℕ using hc
  exact (ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top c)) h

/-- Cokernel lengths add along a composition `f ∘ g` with `f` injective (general form).-/
theorem length_quot_range_comp' {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) (g : M →ₗ[A] N)
    (hf : Function.Injective f) :
    Module.length A (P ⧸ LinearMap.range (f ∘ₗ g)) =
      Module.length A (N ⧸ LinearMap.range g) + Module.length A (P ⧸ LinearMap.range f) := by
  have h1 : LinearMap.range g ≤ (LinearMap.range (f ∘ₗ g)).comap f := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have h2 : LinearMap.range (f ∘ₗ g) ≤ LinearMap.range f := LinearMap.range_comp_le_range g f
  refine Module.length_eq_add_of_exact (Submodule.mapQ _ _ f h1) (Submodule.factor h2) ?_
    (Submodule.factor_surjective h2) ?_
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy⟩ := hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨y, hf (by simpa using hy)⟩
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro hx
        have hx' : Submodule.Quotient.mk (p := LinearMap.range f) x = 0 := by
          rw [← hx]; exact (Submodule.factor_mk h2 x).symm
        rw [Submodule.Quotient.mk_eq_zero] at hx'
        obtain ⟨w, rfl⟩ := hx'
        exact ⟨Submodule.Quotient.mk w, rfl⟩
      · rintro ⟨w, hw⟩
        induction w using Submodule.Quotient.induction_on with
        | H w =>
          rw [← hw, Submodule.mapQ_apply]
          have := Submodule.factor_mk h2 (f w)
          simp only [Submodule.mkQ_apply] at this
          rw [this, Submodule.Quotient.mk_eq_zero]
          exact ⟨w, rfl⟩

variable [IsDomain A] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : Type*} [AddCommGroup B] [Module A B]

/-- The lattice comparison: if an injective endomorphism `φ` of `B` restricts, along an
injective `Φ : Aⁿ → B` with finite-length cokernel, to the matrix `M`, then the cokernel of `φ`
has the same length as the cokernel of `M`.-/
theorem length_coker_eq_ecoker (Φ : (ι → A) →ₗ[A] B) (hΦ : Function.Injective Φ)
    (φ : B →ₗ[A] B) (hφ : Function.Injective φ) (M : Matrix ι ι A)
    (hcomm : φ ∘ₗ Φ = Φ ∘ₗ M.mulVecLin) (hfin : Module.length A (B ⧸ LinearMap.range Φ) ≠ ⊤) :
    Module.length A (B ⧸ LinearMap.range φ) = ecoker M := by
  have e1 := length_quot_range_comp' φ Φ hφ
  have e2 := length_quot_range_comp' Φ M.mulVecLin hΦ
  rw [hcomm, e2] at e1
  exact enat_cancel hfin ((add_comm _ _).trans e1.symm)

end Lattice

section NormLength

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]
  {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra B L] [IsScalarTower A B L]

/-- Scalar multiplication cokernels of a finite module have finite length.-/
theorem length_quot_smul_ne_top (d : A) (hd : d ≠ 0) :
    Module.length A (B ⧸ LinearMap.range (d • (LinearMap.id : B →ₗ[A] B))) ≠ ⊤ := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' A B
  have hle : LinearMap.range (d • (LinearMap.id : (Fin m → A) →ₗ[A] (Fin m → A))) ≤
      (LinearMap.range (d • (LinearMap.id : B →ₗ[A] B))).comap f := by
    rintro _ ⟨v, rfl⟩
    exact ⟨f v, by simp⟩
  have hsurj : Function.Surjective (Submodule.mapQ _ _ f hle) := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨v, rfl⟩ := hf x
      exact ⟨Submodule.Quotient.mk v, rfl⟩
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hsurj)
  have : d • (LinearMap.id : (Fin m → A) →ₗ[A] (Fin m → A)) =
      (Matrix.diagonal (fun _ : Fin m ↦ d)).mulVecLin := by
    ext v i
    simp [Matrix.mulVec_diagonal]
  rw [this]
  exact ecoker_ne_top (by
    rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hd)

omit [Module.Finite A B] in
theorem range_mulLeft_eq (b : B) :
    LinearMap.range (LinearMap.mulLeft A b) = (Ideal.span {b}).restrictScalars A := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩

omit [Module.Finite A B] in
theorem length_quot_span_eq (b : B) :
    Module.length A (B ⧸ Ideal.span {b}) =
      Module.length A (B ⧸ LinearMap.range (LinearMap.mulLeft A b)) := by
  rw [range_mulLeft_eq]
  exact (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).length_eq.symm

variable (hinj : Function.Injective (algebraMap B L))
  (hspan : Submodule.span K (Set.range (algebraMap B L)) = ⊤)
include hinj

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsFractionRing A K]
  [FiniteDimensional K L] [IsScalarTower A K L] [Module.Finite A B] [IsScalarTower A B L] in
theorem mulLeft_injective {x : B} (hx : x ≠ 0) :
    Function.Injective (LinearMap.mulLeft A x) := by
  intro y z hyz
  apply hinj
  have hx' : algebraMap B L x ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx
  have := congrArg (algebraMap B L) hyz
  simp only [LinearMap.mulLeft_apply, map_mul] at this
  exact mul_left_cancel₀ hx' this

include hspan

/-- **Fulton A.2/A.3 (lattice form)**: for a finite `A`-algebra `B ⊆ L` spanning `L` over
`K = Frac A` (`A` a one-dimensional Noetherian domain), `ℓ_A(B/bB) = ord_A (N_{L/K} b)`.-/
theorem length_quot_eq_ordFrac_norm (b : B) (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) ≠ ⊤ ∧
      Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
        ((Multiplicative.ofAdd ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  classical
  -- a `K`-basis of `L` consisting of elements of `B`
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range (algebraMap B L))
  have hs_top : ⊤ ≤ Submodule.span K (Set.range (Subtype.val : s → L)) := by
    rw [Subtype.range_coe, hs_span, hspan]
  haveI : Finite s := hs_li.finite
  haveI : Fintype s := Fintype.ofFinite s
  let e : Module.Basis s K L := Module.Basis.mk hs_li hs_top
  choose β hβ using fun x : s ↦ hs_sub x.2
  have he : ∀ i, e i = algebraMap B L (β i) := fun i ↦ by
    rw [Module.Basis.mk_apply, hβ i]
  -- the free lattice `Φ : Aˢ → B`
  let Φ : (s → A) →ₗ[A] B := Fintype.linearCombination A β
  have hΦL : ∀ w : s → A, algebraMap B L (Φ w) = ∑ i, algebraMap A K (w i) • e i := by
    intro w
    simp only [Φ, Fintype.linearCombination_apply, map_sum, he]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [algebraMap_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∑ i, algebraMap A K (w i) • e i = 0 := by rw [← hΦL, hw, map_zero]
    have := (Fintype.linearIndependent_iff.mp e.linearIndependent) _ h0
    funext i
    exact IsFractionRing.injective A K (by rw [this i, Pi.zero_apply, map_zero])
  -- every element of `B` has a nonzero multiple in the lattice
  have hmult : ∀ x : B, ∃ d : A, d ≠ 0 ∧ d • x ∈ LinearMap.range Φ := by
    intro x
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors A) (fun i ↦ e.repr (algebraMap B L x) i)
    choose a ha using hint
    refine ⟨d, nonZeroDivisors.ne_zero hd, a, hinj ?_⟩
    rw [hΦL, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B L,
      ← Algebra.smul_def]
    conv_rhs => rw [← e.sum_repr (algebraMap B L x)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ha i, ← smul_assoc]
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A B).FG)
  choose! dS hdS0 hdS using fun x (_ : x ∈ S) ↦ hmult x
  set d : A := ∏ x ∈ S, dS x with hd_def
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx ↦ hdS0 x hx
  have hdmem : ∀ y : B, d • y ∈ LinearMap.range Φ := by
    intro y
    have hy : y ∈ Submodule.span A (S : Set B) := by rw [hS]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [hd_def, ← Finset.prod_erase_mul S dS hx, mul_smul]
      exact Submodule.smul_mem _ _ (hdS x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  -- finiteness of the lattice cokernel
  have hfinΦ : Module.length A (B ⧸ LinearMap.range Φ) ≠ ⊤ := by
    have hle : LinearMap.range (d • (LinearMap.id : B →ₗ[A] B)) ≤ LinearMap.range Φ := by
      rintro _ ⟨y, rfl⟩; exact hdmem y
    exact ne_top_of_le_ne_top (length_quot_smul_ne_top d hd0)
      (Module.length_le_of_surjective _ (Submodule.factor_surjective hle))
  -- the key step for elements preserving the lattice
  have key : ∀ c : B, c ≠ 0 → (∀ j, c * β j ∈ LinearMap.range Φ) →
      Module.length A (B ⧸ LinearMap.range (LinearMap.mulLeft A c)) ≠ ⊤ ∧
      Ring.ordFrac A (Algebra.norm K (algebraMap B L c)) =
        ((Multiplicative.ofAdd
          ((Module.length A (B ⧸ LinearMap.range (LinearMap.mulLeft A c))).toNat : ℤ) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro c hc hcβ
    choose w hw using hcβ
    let Mc : Matrix s s A := Matrix.of fun i j ↦ w j i
    have hcomm : LinearMap.mulLeft A c ∘ₗ Φ = Φ ∘ₗ Mc.mulVecLin := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Matrix.mulVecLin_apply, Φ,
        Fintype.linearCombination_apply, Finset.mul_sum]
      have : ∀ j, c * (v j • β j) = v j • Φ (w j) := fun j ↦ by
        rw [mul_smul_comm, hw j]
      simp_rw [this, Φ, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_smul]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Mc, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    have hlen := length_coker_eq_ecoker Φ hΦ _ (mulLeft_injective hinj hc) Mc hcomm hfinΦ
    have hmat : Algebra.leftMulMatrix e (algebraMap B L c) = Mc.map (algebraMap A K) := by
      ext i j
      rw [Algebra.leftMulMatrix_eq_repr_mul, he j, ← map_mul, ← hw j, hΦL,
        Module.Basis.repr_sum_self]
      rfl
    have hdetMc : Mc.det ≠ 0 := by
      intro h0
      have hN : Algebra.norm K (algebraMap B L c) ≠ 0 := by
        rw [Algebra.norm_ne_zero_iff]
        exact (map_ne_zero_iff _ hinj).mpr hc
      rw [Algebra.norm_eq_matrix_det e, hmat, det_map_algebraMap, h0, map_zero] at hN
      exact hN rfl
    refine ⟨hlen ▸ ecoker_ne_top hdetMc, ?_⟩
    rw [Algebra.norm_eq_matrix_det e, hmat, det_map_algebraMap, Ring.ordFrac_eq_ord A hdetMc,
      ordMonoidWithZeroHom_eq_ofAdd_toNat hdetMc, hlen, ecoker_eq_ord_det Mc hdetMc]
  -- apply to `d` and to `d * b`
  have hdB : algebraMap A B d ≠ 0 := by
    intro h0
    have : algebraMap A L d = 0 := by rw [IsScalarTower.algebraMap_apply A B L, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply A K L] at this
    exact hd0 (IsFractionRing.injective A K ((map_eq_zero _).mp this |>.trans (map_zero _).symm))
  have hkd := key (algebraMap A B d) hdB (fun j ↦ by
    rw [← Algebra.smul_def]; exact hdmem _)
  have hcb : algebraMap A B d * b ≠ 0 := by
    intro h0
    have := congrArg (algebraMap B L) h0
    rw [map_mul, map_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact hdB ((map_eq_zero_iff _ hinj).mp h)
    · exact hb ((map_eq_zero_iff _ hinj).mp h)
  have hkc := key (algebraMap A B d * b) hcb (fun j ↦ by
    rw [mul_assoc, ← Algebra.smul_def]; exact hdmem _)
  have hsplit := length_quot_range_comp' (LinearMap.mulLeft A (algebraMap A B d))
    (LinearMap.mulLeft A b) (mulLeft_injective hinj hdB)
  rw [← LinearMap.mulLeft_mul] at hsplit
  have hfinb : Module.length A (B ⧸ LinearMap.range (LinearMap.mulLeft A b)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hsplit
    exact hkc.1 hsplit
  rw [length_quot_span_eq]
  refine ⟨hfinb, ?_⟩
  have hnorm : Algebra.norm K (algebraMap B L (algebraMap A B d * b)) =
      Algebra.norm K (algebraMap B L (algebraMap A B d)) * Algebra.norm K (algebraMap B L b) := by
    rw [map_mul, map_mul]
  have e2 := hkc.2
  rw [hnorm, map_mul, hkd.2, hsplit, ENat.toNat_add hfinb hkd.1] at e2
  push_cast at e2
  rw [ofAdd_add, WithZero.coe_mul, mul_comm] at e2
  exact mul_right_cancel₀ WithZero.coe_ne_zero e2

end NormLength

section SmulFinite

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {B : Type*} [AddCommGroup B] [Module A B] [Module.Finite A B]

/-- Scalar multiplication cokernels of a finite module have finite length.-/
theorem length_quot_smul_ne_top' (d : A) (hd : d ≠ 0) :
    Module.length A (B ⧸ LinearMap.range (d • (LinearMap.id : B →ₗ[A] B))) ≠ ⊤ := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' A B
  have hle : LinearMap.range (d • (LinearMap.id : (Fin m → A) →ₗ[A] (Fin m → A))) ≤
      (LinearMap.range (d • (LinearMap.id : B →ₗ[A] B))).comap f := by
    rintro _ ⟨v, rfl⟩
    exact ⟨f v, by simp⟩
  have hsurj : Function.Surjective (Submodule.mapQ _ _ f hle) := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨v, rfl⟩ := hf x
      exact ⟨Submodule.Quotient.mk v, rfl⟩
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hsurj)
  have : d • (LinearMap.id : (Fin m → A) →ₗ[A] (Fin m → A)) =
      (Matrix.diagonal (fun _ : Fin m ↦ d)).mulVecLin := by
    ext v i
    simp [Matrix.mulVec_diagonal]
  rw [this]
  exact ecoker_ne_top (by
    rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hd)

end SmulFinite

section KA

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- Lattice data: a family `γ` in a finite `A`-module `B ⊆ L` whose image is a `K`-basis of the
`K`-span of `B` gives an injective `Φ : Aˢ → B` with finite-length cokernel.-/
theorem lattice_data {B : Type*} [AddCommGroup B] [Module A B] [Module.Finite A B]
    (ι : B →ₗ[A] L) (hι : Function.Injective ι) {s : Type*} [Fintype s] (γ : s → B)
    (hli : LinearIndependent K (ι ∘ γ))
    (hmem : ∀ x, ι x ∈ Submodule.span K (Set.range (ι ∘ γ))) :
    Function.Injective (Fintype.linearCombination A γ) ∧
      Module.length A (B ⧸ LinearMap.range (Fintype.linearCombination A γ)) ≠ ⊤ := by
  classical
  set Φ := Fintype.linearCombination A γ with hΦdef
  have hΦL : ∀ w : s → A, ι (Φ w) = ∑ i, algebraMap A K (w i) • ι (γ i) := by
    intro w
    simp only [Φ, Fintype.linearCombination_apply, map_sum, map_smul, algebraMap_smul]
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∑ i, algebraMap A K (w i) • ι (γ i) = 0 := by
      rw [← hΦL, hw, map_zero]
    have := (Fintype.linearIndependent_iff.mp hli) _ h0
    funext i
    exact IsFractionRing.injective A K (by rw [this i, Pi.zero_apply, map_zero])
  refine ⟨hΦ, ?_⟩
  have hmult : ∀ x : B, ∃ d : A, d ≠ 0 ∧ d • x ∈ LinearMap.range Φ := by
    intro x
    let bs := Module.Basis.span hli
    let c := bs.repr ⟨ι x, hmem x⟩
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors A) (fun i ↦ c i)
    choose a ha using hint
    refine ⟨d, nonZeroDivisors.ne_zero hd, a, hι ?_⟩
    have hx : ι x = ∑ i, c i • (ι ∘ γ) i := by
      have h := congrArg Subtype.val (bs.sum_repr ⟨ι x, hmem x⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, bs, Module.Basis.span_apply] at h
      exact h.symm
    rw [hΦL, map_smul, hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ha i, ← smul_assoc]
    rfl
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A B).FG)
  choose! dS hdS0 hdS using fun x (_ : x ∈ S) ↦ hmult x
  set d : A := ∏ x ∈ S, dS x with hd_def
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx ↦ hdS0 x hx
  have hdmem : ∀ y : B, d • y ∈ LinearMap.range Φ := by
    intro y
    have hy : y ∈ Submodule.span A (S : Set B) := by rw [hS]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [hd_def, ← Finset.prod_erase_mul S dS hx, mul_smul]
      exact Submodule.smul_mem _ _ (hdS x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have hle : LinearMap.range (d • (LinearMap.id : B →ₗ[A] B)) ≤ LinearMap.range Φ := by
    rintro _ ⟨y, rfl⟩; exact hdmem y
  exact ne_top_of_le_ne_top (length_quot_smul_ne_top' d hd0)
    (Module.length_le_of_surjective _ (Submodule.factor_surjective hle))

variable [FiniteDimensional K L]
  {C : Type*} [CommRing C] [IsDomain C] [Algebra A C] [Algebra C L] [IsScalarTower A C L]

variable (A K) in
include A K in
/-- **Krull–Akizuki, length part**: `C/aC` has finite `A`-length for `0 ≠ a ∈ A`, whenever the
domain `C ⊇ A` embeds in a finite extension `L` of `K = Frac A`.-/
theorem length_quot_algebraMap_ne_top (hCL : Function.Injective (algebraMap C L)) (a : A)
    (ha : a ≠ 0) : Module.length A (C ⧸ Ideal.span {algebraMap A C a}) ≠ ⊤ := by
  classical
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range (algebraMap C L))
  haveI : Finite s := hs_li.finite
  haveI : Fintype s := Fintype.ofFinite s
  choose γ hγ using fun x : s ↦ hs_sub x.2
  have haL : algebraMap A L a ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha)
  have haC : algebraMap A C a ≠ 0 := by
    intro h0; apply haL; rw [IsScalarTower.algebraMap_apply A C L, h0, map_zero]
  set N : ℕ∞ := ecoker (Matrix.diagonal (fun _ : s ↦ a)) with hNdef
  have hdiag : (Matrix.diagonal (fun _ : s ↦ a)).det ≠ 0 := by
    rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ha
  have hN : N ≠ ⊤ := ecoker_ne_top hdiag
  let Q := C ⧸ Ideal.span {algebraMap A C a}
  let π : C →ₗ[A] Q := (Ideal.Quotient.mkₐ A (Ideal.span {algebraMap A C a})).toLinearMap
  have hbound : ∀ T : Finset C,
      Module.length A (LinearMap.range
        (π ∘ₗ (Submodule.span A (Set.range γ ∪ (T : Set C))).subtype)) ≤ N := by
    intro T
    set P := Submodule.span A (Set.range γ ∪ (T : Set C)) with hPdef
    haveI : Module.Finite A P :=
      Module.Finite.span_of_finite A ((Set.finite_range γ).union T.finite_toSet)
    have hγP : ∀ i, γ i ∈ P := fun i ↦ Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    let γ' : s → P := fun i ↦ ⟨γ i, hγP i⟩
    let ι : P →ₗ[A] L := (IsScalarTower.toAlgHom A C L).toLinearMap ∘ₗ P.subtype
    have hι : Function.Injective ι := hCL.comp Subtype.val_injective
    have hιγ : ι ∘ γ' = Subtype.val := by
      funext i; simp [ι, γ', hγ]
    have hli' : LinearIndependent K (ι ∘ γ') := by rw [hιγ]; exact hs_li
    have hmem : ∀ x, ι x ∈ Submodule.span K (Set.range (ι ∘ γ')) := by
      intro x
      rw [hιγ, Subtype.range_coe, hs_span]
      exact Submodule.subset_span ⟨x.1, rfl⟩
    obtain ⟨hΦ, hfin⟩ := lattice_data ι hι γ' hli' hmem
    have hφ : Function.Injective (a • (LinearMap.id : P →ₗ[A] P)) := by
      intro x y hxy
      have h' : a • x = a • y := hxy
      apply Subtype.ext
      have := congrArg Subtype.val h'
      rw [Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def] at this
      exact mul_left_cancel₀ haC this
    have hcomm : (a • (LinearMap.id : P →ₗ[A] P)) ∘ₗ Fintype.linearCombination A γ' =
        Fintype.linearCombination A γ' ∘ₗ (Matrix.diagonal (fun _ : s ↦ a)).mulVecLin := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Matrix.mulVecLin_apply, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul,
        Matrix.mulVec_diagonal]
    have hlen := length_coker_eq_ecoker _ hΦ _ hφ _ hcomm hfin
    -- the image of `P` is a quotient of `P / aP`
    let ψ := π ∘ₗ P.subtype
    have hker : LinearMap.range (a • (LinearMap.id : P →ₗ[A] P)) ≤ LinearMap.ker ψ := by
      rintro _ ⟨x, rfl⟩
      change π ((a • x : P) : C) = 0
      rw [Submodule.coe_smul, Algebra.smul_def]
      simp only [π, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_mul]
    rw [← (LinearMap.quotKerEquivRange ψ).length_eq, hNdef, ← hlen]
    exact Module.length_le_of_surjective _ (Submodule.factor_surjective hker)
  -- a chain argument
  intro htop
  have hlt : N < Module.length A Q := by
    rw [show Module.length A Q = ⊤ from htop]
    exact lt_top_iff_ne_top.mpr hN
  lift N to ℕ using hN with n hn
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ Order.height (⊤ : Submodule A Q) := by
    rw [← Module.length_eq_height]
    exact Order.add_one_le_of_lt hlt
  obtain ⟨p, hplast, hplen⟩ := Order.exists_series_of_le_height (⊤ : Submodule A Q) hle
  have hstep : ∀ i : Fin p.length, ∃ w, w ∈ p i.succ ∧ w ∉ p i.castSucc := by
    intro i
    exact SetLike.exists_of_lt (p.strictMono (Fin.castSucc_lt_succ (i := i)))
  choose w hw1 hw2 using hstep
  choose t ht using fun i ↦ Ideal.Quotient.mk_surjective (I := Ideal.span {algebraMap A C a}) (w i)
  let T : Finset C := Finset.univ.image t
  set W := LinearMap.range (π ∘ₗ (Submodule.span A (Set.range γ ∪ (T : Set C))).subtype)
  have hwW : ∀ i, w i ∈ W := by
    intro i
    refine ⟨⟨t i, Submodule.subset_span (Or.inr (Finset.mem_coe.mpr
      (Finset.mem_image_of_mem t (Finset.mem_univ i))))⟩, ?_⟩
    simp [π, ht i]
  let q : LTSeries (Submodule A Q) :=
    { length := p.length
      toFun := fun j ↦ W ⊓ p j
      step := fun i ↦ by
        refine lt_of_le_of_ne
          (inf_le_inf_left _ (p.strictMono (Fin.castSucc_lt_succ (i := i))).le) ?_
        intro h
        have : w i ∈ W ⊓ p i.succ := ⟨hwW i, hw1 i⟩
        rw [← h] at this
        exact hw2 i this.2 }
  have hqlast : q.last ≤ W := inf_le_left
  have h1 := Order.length_le_height hqlast
  rw [← Module.length_submodule] at h1
  have h2 := (hbound T).trans_eq' (rfl : Module.length A W = _)
  have : ((p.length : ℕ) : ℕ∞) ≤ n := h1.trans h2
  rw [hplen] at this
  norm_cast at this
  omega

variable (A K) in
include A K in
/-- **Krull–Akizuki, dimension part**: a domain `C ⊇ A` embedding in a finite extension of
`Frac A`, with `A` a one-dimensional Noetherian domain, has dimension `≤ 1`.-/
theorem krullDimLE_one_of_finite (hCL : Function.Injective (algebraMap C L)) :
    Ring.KrullDimLE 1 C := by
  rw [Ring.krullDimLE_one_iff]
  intro P hP
  by_cases hP0 : P = ⊥
  · left
    subst hP0
    exact ⟨⟨Ideal.isPrime_bot, le_rfl⟩, fun _ _ _ ↦ bot_le⟩
  right
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have halg : IsAlgebraic A c := by
    have h1 : IsAlgebraic K (algebraMap C L c) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic A (algebraMap C L c) := (IsFractionRing.isAlgebraic_iff A K L).mpr h1
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A C L) hCL).mp h2
  have hne := Ideal.comap_ne_bot_of_algebraic_mem hc0 (Ideal.mem_span_singleton_self c) halg
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfin := length_quot_algebraMap_ne_top A K hCL a ha0
  have hfinC : IsFiniteLength C (C ⧸ Ideal.span {algebraMap A C a}) := by
    rw [← Module.length_ne_top_iff]
    refine ne_top_of_le_ne_top hfin ?_
    have := Submodule.length_le_length_restrictScalars A
      (⊤ : Submodule C (C ⧸ Ideal.span {algebraMap A C a}))
    rwa [Submodule.restrictScalars_top, Module.length_top, Module.length_top] at this
  haveI : IsArtinian C (C ⧸ Ideal.span {algebraMap A C a}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinC).2
  have hle : Ideal.span {algebraMap A C a} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (Ideal.mem_span_singleton'.mp ha).elim fun y hy ↦ hy ▸ P.mul_mem_left y hcP
  haveI : IsArtinian C (C ⧸ P) :=
    isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)
  haveI : IsArtinianRing (C ⧸ P) := isArtinian_of_tower C inferInstance
  exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)

end KA

section LocQuot

variable {B D : Type*} [CommRing B] [CommRing D] [Algebra B D]

theorem map_mk_isPrime (m : Ideal B) [m.IsPrime] (I : Ideal B) (hI : I ≤ m) :
    (m.map (Ideal.Quotient.mk I)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

theorem mem_map_mk_iff (m : Ideal B) (I : Ideal B) (hI : I ≤ m) (x : B) :
    Ideal.Quotient.mk I x ∈ m.map (Ideal.Quotient.mk I) ↔ x ∈ m := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, sup_eq_left.mpr hI]

/-- Localization commutes with quotients: `(D/ID)` is the localization of `B/I` at `m/I`.-/
theorem isLocalization_quotient (m : Ideal B) [m.IsPrime] [IsLocalization.AtPrime D m]
    (I : Ideal B) (hI : I ≤ m) :
    letI : Algebra (B ⧸ I) (D ⧸ I.map (algebraMap B D)) :=
      (Ideal.quotientMap _ (algebraMap B D) Ideal.le_comap_map).toAlgebra
    haveI := map_mk_isPrime m I hI
    IsLocalization.AtPrime (D ⧸ I.map (algebraMap B D)) (m.map (Ideal.Quotient.mk I)) := by
  letI : Algebra (B ⧸ I) (D ⧸ I.map (algebraMap B D)) :=
    (Ideal.quotientMap _ (algebraMap B D) Ideal.le_comap_map).toAlgebra
  haveI := map_mk_isPrime m I hI
  have halg : ∀ x : B, algebraMap (B ⧸ I) (D ⧸ I.map (algebraMap B D)) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk _ (algebraMap B D x) := fun x ↦ Ideal.quotientMap_mk
  constructor
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx : x ∉ m := fun h ↦ hy ((mem_map_mk_iff m I hI x).mpr h)
    rw [halg]
    exact (IsLocalization.map_units D (⟨x, hx⟩ : m.primeCompl)).map _
  · intro z
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj m.primeCompl d
    have hs : Ideal.Quotient.mk I (s : B) ∈ (m.map (Ideal.Quotient.mk I)).primeCompl :=
      fun h ↦ s.2 ((mem_map_mk_iff m I hI s).mp h)
    refine ⟨⟨Ideal.Quotient.mk I x, ⟨_, hs⟩⟩, ?_⟩
    simp only
    rw [halg, halg, ← map_mul, hxs]
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [halg, halg, Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨⟨i, s⟩, his⟩ := (IsLocalization.mem_map_algebraMap_iff m.primeCompl D).mp hxy
    simp only at his
    rw [← map_mul] at his
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl D).mp his
    have hcs : Ideal.Quotient.mk I ((c : B) * s) ∈ (m.map (Ideal.Quotient.mk I)).primeCompl :=
      fun h ↦ (m.primeCompl.mul_mem c.2 s.2) ((mem_map_mk_iff m I hI _).mp h)
    refine ⟨⟨_, hcs⟩, ?_⟩
    simp only
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
    have : (c : B) * s * x - (c : B) * s * y = (c : B) * ((x - y) * s) := by ring
    rw [this, hc]
    exact I.mul_mem_left _ i.2

end LocQuot

section CRT

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

theorem span_map_eq {D : Type*} [CommRing D] [Algebra B D] (b : B) :
    (Ideal.span {b}).map (algebraMap B D) = Ideal.span {algebraMap B D b} := by
  rw [Ideal.map_span, Set.image_singleton]

/-- **Chinese remainder for lengths**: if `B/bB` is Artinian, its `A`-length is the sum of the
`A`-lengths of `D_t / b D_t` over any family of localizations `D_t = B_{m_t}` indexed
bijectively by (a superset of) the primes containing `b`.-/
theorem length_eq_sum_localizations (b : B) [IsArtinianRing (B ⧸ Ideal.span {b})]
    {T : Type*} [Fintype T] (m : T → Ideal B) [hm : ∀ t, (m t).IsPrime]
    (D : T → Type*) [∀ t, CommRing (D t)] [∀ t, Algebra B (D t)] [∀ t, Algebra A (D t)]
    [∀ t, IsScalarTower A B (D t)] [∀ t, IsLocalization.AtPrime (D t) (m t)]
    (hinj : Function.Injective m) (hsurj : ∀ P : Ideal B, P.IsPrime → b ∈ P → ∃ t, m t = P) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ t, Module.length A (D t ⧸ Ideal.span {algebraMap B (D t) b}) := by
  classical
  set I : Ideal B := Ideal.span {b} with hIdef
  haveI : Fintype (PrimeSpectrum (B ⧸ I)) := Fintype.ofFinite _
  have h1 : Module.length A (B ⧸ I) =
      ∑ P : PrimeSpectrum (B ⧸ I), Module.length A (Localization.AtPrime P.asIdeal) := by
    rw [((PrimeSpectrum.toPiLocalizationEquiv (B ⧸ I)).restrictScalars A).toLinearEquiv.length_eq]
    exact Module.length_pi_of_fintype A _
  rw [h1]
  -- terms with `b ∉ m t` vanish
  have hzero : ∀ t, b ∉ m t → Module.length A (D t ⧸ Ideal.span {algebraMap B (D t) b}) = 0 := by
    intro t hbt
    have hu : IsUnit (algebraMap B (D t) b) :=
      IsLocalization.map_units (D t) (⟨b, hbt⟩ : (m t).primeCompl)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    haveI : Subsingleton (D t ⧸ (⊤ : Ideal (D t))) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero
  rw [← Finset.sum_filter_of_ne (p := fun t ↦ b ∈ m t) (fun t _ h ↦ by
    by_contra hbt; exact h (hzero t hbt))]
  have hIle : ∀ t, b ∈ m t → I ≤ m t := fun t hbt ↦ by
    rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]; exact hbt
  symm
  refine Finset.sum_bij (fun t ht ↦ (⟨(m t).map (Ideal.Quotient.mk I),
      map_mk_isPrime (m t) I (hIle t (Finset.mem_filter.mp ht).2)⟩ : PrimeSpectrum (B ⧸ I)))
    (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro t₁ ht₁ t₂ ht₂ h
    apply hinj
    have h' := congrArg (fun P : PrimeSpectrum (B ⧸ I) ↦ P.asIdeal.comap (Ideal.Quotient.mk I)) h
    simp only [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker] at h'
    rwa [sup_eq_left.mpr (hIle t₁ (Finset.mem_filter.mp ht₁).2),
      sup_eq_left.mpr (hIle t₂ (Finset.mem_filter.mp ht₂).2)] at h'
  · intro P _
    haveI : (P.asIdeal.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ _
    have hbP : b ∈ P.asIdeal.comap (Ideal.Quotient.mk I) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b)]
      exact P.asIdeal.zero_mem
    obtain ⟨t, ht⟩ := hsurj _ inferInstance hbP
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht ▸ hbP⟩, ?_⟩
    ext1
    simp only [ht]
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  · intro t ht
    have hbt := (Finset.mem_filter.mp ht).2
    haveI := map_mk_isPrime (m t) I (hIle t hbt)
    letI : Algebra (B ⧸ I) (D t ⧸ I.map (algebraMap B (D t))) :=
      (Ideal.quotientMap _ (algebraMap B (D t)) Ideal.le_comap_map).toAlgebra
    haveI := isLocalization_quotient (D := D t) (m t) I (hIle t hbt)
    haveI : IsScalarTower A (B ⧸ I) (D t ⧸ I.map (algebraMap B (D t))) := by
      apply IsScalarTower.of_algebraMap_eq
      intro a
      change Ideal.Quotient.mk _ (algebraMap A (D t) a) =
        Ideal.quotientMap _ (algebraMap B (D t)) Ideal.le_comap_map
          (Ideal.Quotient.mk I (algebraMap A B a))
      rw [Ideal.quotientMap_mk, ← IsScalarTower.algebraMap_apply]
    let e := (IsLocalization.algEquiv ((m t).map (Ideal.Quotient.mk I)).primeCompl
      (Localization.AtPrime ((m t).map (Ideal.Quotient.mk I)))
      (D t ⧸ I.map (algebraMap B (D t)))).restrictScalars A
    rw [e.toLinearEquiv.length_eq, span_map_eq]

end CRT

section LocalFormula

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
  {K L : Type*} [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]

omit [IsDomain R] [IsDomain S] in
/-- If `S` is integral over `R`, the image of `S` spans `L = Frac S` over `K = Frac R`.-/
theorem span_range_eq_top [Algebra.IsIntegral R S] :
    Submodule.span K (Set.range (algebraMap S L)) = ⊤ := by
  set W := Submodule.span K (Set.range (algebraMap S L)) with hW
  have h1 : (1 : L) ∈ W := Submodule.subset_span ⟨1, map_one _⟩
  have hmul : ∀ x y, x ∈ W → y ∈ W → x * y ∈ W := by
    intro x y hx hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact ⟨s * t, map_mul _ _ _⟩
  let W' : Subalgebra K L := Submodule.toSubalgebra W h1 hmul
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, c, _, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hcalg : IsAlgebraic K (algebraMap S L c) :=
    (((Algebra.IsIntegral.isIntegral (R := R) c).map
      (IsScalarTower.toAlgHom R S L)).tower_top (A := K)).isAlgebraic
  have hinv : (algebraMap S L c)⁻¹ ∈ W' :=
    Subalgebra.inv_mem_of_algebraic W' (x := ⟨_, Submodule.subset_span ⟨c, rfl⟩⟩) hcalg
  rw [div_eq_mul_inv]
  exact W'.mul_mem (Submodule.subset_span ⟨a, rfl⟩) hinv

variable [Module.Finite R S] [FiniteDimensional K L]
  (p : Ideal R) [p.IsPrime]
  {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Algebra R A] [IsLocalization.AtPrime A p] [Algebra A K] [IsFractionRing A K]
  [IsScalarTower R A K]

variable (A) in
include p A in
omit [IsDomain S] [Module.Finite R S] [FiniteDimensional K L] [IsNoetherianRing A]
  [Algebra A K] [IsFractionRing A K] [IsScalarTower R A K] in
/-- A nonzero prime inside a height-one prime equals it.-/
theorem eq_of_le_of_ne_bot {q : Ideal R} [q.IsPrime] (hq : q ≠ ⊥) (hqp : q ≤ p) : q = p := by
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  have hdisj : Disjoint (p.primeCompl : Set R) q := by
    rw [Set.disjoint_left]; intro r hr hrq; exact hr (hqp hrq)
  haveI hq' := IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl A q inferInstance hdisj
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl A inferInstance hdisj
  have hinjA : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A p.primeCompl_le_nonZeroDivisors
  have hne : q.map (algebraMap R A) ≠ ⊥ := by
    intro h0; apply hq; rw [← hcomap, h0]; exact Ideal.comap_bot_of_injective _ hinjA
  rcases Ring.krullDimLE_one_iff.mp inferInstance (q.map (algebraMap R A)) hq' with hmin | hmax
  · exact absurd (le_bot_iff.mp (hmin.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le)) hne
  · have hdisjp : Disjoint (p.primeCompl : Set R) p := by
      rw [Set.disjoint_left]; intro r hr hrp; exact hr hrp
    have h2 := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl A inferInstance hdisjp
    rw [← hcomap, ← h2, IsLocalRing.eq_maximalIdeal hmax,
      IsLocalization.AtPrime.map_eq_maximalIdeal p A]

variable {T : Type*} [Fintype T] (Q : T → Ideal S) [hQ : ∀ t, (Q t).IsPrime]
  (D : T → Type*) [∀ t, CommRing (D t)] [∀ t, Algebra S (D t)]
  [∀ t, IsLocalization.AtPrime (D t) (Q t)] [∀ t, Algebra A (D t)]

/-- **Fulton A.3 (local form)**: for a finite extension `R → S` of domains, a height-one prime
`p` of `R` with `A = R_p`, the stalks `D t = S_{Q t}` at the primes over `p`, and `0 ≠ b ∈ S`,
`ord_A (N_{L/K} b) = Σ_t ℓ_A (D_t / b D_t)`.-/
theorem local_formula
    (hDtower : ∀ t r, algebraMap A (D t) (algebraMap R A r) =
      algebraMap S (D t) (algebraMap R S r))
    (hQover : ∀ t, (Q t).comap (algebraMap R S) = p)
    (hQinj : Function.Injective Q)
    (hQsurj : ∀ Q' : Ideal S, Q'.IsPrime → Q'.comap (algebraMap R S) = p → ∃ t, Q t = Q')
    (b : S) (hb : b ≠ 0) :
    (∑ t, Module.length A (D t ⧸ Ideal.span {algebraMap S (D t) b})) ≠ ⊤ ∧
      Ring.ordFrac A (Algebra.norm K (algebraMap S L b)) =
        ((Multiplicative.ofAdd
          ((∑ t, Module.length A (D t ⧸ Ideal.span {algebraMap S (D t) b})).toNat : ℤ) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  classical
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hSL : Function.Injective (algebraMap S L) := IsFractionRing.injective S L
  set M := Algebra.algebraMapSubmonoid S p.primeCompl with hMdef
  have hMmem : ∀ m ∈ M, ∃ r, r ∉ p ∧ algebraMap R S r = m := by
    rintro m ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  have hM0 : ∀ m ∈ M, algebraMap S L m ≠ 0 := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := hMmem m hm
    rw [← IsScalarTower.algebraMap_apply]
    intro h0
    exact hr ((hRL (h0.trans (map_zero _).symm)) ▸ p.zero_mem)
  have hMnz : M ≤ nonZeroDivisors S := fun m hm ↦
    mem_nonZeroDivisors_of_ne_zero (fun h ↦ hM0 m hm (by rw [h, map_zero]))
  let B := Localization M
  letI : Algebra A B := localizationAlgebra p.primeCompl S
  haveI : IsScalarTower R A B := isScalarTower_localizationAlgebra _ _
  haveI : Module.Finite A B := Module.Finite.of_isLocalization R S p.primeCompl
  letI : Algebra B L := (IsLocalization.lift (M := M) (S := B) (g := algebraMap S L)
    (fun m ↦ isUnit_iff_ne_zero.mpr (hM0 m m.2))).toAlgebra
  have hBL : ∀ s : S, algebraMap B L (algebraMap S B s) = algebraMap S L s := fun s ↦
    IsLocalization.lift_eq _ s
  haveI : IsScalarTower S B L := IsScalarTower.of_algebraMap_eq (fun s ↦ (hBL s).symm)
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : IsScalarTower A B L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R S B, hBL,
      RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R A K,
      ← IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R S L]
  have hinj : Function.Injective (algebraMap B L) := by
    change Function.Injective (IsLocalization.lift (M := M) (S := B) (g := algebraMap S L) _)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective B hMnz).eq_iff, hSL.eq_iff]
  haveI : Algebra.IsIntegral R S := inferInstance
  have hspan : Submodule.span K (Set.range (algebraMap B L)) = ⊤ := by
    rw [eq_top_iff, ← span_range_eq_top (R := R) (S := S) (K := K) (L := L)]
    apply Submodule.span_mono
    rintro _ ⟨s, rfl⟩
    exact ⟨algebraMap S B s, hBL s⟩
  have hbB : algebraMap S B b ≠ 0 := fun h ↦ hb (IsLocalization.injective B hMnz
    (h.trans (map_zero _).symm))
  obtain ⟨hfin, hnorm⟩ := length_quot_eq_ordFrac_norm (A := A) (K := K) (L := L) hinj hspan
    (algebraMap S B b) hbB
  rw [hBL] at hnorm
  -- the CRT decomposition
  haveI : IsArtinianRing (B ⧸ Ideal.span {algebraMap S B b}) := by
    have h1 : IsFiniteLength A (B ⧸ Ideal.span {algebraMap S B b}) :=
      Module.length_ne_top_iff.mp hfin
    haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp h1).2
    exact isArtinian_of_tower A inferInstance
  have hQdisj : ∀ t, Disjoint (M : Set S) (Q t) := by
    intro t
    rw [Set.disjoint_left]
    intro m hm hmQ
    obtain ⟨r, hr, rfl⟩ := hMmem m hm
    apply hr
    rw [← hQover t]
    exact hmQ
  letI instDB : ∀ t, Algebra B (D t) := fun t ↦ (IsLocalization.lift (M := M) (S := B)
    (g := algebraMap S (D t)) (fun m ↦ IsLocalization.map_units (D t)
      (⟨m, fun h ↦ Set.disjoint_left.mp (hQdisj t) m.2 h⟩ : (Q t).primeCompl))).toAlgebra
  have hBD : ∀ t (s : S), algebraMap B (D t) (algebraMap S B s) = algebraMap S (D t) s :=
    fun t s ↦ IsLocalization.lift_eq _ s
  haveI : ∀ t, IsScalarTower S B (D t) := fun t ↦
    IsScalarTower.of_algebraMap_eq (fun s ↦ (hBD t s).symm)
  haveI : ∀ t, IsScalarTower A B (D t) := by
    intro t
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    simp only [RingHom.comp_apply]
    rw [hDtower, ← IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R S B,
      hBD]
  set m : T → Ideal B := fun t ↦ (Q t).map (algebraMap S B) with hmdef
  haveI hmprime : ∀ t, (m t).IsPrime := fun t ↦
    IsLocalization.isPrime_of_isPrime_disjoint M B (Q t) inferInstance (hQdisj t)
  have hmcomap : ∀ t, (m t).comap (algebraMap S B) = Q t := fun t ↦
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance (hQdisj t)
  haveI : ∀ t, IsLocalization.AtPrime (D t) (m t) := by
    intro t
    have hle : M ≤ (Q t).primeCompl := fun x hx h ↦ Set.disjoint_left.mp (hQdisj t) hx h
    haveI := IsLocalization.isLocalization_of_submonoid_le B (D t) M (Q t).primeCompl hle
    refine IsLocalization.isLocalization_of_is_exists_mul_mem (D t)
      ((Q t).primeCompl.map (algebraMap S B)) (m t).primeCompl ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩ hsm
      apply hs
      rw [← hmcomap t]
      exact hsm
    · rintro ⟨x, hx⟩
      obtain ⟨⟨s, u⟩, hsu⟩ := IsLocalization.surj M x
      refine ⟨algebraMap S B u, ⟨s, ?_, ?_⟩⟩
      · intro hsQ
        apply hx
        have hsm : algebraMap S B s ∈ m t := Ideal.mem_map_of_mem _ hsQ
        rw [← hsu] at hsm
        rcases (hmprime t).mem_or_mem hsm with h | h
        · exact h
        · exfalso
          apply hle u.2
          rw [← hmcomap t]
          exact h
      · simp only
        rw [mul_comm]
        exact hsu.symm
  have hminj : Function.Injective m := by
    intro t₁ t₂ h
    apply hQinj
    rw [← hmcomap t₁, ← hmcomap t₂, h]
  have hmsurj : ∀ P : Ideal B, P.IsPrime → algebraMap S B b ∈ P → ∃ t, m t = P := by
    intro P hP hbP
    set Q' := P.comap (algebraMap S B)
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hbQ' : b ∈ Q' := hbP
    have hle : Q'.comap (algebraMap R S) ≤ p := by
      intro r hr
      by_contra hrp
      have hu : IsUnit (algebraMap S B (algebraMap R S r)) :=
        IsLocalization.map_units B (⟨algebraMap R S r, ⟨r, hrp, rfl⟩⟩ : M)
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hr hu)
    have hne : Q'.comap (algebraMap R S) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hb hbQ' (Algebra.IsIntegral.isIntegral b)
    haveI : (Q'.comap (algebraMap R S)).IsPrime := Ideal.comap_isPrime _ _
    have hover := eq_of_le_of_ne_bot p A hne hle
    obtain ⟨t, ht⟩ := hQsurj Q' inferInstance hover
    refine ⟨t, ?_⟩
    rw [hmdef]
    change (Q t).map (algebraMap S B) = P
    rw [ht]
    exact IsLocalization.map_under M B P
  have hcrt := length_eq_sum_localizations (A := A) (algebraMap S B b) m D hminj hmsurj
  have hcrt' : Module.length A (B ⧸ Ideal.span {algebraMap S B b}) =
      ∑ t, Module.length A (D t ⧸ Ideal.span {algebraMap S (D t) b}) := by
    rw [hcrt]
    exact Finset.sum_congr rfl (fun t _ ↦ by rw [hBD])
  rw [← hcrt']
  exact ⟨hfin, hnorm⟩

end LocalFormula

end RiemannRoch.ProperPushforwardNorm
