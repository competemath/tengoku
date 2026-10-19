/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.Flat.LocallyFree
import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.RingTheory.Ideal.GoingUp
import Tengoku.Seed.RingTheory.LocalProperties.Reduced
import Tengoku.Seed.LinearAlgebra.Dimension.OrzechProperty
import Tengoku.Seed.RingTheory.Smooth.Flat
import Tengoku.LanaOka.Oka.Analytification.RET.ES.EtaleCriterion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Milnor patching of finite étale algebras

Let `R → S` be an injective ring map and `I ⊆ R` an ideal which is also an ideal of `S`
(`i s ∈ I` for `i ∈ I`, `s ∈ S`), so that `R = S ×_{S ⧸ I S} R ⧸ I`. Given an `S`-algebra `P`, an
`R ⧸ I`-algebra `Q` and an `S ⧸ I S`-algebra `P₀` with maps `φ : P → P₀` and `ψ : Q → P₀`
exhibiting `P₀` as `(S ⧸ I S) ⊗[S] P` and as `(S ⧸ I S) ⊗[R ⧸ I] Q`, the fibre product
`P ×_{P₀} Q` (`MilnorPatching.patch`) satisfies `(R ⧸ I) ⊗[R] (P ×_{P₀} Q) ≅ Q`. If moreover `R`
is noetherian and reduced, `R → S` is finite and `P` is finite étale over `S`, then `P ×_{P₀} Q` is
finite étale over `R` and `S ⊗[R] (P ×_{P₀} Q) ≅ P`.

Flatness is proved through fibre dimensions: the fibre of `P ×_{P₀} Q` at a prime `q ∩ R` has the
dimension of the fibre of `P` at `q` (`MilnorPatching.finrank_fiber_patch`), which is locally
constant along specialisations, and over a reduced local ring a finite module whose fibre
dimensions at all primes agree is free (`Module.free_of_forall_finrank_fiber_eq`).

## Main results

- `Module.free_of_forall_finrank_fiber_eq`,
  `Module.flat_localizedModule_of_forall_finrank_fiber_eq`: freeness from constant fibre
  dimension over a reduced ring.
- `MilnorPatching.isBaseChange_snd`: `(R ⧸ I) ⊗[R] (P ×_{P₀} Q) ≅ Q`.
- `MilnorPatching.flat_patch`, `MilnorPatching.isBaseChange_fst`: flatness and
  `S ⊗[R] (P ×_{P₀} Q) ≅ P`.
- `MilnorPatching.etale_patch`: Milnor patching of finite étale algebras.
-/

open TensorProduct

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The dimension of the fibre `K ⊗[R] M` does not change along a field extension `K → L`. -/
lemma finrank_tensorProduct_eq_of_isScalarTower (K L : Type*) [Field K] [Field L] [Algebra R K]
    [Algebra R L] [Algebra K L] [IsScalarTower R K L] :
    finrank L (L ⊗[R] M) = finrank K (K ⊗[R] M) := by
  rw [← (AlgebraTensorModule.cancelBaseChange R K L L M).finrank_eq, Module.finrank_baseChange]

/-- If `v ∘ u` and `u ∘ v` are multiplication by `r` and `r` is a unit in `K`, then
`K ⊗ u` is bijective. -/
lemma bijective_baseChange_of_comp_eq_smul {N : Type*} [AddCommGroup N] [Module R N]
    (K : Type*) [CommRing K] [Algebra R K] (u : M →ₗ[R] N) (v : N →ₗ[R] M) (r : R)
    (h₁ : v ∘ₗ u = r • LinearMap.id) (h₂ : u ∘ₗ v = r • LinearMap.id)
    (hr : IsUnit (algebraMap R K r)) : Function.Bijective (u.baseChange K) := by
  obtain ⟨c, hc⟩ := hr.exists_left_inv
  have hM (x : K ⊗[R] M) : c • r • x = x := by
    rw [← algebraMap_smul K r x, smul_smul, hc, one_smul]
  have hN (x : K ⊗[R] N) : c • r • x = x := by
    rw [← algebraMap_smul K r x, smul_smul, hc, one_smul]
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨c • v.baseChange K y, ?_⟩⟩
  · have h := congrArg (fun z ↦ c • v.baseChange K z) hxy
    simp only [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h₁,
      LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply,
      LinearMap.id_apply, hM] at h
    exact h
  · rw [map_smul, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h₂,
      LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply,
      LinearMap.id_apply, hN]

/-- **A finite module over a reduced local ring with constant fibre dimension is free.** -/
theorem free_of_forall_finrank_fiber_eq [IsLocalRing R] [IsReduced R] [Module.Finite R M]
    (h : ∀ (p : Ideal R) [p.IsPrime], finrank p.ResidueField (p.Fiber M) =
      finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)) :
    Module.Free R M := by
  let k := IsLocalRing.ResidueField R
  have hspan : Submodule.span k (Set.range fun m : M ↦ (1 : k) ⊗ₜ[R] m) = ⊤ := by
    have h1 := (IsLocalRing.map_tensorProduct_mk_eq_top (N := (⊤ : Submodule R M))).2 rfl
    rw [Submodule.map_top] at h1
    refine eq_top_iff.2 fun x _ ↦ ?_
    have hx : x ∈ LinearMap.range (TensorProduct.mk R k M 1) := h1 ▸ trivial
    obtain ⟨m, rfl⟩ := hx
    exact Submodule.subset_span ⟨m, rfl⟩
  obtain ⟨s, hs, hsspan, hli⟩ := exists_linearIndependent k (Set.range fun m : M ↦ (1 : k) ⊗ₜ[R] m)
  let b : Basis s k (k ⊗[R] M) := Basis.mk hli (by rw [Subtype.range_coe, hsspan, hspan])
  choose f hf using fun i : s ↦ hs i.2
  have hb : ∀ i, (1 : k) ⊗ₜ f i = b i := fun i ↦ (hf i).trans (Basis.mk_apply _ _ _).symm
  have hfspan := IsLocalRing.span_eq_top_of_tmul_eq_basis f b hb
  haveI : Finite s := Module.Finite.finite_basis b
  letI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = finrank k (k ⊗[R] M) := (Module.finrank_eq_card_basis b).symm
  let φ := Fintype.linearCombination R f
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hfspan]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext i
    have hmem : c i ∈ nilradical R := by
      rw [nilradical_eq_sInf]
      refine Submodule.mem_sInf.2 fun (p : Ideal R) hp ↦ ?_
      haveI : p.IsPrime := hp
      let κ := p.ResidueField
      let g : s → κ ⊗[R] M := fun j ↦ (1 : κ) ⊗ₜ f j
      have hg' : ∀ t : κ ⊗[R] M, t ∈ Submodule.span κ (Set.range g) := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => exact zero_mem _
        | add x y hx hy => exact add_mem hx hy
        | tmul x m =>
          have hm : m ∈ Submodule.span R (Set.range f) := hfspan ▸ trivial
          induction hm using Submodule.span_induction generalizing x with
          | mem m hm =>
            obtain ⟨j, rfl⟩ := hm
            have : x ⊗ₜ[R] f j = x • g j := by
              simp only [g, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rw [this]
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
          | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
          | add m m' _ _ hm hm' => rw [TensorProduct.tmul_add]; exact add_mem (hm x) (hm' x)
          | smul r m _ hm => rw [← TensorProduct.smul_tmul]; exact hm _
      have hg : ⊤ ≤ Submodule.span κ (Set.range g) := fun t _ ↦ hg' t
      have hli' : LinearIndependent κ g :=
        linearIndependent_of_top_le_span_of_card_eq_finrank hg (by rw [hcard, h p])
      have hsum : ∑ j, algebraMap R κ (c j) • g j = 0 := by
        have : (1 : κ) ⊗ₜ[R] φ c = 0 := by rw [hc, TensorProduct.tmul_zero]
        rw [← this, Fintype.linearCombination_apply, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [g, TensorProduct.tmul_smul, algebraMap_smul]
      have := Fintype.linearIndependent_iff.1 hli' _ hsum i
      exact Ideal.algebraMap_residueField_eq_zero.1 this
    rw [nilradical_eq_zero] at hmem
    exact hmem
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩)

/-- The fibres of `M_S` over `Localization S` are the fibres of `M` over `R`. -/
lemma finrank_tensorProduct_localizedModule (S : Submonoid R) (K : Type*) [Field K]
    [Algebra (Localization S) K] [Algebra R K] [IsScalarTower R (Localization S) K] :
    finrank K (K ⊗[Localization S] LocalizedModule S M) = finrank K (K ⊗[R] M) :=
  ((AlgebraTensorModule.congr (LinearEquiv.refl K K)
    (LocalizedModule.equivTensorProduct S M)).trans
      (AlgebraTensorModule.cancelBaseChange R (Localization S) K K M)).finrank_eq

/-- **Flatness at a prime from constant fibre dimension**, over a reduced ring: if the fibres of
the finite module `M` at all primes `p ≤ m` have the same dimension as the fibre at `m`, then
`M_m` is flat. -/
theorem flat_localizedModule_of_forall_finrank_fiber_eq [IsReduced R] [Module.Finite R M]
    (m : Ideal R) [m.IsPrime]
    (h : ∀ (p : Ideal R) [p.IsPrime], p ≤ m →
      finrank p.ResidueField (p.Fiber M) = finrank m.ResidueField (m.Fiber M)) :
    Module.Flat R (LocalizedModule m.primeCompl M) := by
  let Rm := Localization.AtPrime m
  haveI : Module.Finite Rm (LocalizedModule m.primeCompl M) :=
    Module.Finite.of_isLocalizedModule m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl M)
  haveI : Module.Free Rm (LocalizedModule m.primeCompl M) := by
    refine free_of_forall_finrank_fiber_eq fun Q _ ↦ ?_
    let p := Q.comap (algebraMap R Rm)
    have hp : p ≤ m := fun x hx ↦ by
      by_contra hxm
      have hu : IsUnit (algebraMap R Rm x) :=
        IsLocalization.map_units Rm (⟨x, hxm⟩ : m.primeCompl)
      exact Ideal.IsPrime.ne_top (inferInstanceAs Q.IsPrime) (Ideal.eq_top_of_isUnit_mem Q hx hu)
    letI : Algebra R Q.ResidueField :=
      ((algebraMap Rm Q.ResidueField).comp (algebraMap R Rm)).toAlgebra
    haveI : IsScalarTower R Rm Q.ResidueField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : Algebra p.ResidueField Q.ResidueField :=
      (Ideal.ResidueField.map p Q (algebraMap R Rm) rfl).toAlgebra
    haveI : IsScalarTower R p.ResidueField Q.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun r ↦
        (Ideal.ResidueField.map_algebraMap p Q (algebraMap R Rm) rfl r).symm
    rw [finrank_tensorProduct_localizedModule (S := m.primeCompl),
      finrank_tensorProduct_eq_of_isScalarTower p.ResidueField Q.ResidueField, h p hp,
      finrank_tensorProduct_localizedModule (S := m.primeCompl) (K := IsLocalRing.ResidueField Rm)]
  haveI : Module.Flat Rm (LocalizedModule m.primeCompl M) := inferInstance
  haveI : Module.Flat R Rm := IsLocalization.flat Rm m.primeCompl
  exact Module.Flat.trans R Rm (LocalizedModule m.primeCompl M)

end Module

namespace MilnorPatching

open Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

/-- The algebra structure of `S ⧸ I S` over `R ⧸ I`. -/
abbrev quotientAlgebra : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

attribute [local instance] quotientAlgebra

instance : IsScalarTower R (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable {I} {P Q P₀ : Type*} [CommRing P] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
  [CommRing Q] [Algebra R Q] [Algebra (R ⧸ I) Q] [IsScalarTower R (R ⧸ I) Q]
  [CommRing P₀] [Algebra R P₀] [Algebra S P₀] [Algebra (R ⧸ I) P₀] [IsScalarTower R S P₀]
  [IsScalarTower R (R ⧸ I) P₀]
  (φ : P →ₐ[S] P₀) (ψ : Q →ₐ[R ⧸ I] P₀)

/-- **The patched algebra** `P ×_{P₀} Q`. -/
def patch : Subalgebra R (P × Q) :=
  AlgHom.equalizer ((φ.restrictScalars R).comp (AlgHom.fst R P Q))
    ((ψ.restrictScalars R).comp (AlgHom.snd R P Q))

lemma mem_patch {x : P × Q} : x ∈ patch φ ψ ↔ φ x.1 = ψ x.2 :=
  Iff.rfl

/-- The projection `P ×_{P₀} Q → P`. -/
def fst : patch φ ψ →ₐ[R] P :=
  (AlgHom.fst R P Q).comp (patch φ ψ).val

/-- The projection `P ×_{P₀} Q → Q`. -/
def snd : patch φ ψ →ₐ[R] Q :=
  (AlgHom.snd R P Q).comp (patch φ ψ).val

@[simp]
lemma fst_apply (x : patch φ ψ) : fst φ ψ x = x.1.1 :=
  rfl

@[simp]
lemma snd_apply (x : patch φ ψ) : snd φ ψ x = x.1.2 :=
  rfl

lemma φ_fst (x : patch φ ψ) : φ (fst φ ψ x) = ψ (snd φ ψ x) :=
  x.2

variable {φ ψ}

section BaseChange

variable [Algebra (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀]
  (hφ : IsBaseChange (S ⧸ I.map (algebraMap R S)) (φ.toLinearMap))
  (hψ : IsBaseChange (S ⧸ I.map (algebraMap R S)) (ψ.toLinearMap))

omit [Algebra R P] [IsScalarTower R S P] [Algebra R P₀] [Algebra (R ⧸ I) P₀] [IsScalarTower R S P₀]
  [IsScalarTower R (R ⧸ I) P₀] [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
include hφ in
lemma surjective_of_isBaseChange : Function.Surjective φ := by
  intro y
  induction y using hφ.inductionOn with
  | zero => exact ⟨0, map_zero φ⟩
  | tmul m => exact ⟨m, rfl⟩
  | smul s n hn =>
    obtain ⟨m, rfl⟩ := hn
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    refine ⟨s • m, ?_⟩
    rw [map_smul]
    exact (algebraMap_smul (S ⧸ I.map (algebraMap R S)) s (φ m)).symm
  | add n₁ n₂ h₁ h₂ =>
    obtain ⟨m₁, rfl⟩ := h₁
    obtain ⟨m₂, rfl⟩ := h₂
    exact ⟨m₁ + m₂, map_add φ m₁ m₂⟩

omit [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
include hφ in
lemma surjective_snd : Function.Surjective (snd φ ψ) := fun q ↦ by
  obtain ⟨p, hp⟩ := surjective_of_isBaseChange hφ (ψ q)
  exact ⟨⟨(p, q), hp⟩, rfl⟩

omit [Algebra R P] [IsScalarTower R S P] [Algebra R P₀] [Algebra (R ⧸ I) P₀] [IsScalarTower R S P₀]
  [IsScalarTower R (R ⧸ I) P₀] [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
include hφ in
/-- The kernel of `φ` is `I P`. -/
lemma mem_smul_top_of_eq_zero {p : P} (hp : φ p = 0) :
    p ∈ I.map (algebraMap R S) • (⊤ : Submodule S P) := by
  have h1 : (1 : S ⧸ I.map (algebraMap R S)) ⊗ₜ[S] p = 0 := by
    apply hφ.equiv.injective
    rw [IsBaseChange.equiv_tmul, one_smul, map_zero]
    exact hp
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul P (I.map (algebraMap R S))) h1
  rw [← map_one (Ideal.Quotient.mk (I.map (algebraMap R S))),
    TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul, map_zero,
    Submodule.Quotient.mk_eq_zero] at h2
  exact h2

omit [Algebra (S ⧸ I.map (algebraMap R S)) P₀] [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
/-- For `i ∈ I` and `p : P`, the pair `(i p, 0)` lies in the patched algebra. -/
lemma smul_mem_patch {i : R} (hi : i ∈ I) (p : P) : (i • p, (0 : Q)) ∈ patch φ ψ := by
  have h : φ (i • p) = i • φ p := map_smul (φ.restrictScalars R) i p
  rw [mem_patch, map_zero, h, ← algebraMap_smul (R ⧸ I) i (φ p),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hi, zero_smul]

/-- The element `(i p, 0)` of the patched algebra. -/
def smulElem {i : R} (hi : i ∈ I) (p : P) : patch φ ψ :=
  ⟨(i • p, 0), smul_mem_patch hi p⟩

include hφ hψ in
/-- **`P` is generated over `S` by the image of the patched algebra.** -/
lemma mem_span_range_fst (p : P) :
    p ∈ Submodule.span S (Set.range (fst φ ψ)) := by
  have hJ : I.map (algebraMap R S) • (⊤ : Submodule S P) ≤
      Submodule.span S (Set.range (fst φ ψ)) := by
    refine Submodule.smul_le.2 fun j hj p _ ↦ ?_
    induction hj using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rw [algebraMap_smul]
      exact Submodule.subset_span ⟨smulElem hi p, rfl⟩
    | zero => rw [zero_smul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul s x _ hx =>
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ s hx
  have hq : φ p ∈ Submodule.span (S ⧸ I.map (algebraMap R S)) (Set.range ψ) := by
    induction φ p using hψ.inductionOn with
    | zero => exact zero_mem _
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul s n hn => exact Submodule.smul_mem _ s hn
    | add n₁ n₂ h₁ h₂ => exact add_mem h₁ h₂
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hq
  -- lift the coefficients and the elements
  choose sl hsl using fun q : Q ↦ Ideal.Quotient.mk_surjective (c q)
  choose pl hpl using fun q : Q ↦ surjective_of_isBaseChange hφ (ψ q)
  let y : P := c.sum fun q _ ↦ sl q • pl q
  have hy : y ∈ Submodule.span S (Set.range (fst φ ψ)) := by
    refine Submodule.sum_mem _ fun q _ ↦ Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨⟨(pl q, q), hpl q⟩, rfl⟩
  have hφy : φ (p - y) = 0 := by
    rw [map_sub, sub_eq_zero, ← hc]
    simp only [y, Finsupp.sum, map_sum, map_smul]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hpl q, ← hsl q, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have := hJ (mem_smul_top_of_eq_zero hφ hφy)
  simpa using add_mem this hy

variable (hI : ∀ i ∈ I, ∀ s : S, ∃ r ∈ I, algebraMap R S r = algebraMap R S i * s)

variable (φ ψ) in
omit [Algebra (S ⧸ I.map (algebraMap R S)) P₀] [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
lemma algebraMap_eq_zero_of_mem {i : R} (hi : i ∈ I) : algebraMap R Q i = 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ I) Q, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 hi, map_zero]

include hφ hψ hI in
/-- **The kernel of `P ×_{P₀} Q → Q` is `I (P ×_{P₀} Q)`.** -/
lemma mem_smul_top_of_snd_eq_zero (x : patch φ ψ) (hx : snd φ ψ x = 0) :
    x ∈ I • (⊤ : Submodule R (patch φ ψ)) := by
  let C : P → Prop := fun p ↦ ∃ y ∈ I • (⊤ : Submodule R (patch φ ψ)),
    fst φ ψ y = p ∧ snd φ ψ y = 0
  have hC0 : C 0 := ⟨0, zero_mem _, map_zero _, map_zero _⟩
  have hCadd : ∀ a b, C a → C b → C (a + b) := by
    rintro a b ⟨y, hy, rfl, hy'⟩ ⟨z, hz, rfl, hz'⟩
    exact ⟨y + z, add_mem hy hz, map_add _ _ _, by rw [map_add, hy', hz', add_zero]⟩
  have hC : ∀ {i : R}, i ∈ I → ∀ p : P, C (i • p) := by
    intro i hi p
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_range_fst hφ hψ p)
    choose r hrI hr using fun y : patch φ ψ ↦ hI i hi (c y)
    refine ⟨c.sum fun y _ ↦ r y • y, Submodule.sum_mem _ fun y _ ↦
      Submodule.smul_mem_smul (hrI y) trivial, ?_, ?_⟩
    · rw [← hc, map_finsuppSum, Finsupp.smul_sum]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      change fst φ ψ (r y • y) = i • c y • fst φ ψ y
      rw [map_smul, ← algebraMap_smul S (r y), hr y, mul_smul, algebraMap_smul]
    · rw [map_finsuppSum]
      exact Finset.sum_eq_zero fun y _ ↦ by
        change snd φ ψ (r y • y) = 0
        rw [map_smul, Algebra.smul_def, algebraMap_eq_zero_of_mem (hrI y), zero_mul]
  have hp : φ (fst φ ψ x) = 0 := by rw [φ_fst, hx, map_zero]
  have key : ∀ p ∈ I.map (algebraMap R S) • (⊤ : Submodule S P), C p := by
    intro p hp
    refine Submodule.smul_induction_on hp (fun j hj n _ ↦ ?_) (fun a b ha hb ↦ hCadd a b ha hb)
    clear ‹n ∈ ⊤›
    induction hj using Submodule.span_induction generalizing n with
    | mem a ha =>
      obtain ⟨i, hi, rfl⟩ := ha
      rw [algebraMap_smul]
      exact hC hi n
    | zero => rw [zero_smul]; exact hC0
    | add a b _ _ ha hb => rw [add_smul]; exact hCadd _ _ (ha n) (hb n)
    | smul s a _ ha => rw [smul_eq_mul, mul_comm, mul_smul]; exact ha (s • n)
  obtain ⟨y, hy, h1, h2⟩ := key _ (mem_smul_top_of_eq_zero hφ hp)
  have : y = x := Subtype.ext (Prod.ext h1 (h2.trans hx.symm))
  rwa [← this]

include hφ hψ hI in
/-- **`P ×_{P₀} Q → Q` is the base change along `R → R ⧸ I`.** -/
theorem isBaseChange_snd : IsBaseChange (R ⧸ I) (snd φ ψ).toLinearMap := by
  have hker : LinearMap.ker (snd φ ψ).toLinearMap = I • (⊤ : Submodule R (patch φ ψ)) := by
    refine le_antisymm (fun x hx ↦ mem_smul_top_of_snd_eq_zero hφ hψ hI x hx) ?_
    refine Submodule.smul_le.2 fun i hi x _ ↦ ?_
    rw [LinearMap.mem_ker, map_smul, AlgHom.toLinearMap_apply, Algebra.smul_def,
      algebraMap_eq_zero_of_mem hi, zero_mul]
  let e : (R ⧸ I) ⊗[R] patch φ ψ ≃ₗ[R] Q :=
    (TensorProduct.quotTensorEquivQuotSMul (patch φ ψ) I).trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans
        ((snd φ ψ).toLinearMap.quotKerEquivOfSurjective (surjective_snd hφ)))
  refine IsBaseChange.of_equiv (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
    fun x ↦ ?_
  rw [LinearEquiv.extendScalarsOfSurjective_apply]
  simp only [e, LinearEquiv.trans_apply]
  rw [← map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rfl

section Fibre

variable (K : Type*) [Field K]

omit [Algebra (S ⧸ I.map (algebraMap R S)) P₀] [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
include hI in
/-- Fibres of the patched algebra away from `V(I)`. -/
lemma finrank_tensorProduct_of_notMem [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    {f : R} (hf : f ∈ I) (hfK : algebraMap S K (algebraMap R S f) ≠ 0) :
    finrank K (K ⊗[R] patch φ ψ) = finrank K (K ⊗[S] P) := by
  let u : patch φ ψ →ₗ[R] P := (fst φ ψ).toLinearMap
  let v : P →ₗ[R] patch φ ψ :=
    { toFun := fun p ↦ smulElem hf p
      map_add' := fun p p' ↦ Subtype.ext (Prod.ext (smul_add f p p') (add_zero 0).symm)
      map_smul' := fun r p ↦ Subtype.ext (Prod.ext (smul_comm f r p) (smul_zero r).symm) }
  have hu : IsUnit (algebraMap R K f) := by
    rw [IsScalarTower.algebraMap_apply R S K]
    exact hfK.isUnit
  have h₁ : v ∘ₗ u = f • LinearMap.id := by
    refine LinearMap.ext fun x ↦ Subtype.ext (Prod.ext rfl ?_)
    change (0 : Q) = f • x.1.2
    rw [Algebra.smul_def, algebraMap_eq_zero_of_mem hf, zero_mul]
  have e₁ := LinearEquiv.ofBijective (u.baseChange K)
    (bijective_baseChange_of_comp_eq_smul K u v f h₁ rfl hu)
  let w : S ⊗[R] P →ₗ[S] P := LinearMap.liftBaseChange S LinearMap.id
  have key (s : S) (p : P) : (1 : S) ⊗ₜ[R] (f • s • p) = (f • s) ⊗ₜ[R] p := by
    obtain ⟨r, -, hr⟩ := hI f hf s
    calc (1 : S) ⊗ₜ[R] (f • s • p) = (1 : S) ⊗ₜ[R] (r • p) := by
          rw [← algebraMap_smul S r p, hr, mul_smul, algebraMap_smul]
      _ = (r • (1 : S)) ⊗ₜ[R] p := (TensorProduct.smul_tmul r 1 p).symm
      _ = (f • s) ⊗ₜ[R] p := by rw [Algebra.smul_def, mul_one, hr, ← Algebra.smul_def]
  let v' : P →ₗ[S] S ⊗[R] P :=
    { toFun := fun p ↦ (1 : S) ⊗ₜ (f • p)
      map_add' := fun p p' ↦ by rw [smul_add, TensorProduct.tmul_add]
      map_smul' := fun s p ↦ by
        change (1 : S) ⊗ₜ[R] (f • s • p) = s • ((1 : S) ⊗ₜ[R] (f • p))
        rw [key, TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] }
  have h₁' : v' ∘ₗ w = algebraMap R S f • LinearMap.id := by
    refine TensorProduct.AlgebraTensorModule.ext fun s p ↦ ?_
    change (1 : S) ⊗ₜ[R] (f • s • p) = algebraMap R S f • (s ⊗ₜ[R] p)
    rw [key, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
  have h₂' : w ∘ₗ v' = algebraMap R S f • LinearMap.id := by
    refine LinearMap.ext fun p ↦ ?_
    change (1 : S) • f • p = algebraMap R S f • p
    rw [one_smul, algebraMap_smul]
  have e₂ := LinearEquiv.ofBijective (w.baseChange K)
    (bijective_baseChange_of_comp_eq_smul K w v' _ h₁' h₂' hfK.isUnit)
  rw [e₁.finrank_eq, ← (AlgebraTensorModule.cancelBaseChange R S K K P).finrank_eq,
    e₂.finrank_eq]

include hφ hψ hI in
/-- Fibres of the patched algebra over `V(I)`. -/
lemma finrank_tensorProduct_of_le [Algebra R K] [Algebra S K] [Algebra (R ⧸ I) K]
    [Algebra (S ⧸ I.map (algebraMap R S)) K]
    [IsScalarTower S (S ⧸ I.map (algebraMap R S)) K] [IsScalarTower R (R ⧸ I) K]
    [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) K] :
    finrank K (K ⊗[R] patch φ ψ) = finrank K (K ⊗[S] P) := by
  have h1 := (isBaseChange_snd hφ hψ hI).comp
    (hψ.comp (TensorProduct.isBaseChange (S ⧸ I.map (algebraMap R S)) P₀ K))
  have h2 := hφ.comp (TensorProduct.isBaseChange (S ⧸ I.map (algebraMap R S)) P₀ K)
  exact (h1.equiv.trans h2.equiv.symm).finrank_eq

end Fibre

include hφ hψ hI in
/-- **The fibres of the patched algebra are the fibres of `P`**: the fibre of `P ×_{P₀} Q` at
`q ∩ R` has the same dimension as the fibre of `P` at a prime `q` of `S`. -/
theorem finrank_fiber_patch (q : Ideal S) [q.IsPrime] :
    finrank (q.comap (algebraMap R S)).ResidueField
        ((q.comap (algebraMap R S)).Fiber (patch φ ψ)) =
      finrank q.ResidueField (q.Fiber P) := by
  set p := q.comap (algebraMap R S)
  letI : Algebra R q.ResidueField :=
    ((algebraMap S q.ResidueField).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S q.ResidueField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) rfl).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      (Ideal.ResidueField.map_algebraMap p q (algebraMap R S) rfl r).symm
  rw [← finrank_tensorProduct_eq_of_isScalarTower p.ResidueField q.ResidueField]
  by_cases hIp : I ≤ p
  · have hJ : ∀ a ∈ I.map (algebraMap R S), algebraMap S q.ResidueField a = 0 := fun a ha ↦
      Ideal.algebraMap_residueField_eq_zero.2 (Ideal.map_le_iff_le_comap.2 hIp ha)
    letI : Algebra (S ⧸ I.map (algebraMap R S)) q.ResidueField :=
      (Ideal.Quotient.lift _ (algebraMap S q.ResidueField) hJ).toAlgebra
    letI : Algebra (R ⧸ I) q.ResidueField :=
      ((algebraMap (S ⧸ I.map (algebraMap R S)) q.ResidueField).comp
        (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))).toAlgebra
    haveI : IsScalarTower S (S ⧸ I.map (algebraMap R S)) q.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower R (R ⧸ I) q.ResidueField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) q.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact finrank_tensorProduct_of_le hφ hψ hI _
  · obtain ⟨f, hfI, hfp⟩ := Set.not_subset.1 hIp
    refine finrank_tensorProduct_of_notMem hI _ hfI ?_
    rwa [ne_eq, Ideal.algebraMap_residueField_eq_zero]

include hφ hψ hI in
/-- **The patched algebra is flat**, for `R` reduced and `R → S` injective and integral. -/
theorem flat_patch [IsReduced R] [Module.Finite R (patch φ ψ)] [Module.Finite S P] [Module.Flat S P]
    (hinj : Function.Injective (algebraMap R S)) [Algebra.IsIntegral R S] :
    Module.Flat R (patch φ ψ) := by
  refine Module.flat_of_localized_maximal _ fun m _ ↦
    Module.flat_localizedModule_of_forall_finrank_fiber_eq m fun p _ hpm ↦ ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ p := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap R S)] at hx
    rw [hinj hx]
    exact zero_mem _
  obtain ⟨q, -, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p ⊥ hker
  obtain ⟨Q, hqQ, hQ, hQm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime m q
    (hqp ▸ hpm)
  subst hqp hQm
  rw [finrank_fiber_patch hφ hψ hI q, finrank_fiber_patch hφ hψ hI Q,
    Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_rankAtStalk]
  exact Module.rankAtStalk_eq_of_le_of_finite_of_flat' P hqQ

include hφ hψ hI in
/-- **`P ×_{P₀} Q → P` is the base change along `R → S`**, for `P ×_{P₀} Q` finite flat. -/
theorem isBaseChange_fst [Module.Finite R (patch φ ψ)] [Module.Flat R (patch φ ψ)]
    [Module.Finite S P] [Module.Flat S P] : IsBaseChange S (fst φ ψ).toLinearMap := by
  let F : S ⊗[R] patch φ ψ →ₗ[S] P := LinearMap.liftBaseChange S (fst φ ψ).toLinearMap
  have hsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    intro p _
    refine Submodule.span_le.2 ?_ (mem_span_range_fst hφ hψ p)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [F]⟩
  have hbij : Function.Bijective F :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hsurj fun m _ ↦
      (Module.rankAtStalk_baseChange _).trans
        ((Ideal.finrank_fiber_eq_rankAtStalk (m.comap (algebraMap R S))).symm.trans
          ((finrank_fiber_patch hφ hψ hI m).trans (Ideal.finrank_fiber_eq_rankAtStalk m)))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hbij) fun x ↦ by simp [F]

end BaseChange

/-- **The patched algebra is finite** over a noetherian ring. -/
theorem finite_patch [IsNoetherianRing R] [Module.Finite R P] [Module.Finite R Q] :
    Module.Finite R (patch φ ψ) :=
  Module.Finite.of_injective (patch φ ψ).val.toLinearMap Subtype.val_injective

/-- The fibres of `M` vanish if `S ⊗[R] M` does. -/
lemma finrank_tensorProduct_eq_zero (K : Type*) [Field K] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] {M : Type*} [AddCommGroup M] [Module R M] [Subsingleton (S ⊗[R] M)] :
    finrank K (K ⊗[R] M) = 0 := by
  haveI : Subsingleton (K ⊗[S] (S ⊗[R] M)) := by
    refine subsingleton_of_forall_eq 0 fun t ↦ ?_
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [← (AlgebraTensorModule.cancelBaseChange R S K K M).finrank_eq]
  exact Module.finrank_zero_of_subsingleton

/-- A finite `R`-module `M` with `S ⊗[R] M = 0` vanishes, for `R → S` injective and integral. -/
lemma subsingleton_of_subsingleton_tensorProduct (hinj : Function.Injective (algebraMap R S))
    [Algebra.IsIntegral R S] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Subsingleton (S ⊗[R] M)] : Subsingleton M := by
  refine Module.subsingleton_of_forall_isMaximal_tensor (A := R) fun m hm ↦
    ⟨m.ResidueField, inferInstance, inferInstance, fun y ↦ ?_, m.ker_algebraMap_residueField, ?_⟩
  · obtain ⟨x, rfl⟩ := m.bijective_algebraMap_quotient_residueField.2 y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨r, IsScalarTower.algebraMap_apply R (R ⧸ m) _ r⟩
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ m := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap R S)] at hx
    rw [hinj hx]
    exact zero_mem _
  obtain ⟨q, -, hq, hqm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m ⊥ hker
  letI : Algebra R q.ResidueField :=
    ((algebraMap S q.ResidueField).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S q.ResidueField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra m.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map m q (algebraMap R S) hqm.symm).toAlgebra
  haveI : IsScalarTower R m.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      (Ideal.ResidueField.map_algebraMap m q (algebraMap R S) hqm.symm r).symm
  have h0 : finrank m.ResidueField (m.ResidueField ⊗[R] M) = 0 := by
    rw [← Module.finrank_tensorProduct_eq_of_isScalarTower m.ResidueField q.ResidueField]
    exact finrank_tensorProduct_eq_zero (S := S) q.ResidueField
  exact Module.finrank_zero_iff.1 h0

section Etale

variable [Algebra (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀]
  (hφ : IsBaseChange (S ⧸ I.map (algebraMap R S)) (φ.toLinearMap))
  (hψ : IsBaseChange (S ⧸ I.map (algebraMap R S)) (ψ.toLinearMap))
  (hI : ∀ i ∈ I, ∀ s : S, ∃ r ∈ I, algebraMap R S r = algebraMap R S i * s)
  (hinj : Function.Injective (algebraMap R S))

variable (φ ψ) in
/-- The `S`-algebra map `S ⊗[R] (P ×_{P₀} Q) → P`. -/
def baseChangeFst : S ⊗[R] patch φ ψ →ₐ[S] P :=
  Algebra.TensorProduct.lift (Algebra.ofId S P) (fst φ ψ) fun _ _ ↦ Commute.all _ _

variable (φ ψ) in
/-- The `R ⧸ I`-algebra map `(R ⧸ I) ⊗[R] (P ×_{P₀} Q) → Q`. -/
def baseChangeSnd : (R ⧸ I) ⊗[R] patch φ ψ →ₐ[R ⧸ I] Q :=
  Algebra.TensorProduct.lift (Algebra.ofId (R ⧸ I) Q) (snd φ ψ) fun _ _ ↦ Commute.all _ _

variable (φ ψ) in
omit [Algebra (S ⧸ I.map (algebraMap R S)) P₀] [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
@[simp]
lemma baseChangeFst_tmul (s : S) (x : patch φ ψ) :
    baseChangeFst φ ψ (s ⊗ₜ x) = algebraMap S P s * fst φ ψ x :=
  rfl

variable (φ ψ) in
omit [Algebra (S ⧸ I.map (algebraMap R S)) P₀] [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
@[simp]
lemma baseChangeSnd_tmul (a : R ⧸ I) (x : patch φ ψ) :
    baseChangeSnd φ ψ (a ⊗ₜ x) = algebraMap (R ⧸ I) Q a * snd φ ψ x :=
  rfl

variable (φ ψ) in
omit [Algebra (S ⧸ I.map (algebraMap R S)) P₀] [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
lemma bijective_baseChangeFst (h : IsBaseChange S (fst φ ψ).toLinearMap) :
    Function.Bijective (baseChangeFst φ ψ) := by
  have : ⇑(baseChangeFst φ ψ) = ⇑h.equiv := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp [Algebra.smul_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact h.equiv.bijective

variable (φ ψ) in
omit [Algebra (S ⧸ I.map (algebraMap R S)) P₀] [IsScalarTower S (S ⧸ I.map (algebraMap R S)) P₀]
  [IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) P₀] in
lemma bijective_baseChangeSnd (h : IsBaseChange (R ⧸ I) (snd φ ψ).toLinearMap) :
    Function.Bijective (baseChangeSnd φ ψ) := by
  have : ⇑(baseChangeSnd φ ψ) = ⇑h.equiv := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp [Algebra.smul_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact h.equiv.bijective

include hφ hψ hI hinj in
/-- **Milnor patching of finite étale algebras.** Let `R → S` be injective and finite, with `R`
noetherian and reduced, and let `I ⊆ R` be an ideal of `S`. If `P` is finite étale over `S`, `Q`
is a finite `R ⧸ I`-algebra and `P ⧸ I P ≅ (S ⧸ I S) ⊗[R ⧸ I] Q` (as encoded by `φ` and `ψ`), then
`P ×_{P₀} Q` is finite étale over `R`, with `S ⊗[R] (P ×_{P₀} Q) ≅ P` and
`(R ⧸ I) ⊗[R] (P ×_{P₀} Q) ≅ Q` (`bijective_baseChangeFst`, `bijective_baseChangeSnd`). -/
theorem etale_patch [IsNoetherianRing R] [IsReduced R] [Module.Finite R S] [Module.Finite S P]
    [Module.Finite R P] [Module.Finite R Q] [Algebra.Etale S P] :
    Algebra.Etale R (patch φ ψ) ∧ Module.Finite R (patch φ ψ) ∧
      Function.Bijective (baseChangeFst φ ψ) ∧ Function.Bijective (baseChangeSnd φ ψ) := by
  haveI := finite_patch (φ := φ) (ψ := ψ)
  haveI := flat_patch hφ hψ hI hinj
  have hb := bijective_baseChangeFst φ ψ (isBaseChange_fst hφ hψ hI)
  refine ⟨?_, inferInstance, hb, bijective_baseChangeSnd φ ψ (isBaseChange_snd hφ hψ hI)⟩
  haveI : Algebra.FiniteType R (patch φ ψ) := .of_restrictScalars_finiteType R R _
  haveI : Algebra.FinitePresentation R (patch φ ψ) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Algebra.FormallyUnramified S (S ⊗[R] patch φ ψ) :=
    .of_equiv (AlgEquiv.ofBijective _ hb).symm
  haveI : Module.Finite (patch φ ψ) Ω[patch φ ψ⁄R] := KaehlerDifferential.finite R _
  haveI : Module.Finite R Ω[patch φ ψ⁄R] := Module.Finite.trans (patch φ ψ) _
  haveI : Subsingleton (S ⊗[R] Ω[patch φ ψ⁄R]) := Algebra.subsingleton_tensor_kaehlerDifferential S
  haveI : Subsingleton Ω[patch φ ψ⁄R] := subsingleton_of_subsingleton_tensorProduct hinj
  haveI : Algebra.FormallyUnramified R (patch φ ψ) := ⟨inferInstance⟩
  exact .of_formallyUnramified_of_flat

end Etale

end MilnorPatching
