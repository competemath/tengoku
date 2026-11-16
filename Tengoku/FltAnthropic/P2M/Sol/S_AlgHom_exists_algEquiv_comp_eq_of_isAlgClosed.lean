import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed

set_option maxHeartbeats 3200000

universe u v w

namespace W2G9

section Factorisation

variable {K : Type*} [Field K] {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {J : Type*} {A : J → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]

/--
@isnad1 id=eq.1h5v.s7.cd81fc4af451 from=translated src=- shape=6bced34f vocab=632e0116
-/
theorem single_mul_single_one [DecidableEq J] {j j' : J} (h : j ≠ j') (a : A j) :
    (Pi.single j a : Π j, A j) * Pi.single j' 1 = 0 := by
  funext k
  simp only [Pi.mul_apply, Pi.zero_apply]
  rcases eq_or_ne k j' with rfl | hk
  · rw [Pi.single_eq_of_ne (Ne.symm h), zero_mul]
  · rw [Pi.single_eq_of_ne hk, mul_zero]

def factorComponent [DecidableEq J] (φ : (Π j, A j) →ₐ[K] Ω) (j : J)
    (h1 : φ (Pi.single j 1) = 1) : A j →ₐ[K] Ω where
  toFun x := φ (Pi.single j x)
  map_one' := h1
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, h1]
    exact (Algebra.algebraMap_eq_smul_one r).symm

/--
@isnad1 id=ex.0h5v.s8.c6bf8352c59b from=translated src=- shape=4d1d7227 vocab=9580ddef
-/
theorem exists_factor_algHom [Finite J] [IsDomain Ω] (φ : (Π j, A j) →ₐ[K] Ω) :
    ∃ (j : J) (φ₀ : A j →ₐ[K] Ω), φ = φ₀.comp (Pi.evalAlgHom K A j) := by
  cases nonempty_fintype J
  classical

  have hidem : ∀ j, φ (Pi.single j 1) = 0 ∨ φ (Pi.single j 1) = 1 := by
    intro j
    have h2 : φ (Pi.single j 1) * φ (Pi.single j 1) = φ (Pi.single j 1) := by
      rw [← map_mul, ← Pi.single_mul, one_mul]
    have h3 : φ (Pi.single j 1) * (φ (Pi.single j 1) - 1) = 0 := by
      rw [mul_sub, h2, mul_one, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

  have hsum : (∑ j, φ (Pi.single j 1)) = 1 := by
    rw [← map_sum]
    have h1 : (∑ j, (Pi.single j 1 : Π j, A j)) = 1 := by
      simpa using Finset.univ_sum_single (1 : Π j, A j)
    rw [h1, map_one]
  have hex : ∃ j, φ (Pi.single j 1) = 1 := by
    by_contra hno
    have hall : ∀ j ∈ Finset.univ, φ (Pi.single (M := A) j 1) = 0 :=
      fun j _ => (hidem j).resolve_right fun h1 => hno ⟨j, h1⟩
    rw [Finset.sum_eq_zero hall] at hsum
    exact zero_ne_one hsum
  obtain ⟨j₀, h1⟩ := hex
  refine ⟨j₀, factorComponent φ j₀ h1, AlgHom.ext fun g => ?_⟩
  have hg : φ g = ∑ j, φ (Pi.single j (g j)) := by
    rw [← map_sum, Finset.univ_sum_single]
  have hzero : ∀ j ∈ Finset.univ, j ≠ j₀ → φ (Pi.single j (g j)) = 0 := by
    intro j _ hj
    have horth : φ (Pi.single j (g j)) * φ (Pi.single j₀ 1) = 0 := by
      rw [← map_mul, single_mul_single_one hj, map_zero]
    rwa [h1, mul_one] at horth
  calc φ g = ∑ j, φ (Pi.single j (g j)) := hg
  _ = φ (Pi.single j₀ (g j₀)) :=
      Finset.sum_eq_single j₀ hzero (fun h => absurd (Finset.mem_univ j₀) h)
  _ = (factorComponent φ j₀ h1).comp (Pi.evalAlgHom K A j₀) g := rfl

end Factorisation

section SplitPoints

variable (K : Type*) [Field K] (Ω : Type*) [CommRing Ω] [Algebra K Ω]
variable {ι : Type*}

def piPoint (i : ι) : (ι → K) →ₐ[K] Ω :=
  (Algebra.ofId K Ω).comp (Pi.evalAlgHom K (fun _ => K) i)

/--
@isnad1 id=eq.0h5v.s7.e817ce314702 from=translated src=- shape=9cbf20c6 vocab=89cb64c3
-/
@[scoped simp] theorem piPoint_apply (i : ι) (g : ι → K) :
    piPoint K Ω i g = algebraMap K Ω (g i) := rfl

/--
@isnad1 id=injectiv.0h3v.s6.f9d37600d3d7 from=translated src=- shape=0a3bfc6f vocab=773acc5a
-/
theorem piPoint_injective [Nontrivial Ω] :
    Function.Injective (piPoint K Ω (ι := ι)) := by
  intro i i' h
  by_contra hne
  classical
  have happ := DFunLike.congr_fun h (Pi.single i 1)
  rw [piPoint_apply, piPoint_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hne), map_one, map_zero] at happ
  exact one_ne_zero happ

/--
@isnad1 id=ex.0h4v.s7.8935c05810f3 from=translated src=- shape=e5a8a51e vocab=f48352f5
-/
theorem algHom_pi_eq_piPoint [Finite ι] [IsDomain Ω] (φ : (ι → K) →ₐ[K] Ω) :
    ∃ i, φ = piPoint K Ω i := by
  obtain ⟨i, φ₀, hφ⟩ := exists_factor_algHom (A := fun _ : ι => K) φ
  refine ⟨i, hφ.trans ?_⟩
  congr 1
  exact AlgHom.ext fun x => φ₀.commutes x

noncomputable def splitPointsEquiv [Finite ι] [IsDomain Ω] :
    ι ≃ ((ι → K) →ₐ[K] Ω) :=
  Equiv.ofBijective (piPoint K Ω)
    ⟨piPoint_injective K Ω,
     fun φ => (algHom_pi_eq_piPoint K Ω φ).imp fun _ h => h.symm⟩

end SplitPoints

section Faithfulness

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

end Faithfulness

section RangeRealization

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
variable {L : Type*} [CommRing L] [Algebra K L]
variable {M : Type*} [Field M] [Algebra K M]

noncomputable def homOfRangeLe (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (h : ∀ x, ∃ y, χ y = β x) : L →ₐ[K] M where
  toFun x := (h x).choose
  map_one' := χ.toRingHom.injective
    (show χ (h 1).choose = χ 1 from
      ((h 1).choose_spec.trans (map_one β)).trans (map_one χ).symm)
  map_mul' x y := χ.toRingHom.injective
    (show χ (h (x * y)).choose = χ ((h x).choose * (h y).choose) from
      (((h (x * y)).choose_spec.trans (map_mul β x y)).trans
        (congrArg₂ (· * ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_mul χ _ _).symm)
  map_zero' := χ.toRingHom.injective
    (show χ (h 0).choose = χ 0 from
      ((h 0).choose_spec.trans (map_zero β)).trans (map_zero χ).symm)
  map_add' x y := χ.toRingHom.injective
    (show χ (h (x + y)).choose = χ ((h x).choose + (h y).choose) from
      (((h (x + y)).choose_spec.trans (map_add β x y)).trans
        (congrArg₂ (· + ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_add χ _ _).symm)
  commutes' r := χ.toRingHom.injective
    (show χ (h (algebraMap K L r)).choose = χ (algebraMap K M r) from
      ((h (algebraMap K L r)).choose_spec.trans (β.commutes r)).trans (χ.commutes r).symm)

end RangeRealization

section Conjugacy

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

/--
@isnad1 id=ex.0h5v.s8.fbb0f842e184 from=translated src=- shape=0d2b96ad vocab=0e635d29
-/
theorem exists_algEquiv_comp_eq {M : Type*} [Field M] [Algebra K M]
    (σ τ : M →ₐ[K] Ω) : ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by
  letI : Algebra M Ω := σ.toRingHom.toAlgebra
  haveI : IsScalarTower K M Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := K) (L := M) (M := Ω) (E := Ω) τ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  refine ⟨AlgEquiv.ofBijective φ (AlgHom.normal_bijective K Ω Ω φ),
    AlgHom.ext fun m => ?_⟩
  exact DFunLike.congr_fun hφ m

end Conjugacy

section FixedField

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

end FixedField

section ProductDescent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

end ProductDescent

section EtaleDescent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

end EtaleDescent

section AbsoluteGalois

end AbsoluteGalois

end W2G9
open scoped _root_.P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed.W2G9

/--
@isnad1 id=ex.0h5v.s8.fbb0f842e184 from=translated src=- shape=0d2b96ad vocab=0e635d29
-/
theorem solution
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {M : Type*} [Field M] [Algebra K M] (σ τ : M →ₐ[K] Ω) :
    ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ :=
  W2G9.exists_algEquiv_comp_eq σ τ
