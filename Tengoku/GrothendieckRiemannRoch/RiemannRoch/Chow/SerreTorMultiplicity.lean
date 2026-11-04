/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
import Tengoku.Seed.Algebra.Category.ModuleCat.Monoidal.Closed
import Tengoku.Seed.Algebra.Category.ModuleCat.Projective
import Tengoku.Seed.CategoryTheory.Monoidal.Tor
import Tengoku.Seed.RingTheory.Length
import Tengoku.Seed.RingTheory.QuotSMulTop
import Tengoku.Seed.RingTheory.Regular.Category

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Serre--Tor multiplicities

This file supplies the commutative-algebra carrier needed for general scheme-theoretic
intersection multiplicities: the categorical Tor modules of two modules over a commutative ring,
their module lengths, and the finite alternating Euler sum when the Tor groups have finite length
and bounded amplitude.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Chow.SerreTor

variable (A : Type u) [CommRing A]

private noncomputable def zeroResolutionSuccessor
    {X₀ X₁ : ModuleCat.{u} A} (f : X₁ ⟶ X₀) :
    Σ' (X₂ : ModuleCat.{u} A) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
  ⟨ModuleCat.of A (Fin 0 → A), 0, by simp⟩

/-- The two-term free complex `0 → A →ᵃ A` used to resolve a principal quotient.-/
noncomputable def principalQuotientComplex (a : A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.mk' (ModuleCat.of A A) (ModuleCat.of A A)
    (ModuleCat.ofHom (LinearMap.lsmul A A a))
    (zeroResolutionSuccessor A)

/-- Every term of the principal quotient complex in degree at least two is zero.
@isnad1 id=iszero.0h3v.s6.f4096de8c9bf from=translated src=- shape=7b28cb01 vocab=7d2303d3
-/
theorem principalQuotientComplex_isZero (a : A) (n : ℕ) :
    IsZero ((principalQuotientComplex A a).X (n + 2)) := by
  let Z := ModuleCat.of A (Fin 0 → A)
  have hZ : IsZero Z :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (inferInstance : Subsingleton (Fin 0 → A))
  apply IsZero.of_iso hZ
  exact ChainComplex.mk'XIso (ModuleCat.of A A) (ModuleCat.of A A)
    (ModuleCat.ofHom (LinearMap.lsmul A A a))
    (zeroResolutionSuccessor A) n

/-- Augmentation of the principal two-term complex onto `A/aA`.-/
noncomputable def principalQuotientAugmentation (a : A) :
    principalQuotientComplex A a ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (QuotSMulTop a A)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨
    (ModuleCat.smulShortComplex (ModuleCat.of A A) a).g, by
      change (ModuleCat.smulShortComplex (ModuleCat.of A A) a).f ≫
        (ModuleCat.smulShortComplex (ModuleCat.of A A) a).g = 0
      exact (ModuleCat.smulShortComplex (ModuleCat.of A A) a).zero⟩

/-- If multiplication by `a` is injective, the principal quotient complex is exact in every
positive degree.
@isnad1 id=exactat.1h3v.s6.f8b87b441fc7 from=translated src=- shape=172774e5 vocab=01574a01
-/
theorem principalQuotientComplex_exactAt_succ (a : A)
    (reg : IsSMulRegular (ModuleCat.of A A) a) (n : ℕ) :
    (principalQuotientComplex A a).ExactAt (n + 1) := by
  obtain _ | n := n
  · rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    apply (ShortComplex.exact_iff_mono _
      ((principalQuotientComplex_isZero A a 0).eq_of_src _ _)).2
    change Mono (ModuleCat.smulShortComplex (ModuleCat.of A A) a).f
    exact reg.smulShortComplex_shortExact.mono_f
  · exact HomologicalComplex.ExactAt.of_isZero
      (principalQuotientComplex_isZero A a n)

/-- The canonical two-term projective resolution of `A/aA` for a regular principal element.-/
noncomputable def principalQuotientResolution (a : A)
    (reg : IsSMulRegular (ModuleCat.of A A) a) :
    ProjectiveResolution (ModuleCat.of A (QuotSMulTop a A)) where
  complex := principalQuotientComplex A a
  projective n := by
    obtain _ | _ | n := n
    · change Projective (ModuleCat.of A A)
      infer_instance
    · change Projective (ModuleCat.of A A)
      infer_instance
    · exact IsZero.projective (principalQuotientComplex_isZero A a n)
  π := principalQuotientAugmentation A a
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨ModuleCat.smulShortComplex_exact (ModuleCat.of A A) a, by infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp only [Category.id_comp, Category.comp_id]; rfl)
          (by simp only [Category.id_comp, Category.comp_id]; rfl)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply principalQuotientComplex_exactAt_succ A a reg
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-- If `a` is also regular on `M`, tensoring the principal quotient complex by `M` remains exact
in every positive degree. This is the chain-level source of Tor-independence for a proper
principal intersection.
@isnad1 id=exactat.1h4v.s8.6dcc7a927840 from=translated src=- shape=def17098 vocab=e91c2aa4
-/
theorem tensorPrincipalQuotientComplex_exactAt_succ (a : A)
    (M : ModuleCat.{u} A) (reg : IsSMulRegular M a) (n : ℕ) :
    ((((tensoringLeft (ModuleCat.{u} A)).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (principalQuotientComplex A a)).ExactAt (n + 1) := by
  let F := (tensoringLeft (ModuleCat.{u} A)).obj M
  obtain _ | n := n
  · rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    apply (ShortComplex.exact_iff_mono _
      ((F.map_isZero (principalQuotientComplex_isZero A a 0)).eq_of_src _ _)).2
    change Mono (F.map (ModuleCat.ofHom (LinearMap.lsmul A A a)))
    have hcomm :
        F.map (ModuleCat.ofHom (LinearMap.lsmul A A a)) ≫
            (MonoidalCategory.rightUnitor M).hom =
          (MonoidalCategory.rightUnitor M).hom ≫
            ModuleCat.ofHom (LinearMap.lsmul A M a) := by
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m r
      simp [F]
      change (a * r) • m = a • r • m
      rw [smul_smul]
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have hρ : Function.Injective (MonoidalCategory.rightUnitor M).hom :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.1
    have hmul : Function.Injective
        (ModuleCat.ofHom (LinearMap.lsmul A M a)).hom := by
      change Function.Injective (LinearMap.lsmul A M a)
      exact reg
    apply hρ
    apply hmul
    calc
      _ = (MonoidalCategory.rightUnitor M).hom
          (F.map (ModuleCat.ofHom (LinearMap.lsmul A A a)) x) :=
        (ConcreteCategory.congr_hom hcomm x).symm
      _ = (MonoidalCategory.rightUnitor M).hom
          (F.map (ModuleCat.ofHom (LinearMap.lsmul A A a)) y) :=
        congrArg (MonoidalCategory.rightUnitor M).hom hxy
      _ = _ := ConcreteCategory.congr_hom hcomm y
  · exact HomologicalComplex.ExactAt.of_isZero
      (F.map_isZero (principalQuotientComplex_isZero A a n))

/-- The `n`th Tor module of two `A`-modules, obtained by left-deriving tensor product in the
second variable.-/
noncomputable def module (M N : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  ((CategoryTheory.Tor (ModuleCat.{u} A) n).obj M).obj N

/-- The possibly infinite module length of the `n`th Tor module.-/
noncomputable def length (M N : ModuleCat.{u} A) (n : ℕ) : ℕ∞ :=
  Module.length A (module A M N n)

/-- Degree-zero Tor is canonically the ordinary tensor product.-/
noncomputable def zeroIsoTensor (M N : ModuleCat.{u} A) :
    module A M N 0 ≅ M ⊗ N :=
  (((tensoringLeft (ModuleCat.{u} A)).obj M).leftDerivedZeroIsoSelf).app N

/-- Degree-zero Tor and the ordinary tensor product have the same module length.
@isnad1 id=eq.0h3v.s6.f85c433ae65d from=translated src=- shape=84a73694 vocab=946dbfd3
-/
theorem length_zero_eq_tensor (M N : ModuleCat.{u} A) :
    length A M N 0 =
      Module.length A ((M ⊗ N : ModuleCat.{u} A) : Type u) :=
  (zeroIsoTensor A M N).toLinearEquiv.length_eq

/-- The length of a zero Tor object is zero.
@isnad1 id=eq.1h4v.s5.1536d472e15a from=translated src=- shape=7fc89624 vocab=fb5f2b76
-/
theorem length_eq_zero_of_isZero (M N : ModuleCat.{u} A) (n : ℕ)
    (h : IsZero (module A M N n)) : length A M N n = 0 := by
  rw [length, Module.length_eq_zero_iff]
  exact ModuleCat.isZero_iff_subsingleton.mp h

/-- The signed integer length occurring in the Serre intersection Euler characteristic.-/
noncomputable def signedLength (M N : ModuleCat.{u} A) (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (length A M N n).toNat

/-- A zero Tor object contributes zero to the signed Euler characteristic.
@isnad1 id=eq.1h4v.s5.4ee102c9fb24 from=translated src=- shape=7fc89624 vocab=16c3d7e8
-/
theorem signedLength_eq_zero_of_isZero (M N : ModuleCat.{u} A) (n : ℕ)
    (h : IsZero (module A M N n)) : signedLength A M N n = 0 := by
  rw [signedLength, length_eq_zero_of_isZero A M N n h]
  simp

/-- Finiteness and bounded-amplitude data making the alternating Tor-length sum well defined.
The bound is proof data only: `multiplicity_eq` below shows that the resulting integer is
independent of its choice.-/
structure EulerData (M N : ModuleCat.{u} A) where
  /-- A degree above which all Tor modules vanish.-/
  bound : ℕ
  /-- Every Tor module through the bound has finite length.-/
  finiteLength : ∀ n ≤ bound, length A M N n ≠ ⊤
  /-- Every Tor module above the bound is zero.-/
  vanishes : ∀ n, bound < n → IsZero (module A M N n)

namespace EulerData

variable {M N : ModuleCat.{u} A}

/-- The Serre--Tor multiplicity, as the finite alternating sum of Tor-module lengths.-/
noncomputable def multiplicity (d : EulerData A M N) : ℤ :=
  ∑ n ∈ Finset.range (d.bound + 1), signedLength A M N n

/-- Extending a valid amplitude bound only adds zero terms.  Consequently the multiplicity is
independent of every proof-level choice in `EulerData`.
@isnad1 id=eq.0h5v.s5.b3f7c68e4831 from=translated src=- shape=834460b6 vocab=d32a4a75
-/
theorem multiplicity_eq (d e : EulerData A M N) : d.multiplicity = e.multiplicity := by
  unfold multiplicity
  rcases le_total d.bound e.bound with hde | hed
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hde))
    intro n hnE hnD
    rw [signedLength_eq_zero_of_isZero A M N n]
    apply d.vanishes n
    simp only [Finset.mem_range] at hnD hnE
    omega
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hed))
    intro n hnD hnE
    rw [signedLength_eq_zero_of_isZero A M N n]
    apply e.vanishes n
    simp only [Finset.mem_range] at hnE hnD
    omega

end EulerData

/-- An explicit projective resolution whose terms vanish above a specified degree. This is the
constructive finite-Tor-amplitude input: unlike an abstract projective-dimension inequality, it
can be consumed directly by the frozen base's `isoLeftDerivedObj` comparison.-/
structure BoundedProjectiveResolution (N : ModuleCat.{u} A) where
  /-- A chosen projective resolution.-/
  resolution : ProjectiveResolution N
  /-- The last degree in which the resolution may be nonzero.-/
  bound : ℕ
  /-- Resolution terms above the bound vanish.-/
  isZero : ∀ n, bound < n → IsZero (resolution.complex.X n)

namespace BoundedProjectiveResolution

variable {M N : ModuleCat.{u} A}

/-- Transport a bounded projective resolution across an isomorphism of its resolved object. The
complex and its bound are unchanged; only the augmentation is postcomposed with the degree-zero
single-complex image of the isomorphism.-/
noncomputable def ofIso (d : BoundedProjectiveResolution A N)
    {N' : ModuleCat.{u} A} (e : N ≅ N') : BoundedProjectiveResolution A N' where
  resolution :=
    { complex := d.resolution.complex
      projective := d.resolution.projective
      π := d.resolution.π ≫ (ChainComplex.single₀ (ModuleCat.{u} A)).map e.hom }
  bound := d.bound
  isZero := d.isZero

/-- Multiplication by a regular principal element gives a projective resolution concentrated in
degrees zero and one.-/
noncomputable def principalQuotient (a : A)
    (reg : IsSMulRegular (ModuleCat.of A A) a) :
    BoundedProjectiveResolution A (ModuleCat.of A (QuotSMulTop a A)) where
  resolution := principalQuotientResolution A a reg
  bound := 1
  isZero n hn := by
    obtain _ | _ | n := n
    · omega
    · omega
    · exact principalQuotientComplex_isZero A a n

/-- Homology of a module-valued complex has finite length whenever its middle complex term does:
cycles embed into that term and surject onto homology.
@isnad1 id=ne.1h3v.s8.d28fd8e2f5b6 from=translated src=- shape=7e969cdf vocab=0b76d9bb
-/
theorem homology_length_ne_top_of_X
    (K : HomologicalComplex (ModuleCat.{u} A) (ComplexShape.down ℕ)) (n : ℕ)
    (h : Module.length A (↑(K.X n) : Type u) ≠ ⊤) :
    Module.length A (↑(K.homology n) : Type u) ≠ ⊤ := by
  rw [Module.length_ne_top_iff] at h ⊢
  exact (h.of_injective
    ((ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance)).of_surjective
      ((ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance)

/-- Tensoring an explicit bounded projective resolution computes zero Tor above its bound.
@isnad1 id=iszero.1h5v.s5.e666ad845f6c from=translated src=- shape=590192cb vocab=bbf64cfc
-/
theorem isZero_module (d : BoundedProjectiveResolution A N) (M : ModuleCat.{u} A)
    (n : ℕ) (hn : d.bound < n) : IsZero (module A M N n) := by
  change IsZero
    (((((tensoringLeft (ModuleCat.{u} A)).obj M).leftDerived n).obj N))
  refine IsZero.of_iso ?_
    (d.resolution.isoLeftDerivedObj ((tensoringLeft (ModuleCat.{u} A)).obj M) n)
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _
    (((tensoringLeft (ModuleCat.{u} A)).obj M).map_isZero (d.isZero n hn))

/-- Finite length of the `n`th term after tensoring a chosen projective resolution implies
finite length of the `n`th Tor module computed by that resolution.
@isnad1 id=ne.1h5v.s9.87436b7c52c7 from=translated src=- shape=756770d6 vocab=1a8b2109
-/
theorem length_ne_top_of_term (d : BoundedProjectiveResolution A N)
    (M : ModuleCat.{u} A) (n : ℕ)
    (hterm : Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj M).obj
        (d.resolution.complex.X n)) : Type u) ≠ ⊤) :
    length A M N n ≠ ⊤ := by
  change Module.length A
    (↑(((((tensoringLeft (ModuleCat.{u} A)).obj M).leftDerived n).obj N)) : Type u) ≠ ⊤
  rw [(d.resolution.isoLeftDerivedObj
      ((tensoringLeft (ModuleCat.{u} A)).obj M) n).toLinearEquiv.length_eq]
  exact homology_length_ne_top_of_X A
    (((tensoringLeft (ModuleCat.{u} A)).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ) |>.obj d.resolution.complex) n hterm

/-- A bounded projective resolution plus finite length in its finitely many possible homological
degrees gives canonical Serre--Tor Euler data. The high-degree vanishing proof is discharged by
the resolution rather than supplied independently by the caller.-/
noncomputable def toEulerData (d : BoundedProjectiveResolution A N)
    (M : ModuleCat.{u} A)
    (finiteLength : ∀ n ≤ d.bound, length A M N n ≠ ⊤) : EulerData A M N where
  bound := d.bound
  finiteLength := finiteLength
  vanishes n hn := isZero_module A d M n hn

/-- If the finitely many potentially nonzero terms of the tensor-applied resolution have finite
length, both finite length of Tor and high-degree vanishing are automatic.-/
noncomputable def toEulerDataOfFiniteTerms (d : BoundedProjectiveResolution A N)
    (M : ModuleCat.{u} A)
    (finiteTerm : ∀ n ≤ d.bound, Module.length A
      (↑(((tensoringLeft (ModuleCat.{u} A)).obj M).obj
        (d.resolution.complex.X n)) : Type u) ≠ ⊤) : EulerData A M N :=
  d.toEulerData A M (fun n hn ↦ d.length_ne_top_of_term A M n (finiteTerm n hn))

/-- A regular principal quotient has no Tor in degrees at least two.
@isnad1 id=iszero.1h4v.s10.7a42cfdaaefa from=translated src=- shape=843eb0a2 vocab=148e01e9
-/
theorem isZero_module_principalQuotient (a : A)
    (reg : IsSMulRegular (ModuleCat.of A A) a) (M : ModuleCat.{u} A) (n : ℕ) :
    IsZero (module A M (ModuleCat.of A (QuotSMulTop a A)) (n + 2)) := by
  apply (principalQuotient A a reg).isZero_module A M
  change 1 < n + 2
  omega

/-- If the principal equation is regular both on the ring and on the first module, every
positive Tor with the principal quotient vanishes.
@isnad1 id=iszero.2h4v.s10.de3f074f24db from=translated src=- shape=8b946610 vocab=148e01e9
-/
theorem isZero_module_principalQuotient_of_isSMulRegular (a : A)
    (regA : IsSMulRegular (ModuleCat.of A A) a) (M : ModuleCat.{u} A)
    (regM : IsSMulRegular M a) (n : ℕ) :
    IsZero (module A M (ModuleCat.of A (QuotSMulTop a A)) (n + 1)) := by
  change IsZero
    (((((tensoringLeft (ModuleCat.{u} A)).obj M).leftDerived (n + 1)).obj
      (ModuleCat.of A (QuotSMulTop a A))))
  refine IsZero.of_iso ?_
    ((principalQuotientResolution A a regA).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat.{u} A)).obj M) (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact tensorPrincipalQuotientComplex_exactAt_succ A a M regM n

/-- The positive-Tor vanishing theorem is unchanged after identifying the principal quotient
with any isomorphic target module.
@isnad1 id=iszero.2h6v.s10.406d97182fac from=translated src=- shape=a50b50da vocab=2b1caa84
-/
theorem isZero_module_of_iso_principalQuotient_of_isSMulRegular (a : A)
    (regA : IsSMulRegular (ModuleCat.of A A) a) (M : ModuleCat.{u} A)
    (regM : IsSMulRegular M a) {N' : ModuleCat.{u} A}
    (e : ModuleCat.of A (QuotSMulTop a A) ≅ N') (n : ℕ) :
    IsZero (module A M N' (n + 1)) := by
  let resolution := (principalQuotient A a regA).ofIso A e
  change IsZero
    (((((tensoringLeft (ModuleCat.{u} A)).obj M).leftDerived (n + 1)).obj N'))
  refine IsZero.of_iso ?_
    (resolution.resolution.isoLeftDerivedObj
      ((tensoringLeft (ModuleCat.{u} A)).obj M) (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact tensorPrincipalQuotientComplex_exactAt_succ A a M regM n

/-- Finite length of `M` is enough to construct all Serre--Tor Euler data against a regular
principal quotient: both nonzero resolution terms are copies of `A`.-/
noncomputable def principalQuotientEulerData (a : A)
    (reg : IsSMulRegular (ModuleCat.of A A) a) (M : ModuleCat.{u} A)
    (hM : Module.length A (↑M : Type u) ≠ ⊤) :
    EulerData A M (ModuleCat.of A (QuotSMulTop a A)) :=
  (principalQuotient A a reg).toEulerDataOfFiniteTerms A M (fun n hn ↦ by
    change n ≤ 1 at hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · change Module.length A (TensorProduct A (↑M : Type u) A) ≠ ⊤
      rwa [(TensorProduct.rid A (↑M : Type u)).length_eq]
    · change Module.length A (TensorProduct A (↑M : Type u) A) ≠ ⊤
      rwa [(TensorProduct.rid A (↑M : Type u)).length_eq])

/-- For a regular principal quotient, the Euler characteristic is the degree-zero Tor length
minus the degree-one Tor length; all higher terms vanish by the explicit resolution.
@isnad1 id=eq.2h3v.s11.1f021d5b40e1 from=translated src=- shape=55fd5bac vocab=cc82d7dc
-/
theorem principalQuotientEulerData_multiplicity (a : A)
    (reg : IsSMulRegular (ModuleCat.of A A) a) (M : ModuleCat.{u} A)
    (hM : Module.length A (↑M : Type u) ≠ ⊤) :
    (principalQuotientEulerData A a reg M hM).multiplicity =
      (length A M (ModuleCat.of A (QuotSMulTop a A)) 0).toNat -
        (length A M (ModuleCat.of A (QuotSMulTop a A)) 1).toNat := by
  simp [principalQuotientEulerData, toEulerDataOfFiniteTerms, toEulerData,
    principalQuotient, EulerData.multiplicity, signedLength, Finset.sum_range_succ,
    sub_eq_add_neg]

end BoundedProjectiveResolution

/-- Tor-independent modules with finite tensor-product length have canonical Euler data of
amplitude zero.-/
noncomputable def eulerDataOfTorIndependent (M N : ModuleCat.{u} A)
    (hzero : Module.length A ((M ⊗ N : ModuleCat.{u} A) : Type u) ≠ ⊤)
    (hTor : ∀ n : ℕ, IsZero (module A M N (n + 1))) : EulerData A M N where
  bound := 0
  finiteLength n hn := by
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    rwa [length_zero_eq_tensor]
  vanishes n hn := by
    cases n with
    | zero => omega
    | succ m => simpa only [Nat.succ_eq_add_one] using hTor m

/-- A proper regular principal intersection has amplitude-zero Euler data: regularity on the
first module kills every positive Tor, while finite length of the ordinary tensor product
supplies the only nonzero length.-/
noncomputable def eulerDataPrincipalQuotientOfRegular (a : A)
    (regA : IsSMulRegular (ModuleCat.of A A) a) (M : ModuleCat.{u} A)
    (regM : IsSMulRegular M a)
    (hzero : Module.length A
      (↑(M ⊗ ModuleCat.of A (QuotSMulTop a A)) : Type u) ≠ ⊤) :
    EulerData A M (ModuleCat.of A (QuotSMulTop a A)) :=
  eulerDataOfTorIndependent A M _ hzero
    (BoundedProjectiveResolution.isZero_module_principalQuotient_of_isSMulRegular
      A a regA M regM)

/-- Isomorphic copies of a regular principal quotient have the same amplitude-zero Euler-data
construction. This is the form consumed by geometric stalk identifications.-/
noncomputable def eulerDataOfIsoPrincipalQuotientOfRegular (a : A)
    (regA : IsSMulRegular (ModuleCat.of A A) a) (M : ModuleCat.{u} A)
    (regM : IsSMulRegular M a) {N' : ModuleCat.{u} A}
    (e : ModuleCat.of A (QuotSMulTop a A) ≅ N')
    (hzero : Module.length A (↑(M ⊗ N') : Type u) ≠ ⊤) :
    EulerData A M N' :=
  eulerDataOfTorIndependent A M N' hzero
    (BoundedProjectiveResolution.isZero_module_of_iso_principalQuotient_of_isSMulRegular
      A a regA M regM e)

/-- If the second module is projective, its higher Tor groups vanish automatically, so finite
tensor-product length alone supplies amplitude-zero Euler data.-/
noncomputable def eulerDataOfProjective (M N : ModuleCat.{u} A) [Projective N]
    (hzero : Module.length A ((M ⊗ N : ModuleCat.{u} A) : Type u) ≠ ⊤) :
    EulerData A M N :=
  eulerDataOfTorIndependent A M N hzero
    (fun n ↦ CategoryTheory.isZero_Tor_succ_of_projective
      (ModuleCat.{u} A) M N n)

/-- Under Tor independence, the Serre multiplicity collapses to the ordinary tensor-product
length.
@isnad1 id=eq.2h3v.s7.be6894233c37 from=translated src=- shape=f797ac27 vocab=84b3b1e3
-/
theorem eulerDataOfTorIndependent_multiplicity
    (M N : ModuleCat.{u} A)
    (hzero : Module.length A ((M ⊗ N : ModuleCat.{u} A) : Type u) ≠ ⊤)
    (hTor : ∀ n : ℕ, IsZero (module A M N (n + 1))) :
    (eulerDataOfTorIndependent A M N hzero hTor).multiplicity =
      (Module.length A ((M ⊗ N : ModuleCat.{u} A) : Type u)).toNat := by
  simp [EulerData.multiplicity, eulerDataOfTorIndependent, signedLength,
    length_zero_eq_tensor]

/-- In the projective-factor case, the Serre multiplicity is the tensor-product length.
@isnad1 id=eq.1h3v.s7.62c53185c95f from=translated src=- shape=68dd5400 vocab=a0a8e524
-/
theorem eulerDataOfProjective_multiplicity
    (M N : ModuleCat.{u} A) [Projective N]
    (hzero : Module.length A ((M ⊗ N : ModuleCat.{u} A) : Type u) ≠ ⊤) :
    (eulerDataOfProjective A M N hzero).multiplicity =
      (Module.length A ((M ⊗ N : ModuleCat.{u} A) : Type u)).toNat := by
  apply eulerDataOfTorIndependent_multiplicity

end AlgebraicGeometry.Chow.SerreTor
