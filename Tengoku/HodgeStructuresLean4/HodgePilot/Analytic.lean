import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.FiniteType
import Tengoku.Seed.RingTheory.Spectrum.Prime.Topology
import Tengoku.Seed.AlgebraicGeometry.GammaSpecAdjunction
import Tengoku.Seed.Topology.ContinuousMap.Algebra
import Tengoku.Seed.Analysis.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The analytic topology on the ℂ-points of an affine scheme

For a commutative ℂ-algebra `A`, the ℂ-points of `Spec A` form the set
`CPoints A := A →ₐ[ℂ] ℂ` of ℂ-algebra homomorphisms `A → ℂ`.  This file
equips `CPoints A` with its *analytic* (euclidean) topology, defined
presentation-freely as the topology of pointwise evaluation: the initial
topology of the injection `CPoints A ↪ (A → ℂ)` into the full product
(`instTopCPoints`, `isEmbedding_toPi`).

The classical construction instead chooses a presentation
`A ≃ ℂ[x_i]/I` and embeds the points into `ℂⁿ`; the resulting topology is
then shown not to depend on the presentation.  Here the independence
statement is a *theorem* about the presentation-free definition:

* `isEmbedding_evalGen` — **presentation independence**: for any generating
  family `g : ι → A` of the ℂ-algebra `A`, evaluation at the generators
  alone, `φ ↦ (φ (g i))_i`, is a topological embedding
  `CPoints A ↪ (ι → ℂ)`.  (Proof: every element of `A` is a polynomial in
  the generators, and polynomial maps `ℂ^ι → ℂ` are continuous.)
* `mvPolynomialHomeomorph` — for affine space itself the embedding is a
  homeomorphism `𝔸ⁿ(ℂ) ≃ₜ ℂⁿ`: `CPoints (MvPolynomial σ ℂ) ≃ₜ (σ → ℂ)`.
* `comap`, `continuous_comap`, `comap_id`, `comap_comp` — contravariant
  functoriality: an algebra map `A →ₐ[ℂ] B` induces a continuous map
  `CPoints B → CPoints A`.
* `isClosedEmbedding_comap` — a *surjection* `A →ₐ[ℂ] B` induces a closed
  embedding `CPoints B ↪ CPoints A` (a closed subvariety sits as a closed
  subspace of the ambient variety; the range is the zero locus of the
  kernel).
* `toZariski`, `continuous_toZariski` — the comparison map from the
  analytic space of ℂ-points to the Zariski prime spectrum is continuous.
* `bridge` — `CPoints A` coincides with the scheme-theoretic ℂ-points: the
  sections of the structure morphism `Spec A ⟶ Spec ℂ`.
* `evAlgHom` — regular functions are continuous: evaluation is an algebra
  homomorphism `A →ₐ[ℂ] C(CPoints A, ℂ)`.
* `exists_isClosedEmbedding_of_finiteType` and consequences — for `A` of
  finite type, `CPoints A` is homeomorphic to a closed subspace of some
  `ℂⁿ`; hence it is locally compact and second countable (as well as
  Hausdorff, which holds for every `A`: `instT2SpaceCPoints`).

This is the affine, purely topological germ of the classical construction
of Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst.
Fourier 6 (1956), §1 (there performed for arbitrary varieties and endowed
with an analytic-space structure).  No scheme-level analytification, no
analytic-space or manifold structure, and no comparison theorem is claimed
or provided here.
-/

open Topology Set

noncomputable section

universe u v w

namespace HodgePilot.Analytic

section General

variable (A : Type u) [CommRing A] [Algebra ℂ A]

/-- The ℂ-points of `Spec A`: ℂ-algebra homomorphisms `A →ₐ[ℂ] ℂ`.-/
abbrev CPoints := A →ₐ[ℂ] ℂ

/-- Evaluation map into the full product `A → ℂ`.-/
def toPi : CPoints A → (A → ℂ) := fun φ a => φ a

/-- The analytic (euclidean) topology on the ℂ-points: the initial topology
from evaluation at every element of `A`, i.e. the subspace topology of
`CPoints A ⊆ (A → ℂ)` with the product topology.  This definition does not
choose a presentation of `A`; see `isEmbedding_evalGen` for the classical
presentation-independence statement.-/
instance instTopCPoints : TopologicalSpace (CPoints A) :=
  TopologicalSpace.induced (toPi A) Pi.topologicalSpace

variable {A}

lemma isInducing_toPi : IsInducing (toPi A) := ⟨rfl⟩

lemma injective_toPi : Function.Injective (toPi A) :=
  fun _ _ h => AlgHom.ext (congrFun h)

lemma isEmbedding_toPi : IsEmbedding (toPi A) := ⟨isInducing_toPi, injective_toPi⟩

/-- Evaluation at a fixed element of `A` is continuous.-/
lemma continuous_ev (a : A) : Continuous fun φ : CPoints A => φ a :=
  (continuous_apply a).comp isInducing_toPi.continuous

/-- The analytic topology as an infimum of evaluation topologies.-/
lemma topology_eq_iInf :
    instTopCPoints A =
      ⨅ a : A, TopologicalSpace.induced (fun φ : CPoints A => φ a) inferInstance :=
  induced_to_pi _

/-- **Presentation independence** of the analytic topology: for any generating
family `g` of the ℂ-algebra `A`, evaluation at the generators alone induces
the analytic topology.  Classical proof: every element of `A` is a polynomial
in the generators, and polynomial maps `ℂ^ι → ℂ` are continuous.-/
theorem isInducing_evalGen {ι : Type v} (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    IsInducing (fun (φ : CPoints A) (i : ι) => φ (g i)) := by
  constructor
  rw [induced_to_pi, topology_eq_iInf]
  refine le_antisymm (le_iInf fun i => iInf_le _ (g i)) (le_iInf fun a => ?_)
  obtain ⟨p, hp⟩ := (AlgHom.mem_range _).mp
    (show a ∈ (MvPolynomial.aeval (R := ℂ) g).range by
      rw [MvPolynomial.aeval_range, hg]; exact Algebra.mem_top)
  have hev : (fun φ : CPoints A => φ a) =
      (fun v : ι → ℂ => MvPolynomial.eval v p) ∘ (fun (φ : CPoints A) (i : ι) => φ (g i)) := by
    funext φ
    have h1 : φ a = MvPolynomial.aeval (fun i => φ (g i)) p := by
      conv_lhs => rw [← hp]
      exact MvPolynomial.comp_aeval_apply ..
    rw [h1, MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]
    rfl
  calc ⨅ i, TopologicalSpace.induced (fun φ : CPoints A => φ (g i)) inferInstance
      = TopologicalSpace.induced (fun (φ : CPoints A) (i : ι) => φ (g i)) Pi.topologicalSpace :=
        (induced_to_pi _).symm
    _ ≤ TopologicalSpace.induced (fun (φ : CPoints A) (i : ι) => φ (g i))
          (TopologicalSpace.induced (fun v : ι → ℂ => MvPolynomial.eval v p) inferInstance) :=
        induced_mono (continuous_iff_le_induced.mp (MvPolynomial.continuous_eval p))
    _ = TopologicalSpace.induced (fun φ : CPoints A => φ a) inferInstance := by
        rw [induced_compose, ← hev]

/-- A ℂ-point is determined by its values on a generating family.-/
theorem injective_evalGen {ι : Type v} (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Function.Injective (fun (φ : CPoints A) (i : ι) => φ (g i)) := by
  intro φ ψ h
  have hle : Algebra.adjoin ℂ (Set.range g) ≤ AlgHom.equalizer φ ψ :=
    Algebra.adjoin_le (by rintro x ⟨i, rfl⟩; exact congrFun h i)
  exact AlgHom.ext fun a => hle (by rw [hg]; exact Algebra.mem_top)

/-- **Presentation independence**, embedding form: evaluation at any
generating family of `A` is a topological embedding `CPoints A ↪ (ι → ℂ)`.
In particular any presentation of `A` by `n` generators realizes the
ℂ-points, with their analytic topology, as a subspace of `ℂⁿ`.-/
theorem isEmbedding_evalGen {ι : Type v} (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    IsEmbedding (fun (φ : CPoints A) (i : ι) => φ (g i)) :=
  ⟨isInducing_evalGen g hg, injective_evalGen g hg⟩

/-- The ℂ-points of affine space: `𝔸^σ(ℂ) ≃ ℂ^σ` as sets.-/
def mvPolynomialEquiv (σ : Type v) : CPoints (MvPolynomial σ ℂ) ≃ (σ → ℂ) where
  toFun φ i := φ (MvPolynomial.X i)
  invFun v := MvPolynomial.aeval v
  left_inv _ := MvPolynomial.algHom_ext fun i => MvPolynomial.aeval_X _ i
  right_inv _ := funext fun i => MvPolynomial.aeval_X _ i

/-- The ℂ-points of affine space with the analytic topology:
`𝔸^σ(ℂ) ≃ₜ ℂ^σ` as topological spaces.-/
def mvPolynomialHomeomorph (σ : Type v) : CPoints (MvPolynomial σ ℂ) ≃ₜ (σ → ℂ) :=
  (mvPolynomialEquiv σ).toHomeomorphOfIsInducing (by
    show IsInducing (fun (φ : CPoints (MvPolynomial σ ℂ)) (i : σ) => φ (MvPolynomial.X i))
    exact isInducing_evalGen MvPolynomial.X MvPolynomial.adjoin_range_X)

/-- Contravariant functoriality on points: an algebra map `A →ₐ[ℂ] B`
induces `CPoints B → CPoints A` by precomposition.-/
def comap {B : Type v} [CommRing B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) :
    CPoints B → CPoints A := fun ψ => ψ.comp f

theorem continuous_comap {B : Type v} [CommRing B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) :
    Continuous (comap (A := A) f) := by
  refine continuous_induced_rng.2 ?_
  exact continuous_pi fun a => continuous_ev (f a)

@[simp]
theorem comap_id : comap (AlgHom.id ℂ A) = (id : CPoints A → CPoints A) := rfl

theorem comap_comp {B : Type v} [CommRing B] [Algebra ℂ B]
    {C : Type w} [CommRing C] [Algebra ℂ C] (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) :
    comap (g.comp f) = comap (A := A) f ∘ comap (A := B) g := rfl

/-- A surjection of ℂ-algebras induces a *closed* embedding on analytic
spaces of ℂ-points: the closed subvariety `Spec B ⊆ Spec A` cut out by
`ker f` sits as a closed subspace, namely the common zero locus of the
kernel (computed inside the proof).-/
theorem isClosedEmbedding_comap {B : Type v} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (hf : Function.Surjective f) :
    IsClosedEmbedding (comap (A := A) f) := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [topology_eq_iInf (A := B), topology_eq_iInf (A := A), induced_iInf]
    simp only [induced_compose, Function.comp_def, comap, AlgHom.comp_apply]
    exact (hf.iInf_comp _).symm
  · intro ψ₁ ψ₂ h
    refine AlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hf b
    exact AlgHom.congr_fun h a
  · have hrange : Set.range (comap (A := A) f) =
        ⋂ a ∈ RingHom.ker f, {φ : CPoints A | φ a = 0} := by
      ext φ
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨ψ, rfl⟩ a ha
        have hfa : f a = 0 := ha
        simp [comap, hfa]
      · intro hker
        refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) φ hker).comp
          (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom, ?_⟩
        refine AlgHom.ext fun a => ?_
        have hmk : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) =
            Ideal.Quotient.mk (RingHom.ker f) a := by
          rw [AlgEquiv.symm_apply_eq]
          exact (Ideal.quotientKerAlgEquivOfSurjective_mk hf a).symm
        simp [comap, hmk]
        first
          | (all_goals grind; done)
          | (all_goals simp_all; done)
          | (all_goals aesop; done)
          | (all_goals omega; done)
          | (all_goals norm_num; done)
          | (all_goals positivity; done)
          | (all_goals linarith; done)
          | (all_goals decide; done)
          | (all_goals tauto; done)
    rw [hrange]
    refine isClosed_biInter fun a _ => ?_
    exact isClosed_eq (continuous_ev a) continuous_const

/-- The comparison map from the analytic space of ℂ-points to the Zariski
prime spectrum, sending a ℂ-point to its kernel.-/
def toZariski : CPoints A → PrimeSpectrum A := fun φ =>
  ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩

/-- The non-vanishing locus of an element of `A` is open in the analytic
topology (the analytic counterpart of a basic open; seed for localization
compatibility).-/
theorem isOpen_setOf_ne_zero (a : A) : IsOpen {φ : CPoints A | φ a ≠ 0} :=
  isOpen_compl_singleton.preimage (continuous_ev a)

variable (A) in
/-- Regular functions are continuous: evaluation as an algebra homomorphism
from `A` to the ℂ-algebra of continuous functions on its analytic space of
ℂ-points.-/
def evAlgHom : A →ₐ[ℂ] C(CPoints A, ℂ) where
  toFun a := ⟨fun φ => φ a, continuous_ev a⟩
  map_one' := ContinuousMap.ext fun φ => map_one φ
  map_mul' a b := ContinuousMap.ext fun φ => map_mul φ a b
  map_zero' := ContinuousMap.ext fun φ => map_zero φ
  map_add' a b := ContinuousMap.ext fun φ => map_add φ a b
  commutes' c := ContinuousMap.ext fun φ => φ.commutes c

@[simp]
theorem evAlgHom_apply (a : A) (φ : CPoints A) : evAlgHom A a φ = φ a := rfl

variable (A) in
/-- A finite-type ℂ-algebra has its analytic space of ℂ-points realized as
a closed subspace of some `ℂⁿ` (compose a surjective presentation
`ℂ[x₁, …, xₙ] → A` with the homeomorphism `𝔸ⁿ(ℂ) ≃ₜ ℂⁿ`).-/
theorem exists_isClosedEmbedding_of_finiteType [Algebra.FiniteType ℂ A] :
    ∃ (n : ℕ) (e : CPoints A → (Fin n → ℂ)), IsClosedEmbedding e := by
  obtain ⟨n, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℂ) (S := A)).mp
      ‹Algebra.FiniteType ℂ A›
  exact ⟨n, ⇑(mvPolynomialHomeomorph (Fin n)) ∘ comap π,
    (mvPolynomialHomeomorph (Fin n)).isClosedEmbedding.comp
      (isClosedEmbedding_comap π hπ)⟩

end General

/-! ## The bridge to scheme-theoretic ℂ-points

`CPoints A` coincides with the ℂ-points of the scheme `Spec A` in the
scheme-theoretic sense: sections of the structure morphism
`Spec A ⟶ Spec ℂ`. -/

section Bridge

open AlgebraicGeometry CategoryTheory

variable (A : Type) [CommRing A] [Algebra ℂ A]

/-- The structure morphism of `Spec A` as a ℂ-scheme.-/
def structMor : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ A))

/-- ℂ-algebra homomorphisms `A →ₐ[ℂ] ℂ` are exactly the sections of the
structure morphism, i.e. the scheme-theoretic ℂ-points of `Spec A` over ℂ.-/
def bridge : CPoints A ≃
    {p : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of A) // p ≫ structMor A = 𝟙 _} where
  toFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [structMor, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    ext (c : ℂ)
    exact φ.commutes c⟩
  invFun p :=
    { toRingHom := (Spec.preimage p.1).hom
      commutes' := fun c => by
        have h1 : Spec.map (CommRingCat.ofHom (algebraMap ℂ A) ≫ Spec.preimage p.1) =
            𝟙 (Spec (CommRingCat.of ℂ)) := by
          rw [Spec.map_comp, Spec.map_preimage]
          exact p.2
        have h2 : CommRingCat.ofHom (algebraMap ℂ A) ≫ Spec.preimage p.1 =
            𝟙 (CommRingCat.of ℂ) := Spec.map_injective (by rw [h1, Spec.map_id])
        have h3 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom h2) c
        simpa using h3 }
  left_inv φ := by
    ext a
    change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom a = φ a
    rw [Spec.preimage_map]
    rfl
  right_inv p := by
    ext1
    change Spec.map (CommRingCat.ofHom (Spec.preimage p.1).hom) = p.1
    have : CommRingCat.ofHom (Spec.preimage p.1).hom = Spec.preimage p.1 := rfl
    rw [this, Spec.map_preimage]

end Bridge

end HodgePilot.Analytic
