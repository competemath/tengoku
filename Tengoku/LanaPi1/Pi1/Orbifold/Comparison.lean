module

public import Tengoku.LanaPi1.Pi1.Orbifold.Induced

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The étale fundamental group of `[Spec R / A]` is a Galois group (SGA 1 V.8.2)

Let `k` be a field of characteristic `0`, `Ω / k(t)` an algebraic Galois extension (`t`
transcendental over `k`), and `D : GaloisData k t`: open subgroups `H_L ≤ H` of
`Gal(Ω / k(t))`, `H` normalizing `H_L`. Let `L = Ω^{H_L}`, `R` the integral closure of `k[t]`
in `L` and `A = H ⧸ H_L`, acting on `R`. Let `S ⊆ H_L` be the set of inertia elements at the
places of `Ω` centered on `Spec R`.

**Theorem** (`GaloisData.equivPi1`). The action of `H` on the fibres of `A`-equivariant finite
étale covers of `Spec R` induces an isomorphism of profinite groups

  `etalePi1 R A Ω ≃ₜ* GaloisPi1.pi1 H S = H ⧸ ⟨⟨S⟩⟩`.

The map `H ⧸ ⟨⟨S⟩⟩ → etalePi1 R A Ω` is `GaloisData.pi1ToEtalePi1` (inertia acts trivially:
`Pi1.Orbifold.GaloisAction`). It is injective: for `σ ∉ ⟨⟨S⟩⟩` there is an open normal subgroup
`U ⊴ H`, `U ≤ H_L`, containing `S` but not `σ`, and `σ` moves the distinguished fibre element of
the induced cover attached to `U` (`Pi1.Orbifold.Induced`). Its image is dense: given an
automorphism `α` of the fibre functor and finitely many fibre elements, the induced cover of a
small enough level dominates all of them, and its fibre is a single `H`-orbit. As the source is
compact and the target Hausdorff, it is a homeomorphism.
-/

@[expose] public section
namespace Tengoku.LanaPi1 end Tengoku.LanaPi1 open Tengoku.LanaPi1 
universe u

open CategoryTheory Tengoku.LanaPi1.AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

namespace GaloisData

variable (D : GaloisData k t)

/--
@isnad1 id=mem.1h5v.s13.639f6cffabef from=translated src=- shape=c024aca9 vocab=6b249a36
-/
lemma mem_kernel_of_mem_S (s : D.H) (hs : (s : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S) :
    s ∈ GaloisPi1.kernel D.H D.S := by
  rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf]
  exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨1, D.H.one_mem, s, hs, by simp⟩)

variable [IsGalois (K₀ k t) Ω]

/--
@isnad1 id=compacts.0h4v.s11.9cc0d755bbf1 from=translated src=- shape=dcf8fd95 vocab=3fb1fd15
-/
instance compactSpace_H : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H

/-- The level `U = core_H(V₀)` attached to an open subgroup `V₀ ≤ H_L` containing the
`H`-conjugates of the inertia elements.-/
def Level.ofOpen (V₀ : Subgroup D.H) (hV₀ : IsOpen (V₀ : Set D.H))
    (hle : V₀ ≤ D.HL.subgroupOf D.H)
    (hS : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → ∀ g : D.H, g * σ * g⁻¹ ∈ V₀) : D.Level where
  U := V₀.normalCore
  normal := inferInstance
  isOpen := by
    haveI : Finite (D.H ⧸ V₀) := Subgroup.quotient_finite_of_isOpen _ hV₀
    haveI : V₀.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (Subgroup.normalCore_isClosed _ (Subgroup.isClosed_of_isOpen _ hV₀))
  le := (Subgroup.normalCore_le _).trans hle
  S_le σ hσ := fun g => hS σ hσ g

/--
@isnad1 id=le.3h5v.s15.635f29b7a8e2 from=translated src=- shape=90e82275 vocab=9092920f
-/
lemma Level.ofOpen_U_le (V₀ : Subgroup D.H) (hV₀ : IsOpen (V₀ : Set D.H))
    (hle : V₀ ≤ D.HL.subgroupOf D.H)
    (hS : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → ∀ g : D.H, g * σ * g⁻¹ ∈ V₀) :
    (Level.ofOpen D V₀ hV₀ hle hS).U ≤ V₀ :=
  Subgroup.normalCore_le _

/--
@isnad1 id=mem.4h7v.s16.40a821d7a534 from=translated src=- shape=e523062f vocab=9092920f
-/
lemma Level.ofOpen_conj_mem {V₀ : Subgroup D.H} {hV₀ : IsOpen (V₀ : Set D.H)}
    {hle : V₀ ≤ D.HL.subgroupOf D.H}
    {hS : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → ∀ g : D.H, g * σ * g⁻¹ ∈ V₀} {u : D.H}
    (hu : u ∈ (Level.ofOpen D V₀ hV₀ hle hS).U) (g : D.H) : g * u * g⁻¹ ∈ V₀ :=
  hu g

variable [CharZero k]

end GaloisData

end

end Pi1.Orbifold
-- Tengoku: root names of this library moved to Tengoku.LanaPi1 so they do not collide with other libraries (generated)
