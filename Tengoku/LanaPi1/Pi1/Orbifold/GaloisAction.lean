module

public import Tengoku.LanaPi1.Pi1.Orbifold.GaloisData
public import Tengoku.LanaPi1.Pi1.RingTheory.UnramifiedValuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Galois action on the fibres of equivariant finite étale covers

Let `D : GaloisData k t` (open subgroups `H_L ≤ H` of `Gal(Ω / k(t))`, `L = Ω^{H_L}`, `R` the
coordinate ring of the normalization of the `t`-line in `L`, `A = H ⧸ H_L`). An element `σ ∈ H`
acts on the fibre `X.B →ₐ[R] Ω` of an `A`-equivariant finite étale `R`-algebra `X` by
`f ↦ σ ∘ f ∘ (X.act σ̄)⁻¹` (`GaloisData.fibreSmul`); this is natural in `X` and defines a continuous
homomorphism `GaloisData.toEtalePi1 : H →* etalePi1 R A Ω`.

The inertia elements `S` act trivially (`GaloisData.fibreSmul_eq_self_of_mem_S`): for `σ ∈ H_L`
in the inertia group of a valuation subring `W ⊇ k[t]`, the maps `f` and `σ ∘ f` take values in
`W` and agree modulo its maximal ideal, hence agree since `X.B` is unramified over `R`.
Consequently `toEtalePi1` factors through `GaloisPi1.pi1 H S` (`GaloisData.pi1ToEtalePi1`).
-/

@[expose] public section
namespace Tengoku.LanaPi1 end Tengoku.LanaPi1 open Tengoku.LanaPi1 
universe w v u

open CategoryTheory Tengoku.LanaPi1.AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

noncomputable section

namespace FibreAut

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

/-- An automorphism of a fibre functor given by compatible bijections of the fibres.-/
def ofEquivs (e : ∀ c, F.obj c ≃ F.obj c)
    (h : ∀ {c d : C} (f : c ⟶ d) (x : F.obj c), e d (F.map f x) = F.map f (e c x)) :
    FibreAut F :=
  show Aut F from NatIso.ofComponents (fun c => (e c).toIso) (fun f => by ext x; exact h f x)

/--
@isnad1 id=eq.1h5v.s9.0d9df18a8f40 from=translated src=- shape=ea771559 vocab=7f8a59d9
-/
@[simp] lemma ofEquivs_app (e : ∀ c, F.obj c ≃ F.obj c)
    (h : ∀ {c d : C} (f : c ⟶ d) (x : F.obj c), e d (F.map f x) = F.map f (e c x)) (c : C)
    (x : F.obj c) : (ofEquivs e h).app c x = e c x := rfl

end FibreAut

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/--
@isnad1 id=eq.0h5v.s10.5124578fac2d from=translated src=- shape=bd6339f0 vocab=c477da03
-/
lemma aut_apply_inv_apply (σ : Ω ≃ₐ[K₀ k t] Ω) (x : Ω) : σ (σ⁻¹ x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

/--
@isnad1 id=eq.0h5v.s10.58ac3e2562f5 from=translated src=- shape=489fd88f vocab=c477da03
-/
lemma aut_inv_apply_apply (σ : Ω ≃ₐ[K₀ k t] Ω) (x : Ω) : σ⁻¹ (σ x) = x := by
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- The stabilizer of an element of `Ω` is open in the Krull topology.
@isnad1 id=isopen.0h4v.s9.cb0bc59259ec from=translated src=- shape=47e9405d vocab=0800004b
-/
lemma isOpen_setOf_apply_eq [IsGalois (K₀ k t) Ω] (x : Ω) :
    IsOpen {σ : Ω ≃ₐ[K₀ k t] Ω | σ x = x} := by
  have : FiniteDimensional (K₀ k t) (IntermediateField.adjoin (K₀ k t) {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hM : (IntermediateField.adjoin (K₀ k t) {x}).fixingSubgroup ≤
      MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) x :=
    fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x
      (IntermediateField.mem_adjoin_simple_self _ x)
  exact Subgroup.isOpen_mono hM (IntermediateField.fixingSubgroup_isOpen _)

/-- An element of `Ω` integral over `k[t]` lies in every valuation subring containing `k` and
`t`.
@isnad1 id=mem.3h5v.s8.7ff92ddf2548 from=translated src=- shape=b808cdbf vocab=6e9603b3
-/
lemma mem_of_isIntegral {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (ht : t ∈ W) {x : Ω} (hx : IsIntegral (A₀ k t) x) : x ∈ W := by
  let Wk : Subalgebra k Ω := { W.toSubring with algebraMap_mem' := hk }
  have hle : A₀ k t ≤ Wk := Algebra.adjoin_le (Set.singleton_subset_iff.2 ht)
  let φ : A₀ k t →+* W := (Subalgebra.inclusion hle).toRingHom
  have hW : IsIntegral W x :=
    IsIntegral.map_of_comp_eq (T := W) φ (RingHom.id Ω) (RingHom.ext fun _ => rfl) hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hW
  rw [← hy]
  exact y.2

namespace GaloisData

variable (D : GaloisData k t)

/--
@isnad1 id=eq.1h5v.s15.1f91acb05b63 from=translated src=- shape=0cd4d7a1 vocab=865dc173
-/
lemma mk_eq_one_of_mem {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.HL) : (σ : D.A) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (by rwa [Subgroup.mem_subgroupOf])

/-- **The action of `σ ∈ H` on the fibre of `X`**: `f ↦ σ ∘ f ∘ (X.act σ̄)⁻¹`.-/
def fibreSmul (σ : D.H) (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) : X.B →ₐ[D.R] Ω where
  toRingHom := ((σ : Ω ≃ₐ[K₀ k t] Ω) : Ω →+* Ω).comp
    (f.toRingHom.comp ((X.act (σ⁻¹ : D.H)).σ : X.B →+* X.B))
  commutes' r := by
    change (σ : Ω ≃ₐ[K₀ k t] Ω) (f ((X.act (σ⁻¹ : D.H)).σ (algebraMap D.R X.B r))) = _
    rw [(X.act _).map_algebraMap, X.act_a, AlgHom.commutes, algebraMap_smul]
    exact aut_apply_inv_apply _ _

variable [IsGalois (K₀ k t) Ω]

end GaloisData

end

end Pi1.Orbifold
-- Tengoku: root names of this library moved to Tengoku.LanaPi1 so they do not collide with other libraries (generated)
