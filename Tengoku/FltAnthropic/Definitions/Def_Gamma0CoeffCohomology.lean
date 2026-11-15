import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

section Cocycles

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def coeffCocycles (ρ : Representation K G V) : Submodule K (G → V) where
  carrier := {z | ∀ g h : G, z (g * h) = z g + ρ g (z h)}
  zero_mem' := by
    intro g h
    simp
  add_mem' := by
    intro z w hz hw g h
    simp only [Pi.add_apply, hz g h, hw g h, map_add]
    abel
  smul_mem' := by
    intro c z hz g h
    simp only [Pi.smul_apply, hz g h, smul_add, map_smul]

/--
@isnad1 id=iff.0h5v.s8.b55cbe5e813e from=translated src=- shape=a931e73e vocab=9d0a03e0
-/
theorem mem_coeffCocycles_iff (ρ : Representation K G V) (z : G → V) :
    z ∈ coeffCocycles ρ ↔ ∀ g h : G, z (g * h) = z g + ρ g (z h) :=
  Iff.rfl

def coeffCoboundaryMap (ρ : Representation K G V) : V →ₗ[K] (G → V) where
  toFun v := fun g => ρ g v - v
  map_add' v w := by
    ext g
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' c v := by
    ext g
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

/--
@isnad1 id=eq.0h6v.s8.dfe0415c2ae4 from=translated src=- shape=bd9c2153 vocab=388a3afc
-/
@[simp]
theorem coeffCoboundaryMap_apply (ρ : Representation K G V) (v : V) (g : G) :
    coeffCoboundaryMap ρ v g = ρ g v - v :=
  rfl

def coeffCoboundaries (ρ : Representation K G V) : Submodule K (G → V) :=
  LinearMap.range (coeffCoboundaryMap ρ)

/--
@isnad1 id=iff.0h5v.s8.b789507017a2 from=translated src=- shape=d66084e9 vocab=34db1273
-/
theorem mem_coeffCoboundaries_iff (ρ : Representation K G V) (z : G → V) :
    z ∈ coeffCoboundaries ρ ↔ ∃ v : V, (fun g => ρ g v - v) = z := by
  simp [coeffCoboundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩

/--
@isnad1 id=le.0h4v.s7.c8ec7b40a654 from=translated src=- shape=3b8419ac vocab=610b706f
-/
theorem coeffCoboundaries_le_coeffCocycles (ρ : Representation K G V) :
    coeffCoboundaries ρ ≤ coeffCocycles ρ := by
  rintro z ⟨v, rfl⟩ g h
  show ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)
  rw [map_mul, map_sub]
  simp only [Module.End.mul_apply]
  abel

end Cocycles

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsParabolicCocycle (ρ : Representation K Γ V) (z : Γ → V) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
    z γ ∈ LinearMap.range (ρ γ - 1)

def coeffParabolicCocycles (ρ : Representation K Γ V) : Submodule K (Γ → V) where
  carrier := {z | z ∈ coeffCocycles ρ ∧ IsParabolicCocycle ρ z}
  zero_mem' := ⟨Submodule.zero_mem _, fun γ _ => by simp⟩
  add_mem' := by
    rintro z w ⟨hz, hz'⟩ ⟨hw, hw'⟩
    exact ⟨Submodule.add_mem _ hz hw, fun γ hγ => Submodule.add_mem _ (hz' γ hγ) (hw' γ hγ)⟩
  smul_mem' := by
    rintro c z ⟨hz, hz'⟩
    exact ⟨Submodule.smul_mem _ c hz, fun γ hγ => Submodule.smul_mem _ c (hz' γ hγ)⟩

/--
@isnad1 id=iff.0h5v.s13.443b4ac4d5dd from=translated src=- shape=fdbf5d1f vocab=6cfb35cf
-/
theorem mem_coeffParabolicCocycles_iff (ρ : Representation K Γ V) (z : Γ → V) :
    z ∈ coeffParabolicCocycles ρ ↔ z ∈ coeffCocycles ρ ∧ IsParabolicCocycle ρ z :=
  Iff.rfl

/--
@isnad1 id=le.0h4v.s12.24fadd4b1d92 from=translated src=- shape=d49ad2a3 vocab=aa803bde
-/
theorem coeffParabolicCocycles_le_coeffCocycles (ρ : Representation K Γ V) :
    coeffParabolicCocycles ρ ≤ coeffCocycles ρ :=
  fun _ hz => hz.1

/--
@isnad1 id=le.0h4v.s12.d172be6fd5c0 from=translated src=- shape=35dcb27d vocab=8dc67a7c
-/
theorem coeffCoboundaries_le_coeffParabolicCocycles (ρ : Representation K Γ V) :
    coeffCoboundaries ρ ≤ coeffParabolicCocycles ρ := by
  intro z hz
  refine ⟨coeffCoboundaries_le_coeffCocycles ρ hz, fun γ _ => ?_⟩
  obtain ⟨v, rfl⟩ := hz
  exact ⟨v, by simp [coeffCoboundaryMap]⟩

def coeffH1par (ρ : Representation K Γ V) : Type _ :=
  ↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype

instance instAddCommGroupCoeffH1par (ρ : Representation K Γ V) : AddCommGroup (coeffH1par ρ) :=
  inferInstanceAs (AddCommGroup
    (↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype))

instance instModuleCoeffH1par (ρ : Representation K Γ V) : Module K (coeffH1par ρ) :=
  inferInstanceAs (Module K
    (↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype))

def coeffH1parMk (ρ : Representation K Γ V) : ↥(coeffParabolicCocycles ρ) →ₗ[K] coeffH1par ρ :=
  ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype).mkQ

/--
@isnad1 id=surjecti.0h4v.s14.80bbc7e7a06f from=translated src=- shape=b3ee9f58 vocab=11c468c5
-/
theorem coeffH1parMk_surjective (ρ : Representation K Γ V) :
    Function.Surjective (coeffH1parMk ρ) :=
  Submodule.mkQ_surjective _

/--
@isnad1 id=iff.0h5v.s15.1e410775c87b from=translated src=- shape=fa962743 vocab=cc5476e5
-/
theorem coeffH1parMk_eq_zero_iff (ρ : Representation K Γ V) (z : ↥(coeffParabolicCocycles ρ)) :
    coeffH1parMk ρ z = 0 ↔ (z : Γ → V) ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

end Parabolic

section Hecke

variable (N : ℕ) (ℓ : ℕ) [NeZero ℓ]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def coeffHeckeFun (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (z : Gamma0 N → V) : Gamma0 N → V :=
  fun g =>
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
      ρ (g • q).out (a (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q))))

/--
@isnad1 id=eq.0h8v.s15.a135fd8b5ffe from=translated src=- shape=97f4637f vocab=96409281
-/
theorem coeffHeckeFun_apply (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (z : Gamma0 N → V) (g : Gamma0 N) :
    coeffHeckeFun N ℓ ρ a z g =
      letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
      ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        ρ (g • q).out (a (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q)))) :=
  rfl

/--
@isnad1 id=eq.0h5v.s15.dc3d4c3968f4 from=translated src=- shape=01dba5d0 vocab=c5517022
-/
theorem coeffHeckeFun_trivial (φ : Additive (Gamma0 N) →+ K) (g : Gamma0 N) :
    coeffHeckeFun N ℓ (1 : Representation K (Gamma0 N) K) LinearMap.id
        (fun h => φ (Additive.ofMul h)) g
      = heckeOperatorHom N ℓ K φ (Additive.ofMul g) := by
  rw [coeffHeckeFun_apply, heckeOperatorHom_apply]
  simp

end Hecke

end HeckeEis
