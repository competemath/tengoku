import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (coeffCocycles coeffCoboundaryMap_apply coeffCoboundaries coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffHeckeFun coeffHeckeFun_apply)
open _root_.HeckeEis
namespace C2b

open CongruenceSubgroup

section General
variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K]
  {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  (ρ : Representation K Γ V) (ρ' : Representation K Γ V')
  (i : V →ₗ[K] V') (hi : ∀ g : Γ, i ∘ₗ ρ g = ρ' g ∘ₗ i)

def post (i : V →ₗ[K] V') : (Γ → V) →ₗ[K] (Γ → V') where
  toFun z := i ∘ z
  map_add' z w := by funext g; simp
  map_smul' c z := by funext g; simp

include hi in
/--
@isnad1 id=eq.1h9v.s13.cf8a002722e1 from=translated src=- shape=af7ee6ce vocab=84e90edb
-/
theorem hi_apply (g : Γ) (v : V) : i (ρ g v) = ρ' g (i v) := by
  have := LinearMap.congr_fun (hi g) v
  simpa using this

include hi in
/--
@isnad1 id=mem.2h8v.s13.37104eb4141a from=translated src=- shape=3ed457d7 vocab=d0cb31c0
-/
theorem post_mem_coeffCocycles {z : Γ → V} (hz : z ∈ coeffCocycles ρ) : i ∘ z ∈ coeffCocycles ρ' := by
  intro g h
  simp only [Function.comp_apply, hz g h, map_add, hi_apply ρ ρ' i hi]

include hi in
/--
@isnad1 id=mem.2h9v.s13.c83ee6701bb2 from=translated src=- shape=05a7c5fd vocab=c778ffcc
-/
theorem post_mem_range {γ : Γ} {v : V} (hv : v ∈ LinearMap.range (ρ γ - 1)) :
    i v ∈ LinearMap.range (ρ' γ - 1) := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨i u, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hi_apply ρ ρ' i hi]

include hi in
/--
@isnad1 id=mem.2h8v.s13.934c47c01e87 from=translated src=- shape=dbedb95f vocab=015f84b7
-/
theorem post_mem_coeffParabolicCocycles {z : Γ → V} (hz : z ∈ coeffParabolicCocycles ρ) :
    i ∘ z ∈ coeffParabolicCocycles ρ' :=
  ⟨post_mem_coeffCocycles ρ ρ' i hi hz.1, fun γ hγ => post_mem_range ρ ρ' i hi (hz.2 γ hγ)⟩

include hi in
/--
@isnad1 id=mem.2h8v.s13.464d4d6a99e5 from=translated src=- shape=3ed457d7 vocab=ea10c434
-/
theorem post_mem_coeffCoboundaries {z : Γ → V} (hz : z ∈ coeffCoboundaries ρ) :
    i ∘ z ∈ coeffCoboundaries ρ' := by
  obtain ⟨v, rfl⟩ := hz
  refine ⟨i v, ?_⟩
  funext g
  simp only [coeffCoboundaryMap_apply, Function.comp_apply, map_sub, hi_apply ρ ρ' i hi]

def push : ↥(coeffParabolicCocycles ρ) →ₗ[K] ↥(coeffParabolicCocycles ρ') :=
  ((post i).comp (coeffParabolicCocycles ρ).subtype).codRestrict (coeffParabolicCocycles ρ')
    (fun z => post_mem_coeffParabolicCocycles ρ ρ' i hi z.2)

/--
@isnad1 id=eq.1h8v.s15.ede36bb7f401 from=translated src=- shape=d686640c vocab=3d9f71b0
-/
theorem coe_push (z : ↥(coeffParabolicCocycles ρ)) :
    ((push ρ ρ' i hi z : ↥(coeffParabolicCocycles ρ')) : Γ → V') = i ∘ (z : Γ → V) := rfl

/--
@isnad1 id=le.1h7v.s15.a51458c8914b from=translated src=- shape=2f76fc4e vocab=2f3645da
-/
theorem push_le :
    (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype ≤
      ((coeffCoboundaries ρ').comap (coeffParabolicCocycles ρ').subtype).comap (push ρ ρ' i hi) := by
  intro z hz
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hz ⊢
  rw [coe_push]
  exact post_mem_coeffCoboundaries ρ ρ' i hi hz

def mapH1par : coeffH1par ρ →ₗ[K] coeffH1par ρ' :=
  Submodule.mapQ _ _ (push ρ ρ' i hi) (push_le ρ ρ' i hi)

/--
@isnad1 id=eq.1h8v.s16.d334013acdc4 from=translated src=- shape=c1235e66 vocab=86e120cb
-/
theorem mapH1par_mk (z : ↥(coeffParabolicCocycles ρ)) :
    mapH1par ρ ρ' i hi (coeffH1parMk ρ z) = coeffH1parMk ρ' (push ρ ρ' i hi z) := rfl

end General

section Hecke
variable (N : ℕ) {K : Type*} [CommRing K]
  {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  (ρ : Representation K (Gamma0 N) V) (ρ' : Representation K (Gamma0 N) V')
  (i : V →ₗ[K] V') (hi : ∀ g : Gamma0 N, i ∘ₗ ρ g = ρ' g ∘ₗ i)

include hi in

/--
@isnad1 id=eq.2h11v.s12.dbbbb68bcd5f from=translated src=- shape=82791dfe vocab=c7ff0e1b
-/
theorem comp_coeffHeckeFun (ℓ : ℕ) [NeZero ℓ] (a : V →ₗ[K] V) (a' : V' →ₗ[K] V') (hia : i ∘ₗ a = a' ∘ₗ i)
    (z : Gamma0 N → V) :
    i ∘ coeffHeckeFun N ℓ ρ a z = coeffHeckeFun N ℓ ρ' a' (i ∘ z) := by
  have hia' : ∀ v, i (a v) = a' (i v) := fun v => by
    have := LinearMap.congr_fun hia v
    simpa using this
  funext g
  simp only [Function.comp_apply, coeffHeckeFun_apply, map_sum, hi_apply ρ ρ' i hi, hia']

end Hecke

end C2b
open scoped _root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis.C2b
end HeckeEis
open scoped _root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis.C2b _root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis

end
open scoped _root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis.C2b _root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis HeckeEis.C2b CongruenceSubgroup in
/--
@isnad1 id=ex.3h8v.s18.1a971a88620e from=translated src=- shape=3cc8e36d vocab=017b6583
-/
theorem solution
    (N : ℕ) (K : Type*) [CommRing K]
    {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (ρ' : Representation K (CongruenceSubgroup.Gamma0 N) V')
    (i : V →ₗ[K] V') (r : V' →ₗ[K] V)
    (hi : ∀ g : CongruenceSubgroup.Gamma0 N, i ∘ₗ ρ g = ρ' g ∘ₗ i)
    (hr : ∀ g : CongruenceSubgroup.Gamma0 N, r ∘ₗ ρ' g = ρ g ∘ₗ r)
    (hri : r ∘ₗ i = LinearMap.id) :
    ∃ (I : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ')
      (R : HeckeEis.coeffH1par ρ' →ₗ[K] HeckeEis.coeffH1par ρ),
      R ∘ₗ I = LinearMap.id ∧
      (∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
        ∃ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
          (z' : CongruenceSubgroup.Gamma0 N → V') = i ∘ (z : CongruenceSubgroup.Gamma0 N → V) ∧
          I (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ' z') ∧
      (∀ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
        ∃ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
          (z : CongruenceSubgroup.Gamma0 N → V) = r ∘ (z' : CongruenceSubgroup.Gamma0 N → V') ∧
          R (HeckeEis.coeffH1parMk ρ' z') = HeckeEis.coeffH1parMk ρ z) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (a : V →ₗ[K] V) (a' : V' →ₗ[K] V'), i ∘ₗ a = a' ∘ₗ i →
        ∀ (T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ)
          (T' : HeckeEis.coeffH1par ρ' →ₗ[K] HeckeEis.coeffH1par ρ'),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
              (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
              T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w) →
          (∀ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
            ∃ w' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
              (w' : CongruenceSubgroup.Gamma0 N → V') = HeckeEis.coeffHeckeFun N ℓ ρ' a' z' ∧
              T' (HeckeEis.coeffH1parMk ρ' z') = HeckeEis.coeffH1parMk ρ' w') →
          T' ∘ₗ I = I ∘ₗ T) := by
  refine ⟨mapH1par ρ ρ' i hi, mapH1par ρ' ρ r hr, ?_, ?_, ?_, ?_⟩
  ·
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := coeffH1parMk_surjective ρ x
    rw [LinearMap.comp_apply, mapH1par_mk, mapH1par_mk, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    rw [coe_push, coe_push]
    funext g
    have := LinearMap.congr_fun hri ((z : CongruenceSubgroup.Gamma0 N → V) g)
    simpa using this
  · intro z
    exact ⟨push ρ ρ' i hi z, coe_push ρ ρ' i hi z, mapH1par_mk ρ ρ' i hi z⟩
  · intro z'
    exact ⟨push ρ' ρ r hr z', coe_push ρ' ρ r hr z', mapH1par_mk ρ' ρ r hr z'⟩
  · intro ℓ _ a a' hia T T' hT hT'
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := coeffH1parMk_surjective ρ x
    obtain ⟨w, hw, hTw⟩ := hT z
    obtain ⟨w', hw', hT'w⟩ := hT' (push ρ ρ' i hi z)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hTw, mapH1par_mk, mapH1par_mk, hT'w]
    congr 1
    apply Subtype.ext
    rw [hw', coe_push, coe_push, hw]
    exact (comp_coeffHeckeFun N ρ ρ' i hi ℓ a a' hia z).symm
