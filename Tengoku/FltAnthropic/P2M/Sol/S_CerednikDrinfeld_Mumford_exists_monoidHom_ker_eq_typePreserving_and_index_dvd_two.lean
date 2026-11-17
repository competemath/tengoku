import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

namespace IndexTwo

open SimpleGraph

section Parity
variable {W : Type} (𝒯 : SimpleGraph W)

/--
@isnad1 id=eq.0h6v.s8.21a251dea1ca from=translated src=- shape=6b2e74d0 vocab=86a50310
-/
theorem color_eq_add_length (C : 𝒯.Coloring (Fin 2)) {u w : W} (p : 𝒯.Walk u w) :
    ((C w).val : ZMod 2) = ((C u).val : ZMod 2) + (p.length : ZMod 2) := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
      rw [ih, Walk.length_cons, Nat.cast_succ]
      have hne := C.valid hadj
      have key : ∀ x y : Fin 2, x ≠ y → ((y.val : ℕ) : ZMod 2) = ((x.val : ℕ) : ZMod 2) + 1 := by decide
      rw [key _ _ hne]
      ring

/--
@isnad1 id=eq.2h5v.s8.5a5ce46106d9 from=translated src=- shape=17e7f133 vocab=1f7f314b
-/
theorem dist_parity_add (hconn : 𝒯.Connected) (hbip : 𝒯.Colorable 2) (u v w : W) :
    (𝒯.dist u w : ZMod 2) = (𝒯.dist u v : ZMod 2) + (𝒯.dist v w : ZMod 2) := by
  obtain ⟨C⟩ := hbip
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u w
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨r, hr⟩ := hconn.exists_walk_length_eq_dist v w
  have e1 := color_eq_add_length 𝒯 C p
  have e2 := color_eq_add_length 𝒯 C q
  have e3 := color_eq_add_length 𝒯 C r
  rw [hp] at e1; rw [hq] at e2; rw [hr] at e3
  linear_combination e2 + e3 - e1

end Parity

section Iso
variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [Mumford.GraphAction G 𝒯]

/--
@isnad1 id=eq.1h6v.s6.7f35f95bea8a from=translated src=- shape=e99467e1 vocab=6c7fced7
-/
theorem dist_smul (hconn : 𝒯.Connected) (g : G) (v w : W) : 𝒯.dist (g • v) (g • w) = 𝒯.dist v w := by
  have key : ∀ (h : G) (a b : W), 𝒯.dist (h • a) (h • b) ≤ 𝒯.dist a b := by
    intro h a b
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a b
    have := dist_le (p.map (Mumford.smulHom (𝒯 := 𝒯) h))
    rw [Walk.length_map, hp] at this
    exact this
  refine le_antisymm (key g v w) ?_
  have := key g⁻¹ (g • v) (g • w)
  rwa [inv_smul_smul, inv_smul_smul] at this

end Iso

end IndexTwo

/--
@isnad1 id=and.2h4v.s8.92ff8a8db978 from=translated src=- shape=8b04dd83 vocab=31bd987d
-/
theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [Mumford.GraphAction G 𝒯]
    (hconn : 𝒯.Connected) (hbip : 𝒯.Colorable 2) (w₀ : W) :
    (∃ φ : G →* Multiplicative (ZMod 2), φ.ker = Mumford.typePreserving G 𝒯 w₀) ∧
      (Mumford.typePreserving G 𝒯 w₀).index ∣ 2 := by
  classical
  have hadd := IndexTwo.dist_parity_add 𝒯 hconn hbip
  have hiso := IndexTwo.dist_smul (G := G) 𝒯 hconn

  let φ : G →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (Mumford.vertexType 𝒯 w₀ (g • w₀))
      map_one' := by simp [Mumford.vertexType]
      map_mul' := fun g h => by
        rw [← ofAdd_add]
        congr 1
        simp only [Mumford.vertexType, mul_smul]
        rw [hadd w₀ (g • w₀) (g • h • w₀), hiso g w₀ (h • w₀)] }
  have hker : φ.ker = Mumford.typePreserving G 𝒯 w₀ := by
    ext g
    rw [MonoidHom.mem_ker, Mumford.mem_typePreserving_iff]
    change Multiplicative.ofAdd (Mumford.vertexType 𝒯 w₀ (g • w₀)) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    constructor
    · intro h0 w
      simp only [Mumford.vertexType] at h0 ⊢
      rw [hadd w₀ (g • w₀) (g • w), hiso g w₀ w, h0, zero_add]
    · intro h
      have := h w₀
      rwa [Mumford.vertexType_self] at this
  refine ⟨⟨φ, hker⟩, ?_⟩
  rw [← hker, Subgroup.index_ker]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
  have h3 := Subgroup.card_subgroup_dvd_card φ.range
  rw [h2] at h3
  exact h3
