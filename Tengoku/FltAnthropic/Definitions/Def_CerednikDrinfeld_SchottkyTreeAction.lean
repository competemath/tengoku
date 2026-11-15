import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Tengoku.Seed.Algebra.Group.Action.Faithful

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open MulAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

variable (G) in

structure IsTreeLattice : Prop where

  faithful : FaithfulSMul G W

  finite_stabilizer : ∀ w : W, Finite (stabilizer G w)

  finite_quotVert : Finite (QuotVert G W)

  finite_quotEdge : Finite (QuotEdge G 𝒯)

variable (G) in

structure IsSchottky : Prop where

  stabilizer_eq_bot : ∀ w : W, stabilizer G w = ⊥

  smul_ne_symm : ∀ (g : G) (d : 𝒯.Dart), g • d ≠ d.symm

  finite_quotVert : Finite (QuotVert G W)

  finite_quotEdge : Finite (QuotEdge G 𝒯)

/--
@isnad1 id=le.0h4v.s6.53f218004526 from=translated src=- shape=b5fd3e7d vocab=4c71ead1
-/
theorem stabilizer_dart_le (d : 𝒯.Dart) : stabilizer G d ≤ stabilizer G d.fst := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  rw [← smul_dart_fst 𝒯 g d, hg]

namespace IsSchottky

variable {𝒯}

/--
@isnad1 id=eq.1h4v.s5.e5999b1e3a03 from=translated src=- shape=0b2da7c0 vocab=9ea098f8
-/
theorem stabilizer_dart_eq_bot (h : IsSchottky G 𝒯) (d : 𝒯.Dart) : stabilizer G d = ⊥ :=
  le_bot_iff.mp ((stabilizer_dart_le 𝒯 d).trans (h.stabilizer_eq_bot d.fst).le)

/--
@isnad1 id=eq.1h4v.s5.b78b79afb7a4 from=translated src=- shape=8a9b672a vocab=7b52eb02
-/
theorem stabWidth_eq_one (h : IsSchottky G 𝒯) (e : QuotEdge G 𝒯) : stabWidth G 𝒯 e = 1 := by
  induction e using Quotient.inductionOn' with
  | h d => rw [stabWidth_mk, h.stabilizer_dart_eq_bot d, Subgroup.card_bot]; rfl

/--
@isnad1 id=eq.1h4v.s6.5cfd81dffa2a from=translated src=- shape=978920ad vocab=2b1760b4
-/
theorem quotientDegeneracyData_w (h : IsSchottky G 𝒯) (e : QuotEdge G 𝒯) : (quotientDegeneracyData G 𝒯).w e = 1 :=
  h.stabWidth_eq_one e

/--
@isnad1 id=istreela.1h3v.s5.925646c99bfa from=translated src=- shape=b7e03d67 vocab=1f4b8b25
-/
theorem isTreeLattice [Nonempty W] (h : IsSchottky G 𝒯) : IsTreeLattice G 𝒯 where
  faithful := ⟨fun {g₁ g₂} hg => by
    obtain ⟨w⟩ := ‹Nonempty W›
    have : g₂⁻¹ * g₁ ∈ stabilizer G w := by rw [mem_stabilizer_iff, mul_smul, hg w, inv_smul_smul]
    rw [h.stabilizer_eq_bot w, Subgroup.mem_bot] at this
    exact (eq_of_inv_mul_eq_one this).symm⟩
  finite_stabilizer w := by rw [h.stabilizer_eq_bot w]; infer_instance
  finite_quotVert := h.finite_quotVert
  finite_quotEdge := h.finite_quotEdge

end IsSchottky

namespace IsTreeLattice

variable {𝒯}

@[reducible] def fintypeQuotVert (h : IsTreeLattice G 𝒯) : Fintype (QuotVert G W) :=
  @Fintype.ofFinite _ h.finite_quotVert

@[reducible] def fintypeQuotEdge (h : IsTreeLattice G 𝒯) : Fintype (QuotEdge G 𝒯) :=
  @Fintype.ofFinite _ h.finite_quotEdge

end IsTreeLattice

def ActsThrough (W : Type) {G H : Type} [Group G] [Group H] [MulAction G W] [MulAction H W] (ρ : G →* H) : Prop :=
  ∀ (g : G) (w : W), g • w = ρ g • w

variable {𝒯} in

def smulHom (g : G) : 𝒯 →g 𝒯 where
  toFun w := g • w
  map_rel' h := GraphAction.smul_adj g h

/--
@isnad1 id=eq.0h5v.s6.9f8cb92e0f40 from=translated src=- shape=a181f4ad vocab=66ab60e7
-/
@[simp] theorem smulHom_apply (g : G) (w : W) : smulHom (𝒯 := 𝒯) g w = g • w := rfl

/--
@isnad1 id=eq.0h5v.s6.3674a6da0c1e from=translated src=- shape=6e9eeca8 vocab=676ae112
-/
@[simp] theorem smulHom_mapDart (g : G) (d : 𝒯.Dart) : (smulHom g).mapDart d = g • d := rfl

/--
@isnad1 id=eq.0h5v.s7.a528d6ba6b92 from=translated src=- shape=94f092d3 vocab=17e2a6b4
-/
theorem quotEdge_mk_smul (g : G) (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) (g • d) : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d :=
  Quotient.sound (mem_orbit d g)

def dartIndex [DecidableEq (QuotEdge G 𝒯)] (q : QuotEdge G 𝒯) (d : 𝒯.Dart) : ℤ :=
  (if Quotient.mk (orbitRel G 𝒯.Dart) d = q then 1 else 0) -
    (if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = q then 1 else 0)

def walkCycle [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯) {u v : W} (p : 𝒯.Walk u v) :
    E → ℤ :=
  fun e => (p.darts.map (dartIndex 𝒯 (orb e))).sum

variable {𝒯} in

def somePath {u v : W} (h : 𝒯.Reachable u v) : 𝒯.Path u v := by
  classical exact h.some.toPath

open scoped Classical in

def pathCycle [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯) (v₀ : W) (g : G) : E → ℤ :=
  if h : 𝒯.Reachable v₀ (g • v₀) then walkCycle 𝒯 orb (somePath h : 𝒯.Walk v₀ (g • v₀)) else 0

section lemmas

variable [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯)

/--
@isnad1 id=eq.0h5v.s6.b43f2fb8438b from=translated src=- shape=208a4f53 vocab=addbe1c2
-/
theorem dartIndex_symm (q : QuotEdge G 𝒯) (d : 𝒯.Dart) : dartIndex 𝒯 q d.symm = -dartIndex 𝒯 q d := by
  rw [dartIndex, dartIndex, SimpleGraph.Dart.symm_symm]; ring

/--
@isnad1 id=eq.0h6v.s6.2bb8b5f2672a from=translated src=- shape=d6052085 vocab=ace1b343
-/
theorem dartIndex_smul (q : QuotEdge G 𝒯) (g : G) (d : 𝒯.Dart) : dartIndex 𝒯 q (g • d) = dartIndex 𝒯 q d := by
  rw [dartIndex, dartIndex, smul_dart_symm, quotEdge_mk_smul, quotEdge_mk_smul]

/--
@isnad1 id=eq.0h6v.s6.1fb0a082bdaa from=translated src=- shape=78e4e39f vocab=78ece57b
-/
@[simp] theorem walkCycle_nil (u : W) : walkCycle 𝒯 orb (SimpleGraph.Walk.nil : 𝒯.Walk u u) = 0 := by
  funext e; simp [walkCycle]

/--
@isnad1 id=eq.1h10v.s7.8b126fc8fcef from=translated src=- shape=38b1d90c vocab=9feeda9b
-/
theorem walkCycle_cons {u v w : W} (h : 𝒯.Adj u v) (p : 𝒯.Walk v w) (e : E) :
    walkCycle 𝒯 orb (SimpleGraph.Walk.cons h p) e = dartIndex 𝒯 (orb e) ⟨(u, v), h⟩ + walkCycle 𝒯 orb p e := by
  simp [walkCycle]

/--
@isnad1 id=eq.0h10v.s7.ddc465cf80c2 from=translated src=- shape=d1aeeb0f vocab=c7937408
-/
theorem walkCycle_append {u v w : W} (p : 𝒯.Walk u v) (q : 𝒯.Walk v w) :
    walkCycle 𝒯 orb (p.append q) = walkCycle 𝒯 orb p + walkCycle 𝒯 orb q := by
  funext e; simp [walkCycle, SimpleGraph.Walk.darts_append, List.sum_append]

/--
@isnad1 id=eq.0h8v.s6.79b3a3c5bc43 from=translated src=- shape=10223c47 vocab=14b0a663
-/
theorem walkCycle_reverse {u v : W} (p : 𝒯.Walk u v) :
    walkCycle 𝒯 orb p.reverse = -walkCycle 𝒯 orb p := by
  funext e
  simp only [walkCycle, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map,
    Pi.neg_apply]
  induction p.darts with
  | nil => simp
  | cons d l ih => simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih, dartIndex_symm]; ring

/--
@isnad1 id=eq.0h9v.s7.a95db5e2f524 from=translated src=- shape=6880bd19 vocab=139c315a
-/
theorem walkCycle_map_smulHom {u v : W} (g : G) (p : 𝒯.Walk u v) :
    walkCycle 𝒯 orb (p.map (smulHom g)) = walkCycle 𝒯 orb p := by
  funext e
  simp only [walkCycle, SimpleGraph.Walk.darts_map, List.map_map]
  congr 1
  exact List.map_congr_left fun d _ => by rw [Function.comp_apply, smulHom_mapDart, dartIndex_smul]

/--
@isnad1 id=eq.1h7v.s6.a4cc10c83f51 from=translated src=- shape=1d017047 vocab=71afaa8d
-/
theorem pathCycle_of_not_reachable (v₀ : W) (g : G) (h : ¬𝒯.Reachable v₀ (g • v₀)) :
    pathCycle 𝒯 orb v₀ g = 0 := by
  rw [pathCycle, dite_eq_right h]

end lemmas

end Mumford
end CerednikDrinfeld

end
