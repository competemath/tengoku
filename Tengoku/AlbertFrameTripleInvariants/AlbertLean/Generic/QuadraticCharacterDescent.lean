import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.RingTheory.SimpleRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Data.tau_fixed_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Data.unique_tau_fixed` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Data.u_not_base` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Two coefficients on the tau-fixed field

Even and odd projection under delta give an explicit two-coefficient
decomposition on the tau-fixed field. The module assumes the displayed
commuting-automorphism data; identification of the common fixed field
with a concrete measurement field is a separate application.
-/
noncomputable section
namespace AlbertLean.Generic.QuadraticCharacterDescent

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω]

/-- Hypotheses concerning two actual commuting algebra automorphisms of a
field. No dimension, irreducibility, or degree is assumed.-/
structure Data where
  tau : Ω ≃ₐ[k] Ω
  delta : Ω ≃ₐ[k] Ω
  tau_involutive : Function.Involutive tau
  delta_involutive : Function.Involutive delta
  commute : Function.Commute tau delta
  kappa : Ω
  eta : Ω
  kappa_ne : kappa ≠ 0
  eta_ne : eta ≠ 0
  tau_kappa : tau kappa = -kappa
  delta_kappa : delta kappa = kappa
  tau_eta : tau eta = -eta
  delta_eta : delta eta = -eta
  joint_fixed : ∀ x : Ω, (tau x = x ∧ delta x = x) ↔
    ∃ a : k, algebraMap k Ω a = x

namespace Data
variable (D : Data (k := k) (Ω := Ω))

def u : Ω := D.kappa * D.eta

theorem u_ne : D.u ≠ 0 := mul_ne_zero D.kappa_ne D.eta_ne

theorem tau_u : D.tau D.u = D.u := by
  simp [u, D.tau_kappa, D.tau_eta]

theorem delta_u : D.delta D.u = -D.u := by
  simp [u, D.delta_kappa, D.delta_eta]

/-- Direct two-coefficient descent on the tau-fixed field.-/
theorem tau_fixed_iff (x : Ω) : D.tau x = x ↔
    ∃ a d : k, x = algebraMap k Ω a + algebraMap k Ω d * D.u := by
  constructor
  · intro hx
    let p := (x + D.delta x) / 2
    let q := (x - D.delta x) / (2 * D.u)
    have hp : D.tau p = p ∧ D.delta p = p := by
      constructor
      · simp only [p, map_div₀, map_add, map_ofNat D.tau 2, D.commute x, hx]
      · simp only [p, map_div₀, map_add, map_ofNat D.delta 2, D.delta_involutive x]
        ring
    have hq : D.tau q = q ∧ D.delta q = q := by
      constructor
      · simp only [q, map_div₀, map_sub, map_mul, map_ofNat D.tau 2,
          D.tau_u, D.commute x, hx]
      · simp only [q, map_div₀, map_sub, map_mul, map_ofNat D.delta 2,
          D.delta_u, D.delta_involutive x]
        field_simp [D.u_ne]
        ring
    obtain ⟨a,ha⟩ := (D.joint_fixed p).mp hp
    obtain ⟨d,hd⟩ := (D.joint_fixed q).mp hq
    refine ⟨a,d,?_⟩
    rw [ha, hd]
    dsimp [p, q]
    field_simp [D.u_ne]
    ring
  · rintro ⟨a,d,rfl⟩
    simp [D.tau_u]

/-- Uniqueness follows from applying delta to one two-term relation.-/
theorem unique_tau_fixed (x : Ω) (hx : D.tau x = x) :
    ∃! v : k × k, algebraMap k Ω v.1 + algebraMap k Ω v.2 * D.u = x := by
  obtain ⟨a,d,h⟩ := (D.tau_fixed_iff x).mp hx
  refine ⟨(a,d),h.symm,?_⟩
  rintro ⟨a',d'⟩ hv
  have he := hv.trans h
  have hδ := congrArg D.delta he
  simp only [map_add, map_mul, D.delta.commutes, D.delta_u] at hδ
  have ha2 : (2 : Ω) * (algebraMap k Ω a' - algebraMap k Ω a) = 0 := by
    linear_combination he + hδ
  have hd2 : (2 : Ω) * ((algebraMap k Ω d' - algebraMap k Ω d) * D.u) = 0 := by
    linear_combination he - hδ
  have h2 : (2 : Ω) ≠ 0 := by norm_num
  have ha : a' = a := (algebraMap k Ω).injective
    (sub_eq_zero.mp ((mul_eq_zero.mp ha2).resolve_left h2))
  have hd : d' = d := (algebraMap k Ω).injective (sub_eq_zero.mp
    ((mul_eq_zero.mp ((mul_eq_zero.mp hd2).resolve_left h2)).resolve_right D.u_ne))
  exact Prod.ext ha hd

/-- The product direction is non-base and is reversed by the deck map.-/
theorem u_not_base : ¬ ∃ a : k, algebraMap k Ω a = D.u := by
  rintro ⟨a,ha⟩
  have hδ : D.delta D.u = D.u := by rw [← ha]; exact D.delta.commutes a
  have hz : D.u = 0 := by
    have hm : (2 : Ω) * D.u = 0 := by rw [D.delta_u] at hδ; linear_combination -hδ
    exact (mul_eq_zero.mp hm).resolve_left (by norm_num)
  exact D.u_ne hz

end Data

end AlbertLean.Generic.QuadraticCharacterDescent
