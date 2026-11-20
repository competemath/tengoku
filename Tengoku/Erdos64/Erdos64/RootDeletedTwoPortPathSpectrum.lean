import Tengoku.Erdos64.Erdos64.RootDeletedTwoPortPath
import Tengoku.Erdos64.Erdos64.RootDeletedTwoPortNonadjacent
import Tengoku.Erdos64.Erdos64.TwoPortObstruction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A two-port root-deleted component supplies a positive port path, and in a
    dyadic-free ambient graph its two-root closure is necessarily non-dyadic.
@isnad1 id=ex.2h4v.s8.b98c27b1d006 from=translated src=- shape=71bf6d66 vocab=d3778171
-/
theorem rootDeletedComponent_twoPort_path_no_dyadic_closure
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno : ¬ HasPowerOfTwoCycle G) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2) :
    ∃ a b : V, ∃ p : G.Walk a b,
      a ≠ b ∧
      a ∈ rootDeletedComponentCarrier G r C ∧
      b ∈ rootDeletedComponentCarrier G r C ∧
      G.Adj r a ∧ G.Adj r b ∧
      p.IsPath ∧
      (∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) ∧
      r ∉ p.support ∧ 0 < p.length ∧
      (∀ k, 2 ≤ k → p.length + 2 ≠ 2 ^ k) := by
  obtain ⟨a, b, p, hab, ha, hb, hra, hrb, hp, hinside, hroot, hpos⟩ :=
    rootDeletedComponent_twoPort_path r C hcard
  refine ⟨a, b, p, hab, ha, hb, hra, hrb, hp, hinside, hroot, hpos, ?_⟩
  intro k hk hlen
  by_cases hlong : 1 < p.length
  · have hne := twoPort_path_length_ne_pow_two_sub_two hno hp hroot hra hrb
      hab hlong hk
    apply hne
    have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
    omega
  · have hple : p.length = 1 := by omega
    have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
    omega

/-- In the nonadjacent-port subcase, the extracted route is genuinely longer
    than one edge and its two-root closure is still non-dyadic. This is the
    route certificate paired with the separate dyadic residual route.
@isnad1 id=ex.3h4v.s8.20c9e78fde04 from=translated src=- shape=e194b807 vocab=d3778171
-/
theorem rootDeletedComponent_twoPort_nonadjacent_path_no_dyadic_closure
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno : ¬ HasPowerOfTwoCycle G) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2)
    (hnonadj : ∀ a b,
      a ∈ rootDeletedComponentCarrier G r C →
      b ∈ rootDeletedComponentCarrier G r C →
      G.Adj r a → G.Adj r b → a ≠ b → ¬ G.Adj a b) :
    ∃ a b : V, ∃ p : G.Walk a b,
      a ≠ b ∧
      a ∈ rootDeletedComponentCarrier G r C ∧
      b ∈ rootDeletedComponentCarrier G r C ∧
      G.Adj r a ∧ G.Adj r b ∧
      p.IsPath ∧
      (∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) ∧
      r ∉ p.support ∧ 1 < p.length ∧
      (∀ k, 2 ≤ k → p.length + 2 ≠ 2 ^ k) := by
  obtain ⟨a, b, p, hab, ha, hb, hra, hrb, hp, hinside, hroot, hlong⟩ :=
    rootDeletedComponent_twoPort_path_of_nonadjacent r C hcard hnonadj
  refine ⟨a, b, p, hab, ha, hb, hra, hrb, hp, hinside, hroot, hlong, ?_⟩
  intro k hk hlen
  have hne := twoPort_path_length_ne_pow_two_sub_two hno hp hroot hra hrb
    hab hlong hk
  apply hne
  have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
  omega

end Erdos64
