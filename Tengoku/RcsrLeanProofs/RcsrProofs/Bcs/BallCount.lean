/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/
import Tengoku.Seed.Data.Int.Interval
import Tengoku.Seed.Data.Finset.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Counting toolkit for the bcs level sets

Two lemmas shared by the even- and odd-parity counting files:

* `card_filter_prod3`: a filter by three independent coordinate predicates over
  a box factors as a product of three one-dimensional filtered counts.
* `card_xyz_uvw`: the change of variables `(s,u,v) = (x+y+z, x-y+z, -x+y+z)`
  transfers a filtered count over the `(x,y,z)` box to a filtered count over an
  `(s,u,v)` box carrying the same-parity constraint, given confinement of the
  predicate to both boxes. The map is linear and injective; its image is
  exactly the all-same-parity sublattice.
-/

namespace Bcs

open Finset

/-- Triple product-filter factorization: independent coordinate predicates.
@isnad1 id=eq.0h6v.s7.4b1efb64f8ec from=translated src=- shape=b6846423 vocab=60451990
-/
theorem card_filter_prod3 (A B C : Finset Int) (P Q R : Int → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] :
    ((A ×ˢ B ×ˢ C).filter fun p => P p.1 ∧ Q p.2.1 ∧ R p.2.2).card
      = (A.filter P).card * (B.filter Q).card * (C.filter R).card := by
  have h1 : ((A ×ˢ B ×ˢ C).filter fun p => P p.1 ∧ Q p.2.1 ∧ R p.2.2)
      = A.filter P ×ˢ ((B ×ˢ C).filter fun q => Q q.1 ∧ R q.2) := by
    rw [← filter_product]
  rw [h1, card_product, filter_product, card_product, Nat.mul_assoc]

/-- Change of variables `(x,y,z) ↦ (x+y+z, x-y+z, -x+y+z)`: counts transfer
from the `(x,y,z)` box to the same-parity sublattice of the `(s,u,v)` box,
provided the predicate confines its solutions to both boxes.
@isnad1 id=eq.2h3v.s10.b7bfee6030db from=translated src=- shape=884a428d vocab=5092be48
-/
theorem card_xyz_uvw (n N : ℕ) (F : Int → Int → Int → Prop)
    [∀ s u v, Decidable (F s u v)]
    (hxyz : ∀ x y z : Int, F (x+y+z) (x-y+z) (-x+y+z) →
      x ∈ Icc (-(n:Int)) n ∧ y ∈ Icc (-(n:Int)) n ∧ z ∈ Icc (-(n:Int)) n)
    (huvw : ∀ s u v : Int, F s u v →
      s ∈ Icc (-(N:Int)) N ∧ u ∈ Icc (-(N:Int)) N ∧ v ∈ Icc (-(N:Int)) N) :
    ((Icc (-(n:Int)) n ×ˢ Icc (-(n:Int)) n ×ˢ Icc (-(n:Int)) n).filter
        fun p => F (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2) (-p.1 + p.2.1 + p.2.2)).card
      = ((Icc (-(N:Int)) N ×ˢ Icc (-(N:Int)) N ×ˢ Icc (-(N:Int)) N).filter
          fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
            F q.1 q.2.1 q.2.2).card := by
  refine Finset.card_bij'
    (fun p _ => (p.1 + p.2.1 + p.2.2, p.1 - p.2.1 + p.2.2, -p.1 + p.2.1 + p.2.2))
    (fun q _ => ((q.1 - q.2.2) / 2, (q.1 - q.2.1) / 2, (q.2.1 + q.2.2) / 2))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp ⊢
    obtain ⟨-, hF⟩ := hp
    obtain ⟨hs, hu, hv⟩ := huvw _ _ _ hF
    simp only [mem_Icc] at hs hu hv
    exact ⟨⟨hs, hu, hv⟩, ⟨by omega, by omega⟩, hF⟩
  · rintro ⟨s, u, v⟩ hq
    simp only [mem_filter, mem_product, mem_Icc] at hq ⊢
    obtain ⟨-, ⟨hp1, hp2⟩, hF⟩ := hq
    have hx : (s - v) / 2 + (s - u) / 2 + (u + v) / 2 = s := by omega
    have hy : (s - v) / 2 - (s - u) / 2 + (u + v) / 2 = u := by omega
    have hz : -((s - v) / 2) + (s - u) / 2 + (u + v) / 2 = v := by omega
    rw [hx, hy, hz]
    obtain ⟨hxb, hyb, hzb⟩ := hxyz ((s - v) / 2) ((s - u) / 2) ((u + v) / 2)
      (by rw [hx, hy, hz]; exact hF)
    simp only [mem_Icc] at hxb hyb hzb
    exact ⟨⟨hxb, hyb, hzb⟩, hF⟩
  · rintro ⟨x, y, z⟩ _
    have h1 : (x + y + z - (-x + y + z)) / 2 = x := by omega
    have h2 : (x + y + z - (x - y + z)) / 2 = y := by omega
    have h3 : (x - y + z + (-x + y + z)) / 2 = z := by omega
    simp only [h1, h2, h3]
  · rintro ⟨s, u, v⟩ hq
    simp only [mem_filter, mem_product, mem_Icc] at hq
    obtain ⟨-, ⟨hp1, hp2⟩, -⟩ := hq
    have h1 : (s - v) / 2 + (s - u) / 2 + (u + v) / 2 = s := by omega
    have h2 : (s - v) / 2 - (s - u) / 2 + (u + v) / 2 = u := by omega
    have h3 : -((s - v) / 2) + (s - u) / 2 + (u + v) / 2 = v := by omega
    simp only [h1, h2, h3]

end Bcs
