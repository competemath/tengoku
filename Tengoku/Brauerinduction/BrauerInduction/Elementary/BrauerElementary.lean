import Tengoku.Brauerinduction.BrauerInduction.Elementary.PElementary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brauer elementary groups

This file contains an API for Brauer elementary groups.

A group is **Brauer elementary** if it is `p`-elementary for some prime `p`.

 -/

universe u v

namespace BrauerInduction

/--
A group is **Brauer elementary** if it is `p`-elementary for some prime `p`.-/
def IsBrauerElementary (G : Type u) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ IsPElementary p G

namespace IsBrauerElementary

variable {p : ℕ}
variable {G : Type u} [Group G]
variable {G' : Type v} [Group G']

/--
A `p`-elementary group is Brauer elementary, provided `p` is prime.
@isnad1 id=isbrauer.1h2v.s4.7b3ab1620cf3 from=translated src=- shape=9194aace vocab=60de8814
-/
theorem ofIsPElementary
    (p : ℕ) [hp : Fact p.Prime]
    (hG : IsPElementary p G) :
    IsBrauerElementary G :=
  ⟨p, hp.out, hG⟩

/--
A group carrying explicit `p`-elementary structure is Brauer elementary,
provided `p` is prime.
@isnad1 id=isbrauer.0h3v.s4.6e1ac704bae5 from=translated src=- shape=9194aace vocab=cf9819b7
-/
theorem ofPElementary
    (p : ℕ) [hp : Fact p.Prime]
    (eG : PElementary p G) :
    IsBrauerElementary G :=
  ofIsPElementary (p := p) ⟨eG⟩

/--
A `p`-group is Brauer elementary.
@isnad1 id=isbrauer.1h2v.s4.a03aa79329b3 from=translated src=- shape=9194aace vocab=796e15ff
-/
theorem ofIsPGroup
    (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p G) :
    IsBrauerElementary G :=
  ofIsPElementary (p := p) (IsPElementary.ofIsPGroup (p := p) hG)

/--
Brauer elementarity is invariant under multiplicative equivalence.
@isnad1 id=isbrauer.1h3v.s5.f68303b2ba75 from=translated src=- shape=35640043 vocab=877c9077
-/
theorem ofMulEquiv
    (hG : IsBrauerElementary G) (φ : G ≃* G') :
    IsBrauerElementary G' := by
  rcases hG with ⟨p, hp, hpelem⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, IsPElementary.ofMulEquiv p hpelem φ⟩

/--
A subgroup of a Brauer elementary group is Brauer elementary.

This is the group-level version: if `K : Subgroup G`, then `K` is regarded as a
group in its own right.
@isnad1 id=isbrauer.1h2v.s5.b3e40b3684c4 from=translated src=- shape=2737fe64 vocab=2090b83e
-/
theorem ofSubgroup
    (hG : IsBrauerElementary G) (K : Subgroup G) :
    IsBrauerElementary K := by
  rcases hG with ⟨p, hp, ⟨eG⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, ⟨PElementary.ofSubgroup eG K⟩⟩

/--
Every finite cyclic group is Brauer elementary.
@isnad1 id=isbrauer.1h1v.s4.e0bb326487b3 from=translated src=- shape=affebb5f vocab=3a639318
-/
theorem of_isCyclic
    [Finite G] (hG : IsCyclic G) :
    IsBrauerElementary G := by
  let p : ℕ := 2
  haveI : Fact p.Prime := ⟨Nat.prime_two⟩
  haveI : IsCyclic G := hG
  exact ⟨p, Nat.prime_two, IsPElementary.of_isCyclic (p := p) (G := G)⟩

/--
Every finite Brauer elementary group is nilpotent.
@isnad1 id=isnilpot.1h1v.s3.cda9514fef96 from=translated src=- shape=affebb5f vocab=35ebbbf3
-/
theorem isNilpotent
    [Finite G] (hG : IsBrauerElementary G) :
    Group.IsNilpotent G := by
  rcases hG with ⟨p, hp, ⟨eG⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact eG.isNilpotent

/--
Every subgroup of a finite Brauer elementary group is nilpotent.
@isnad1 id=isnilpot.1h2v.s5.0f9c068a17e0 from=translated src=- shape=4ce0f501 vocab=53a611c9
-/
theorem isNilpotent_subgroup
    [Finite G] (hG : IsBrauerElementary G)
    (K : Subgroup G) :
    Group.IsNilpotent K := by
  have hK : IsBrauerElementary K := ofSubgroup hG K
  exact hK.isNilpotent

end IsBrauerElementary

end BrauerInduction
