import Tengoku.DeletionCodesLean.DeletionCode.WordPaths
import Tengoku.Seed.Data.Nat.Find
import Tengoku.Seed.Logic.Relation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms supplier_adjacent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_minimal_in_component` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms component_root_windows` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms component_root_subword` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Concrete selection of a root in every component of a family of word paths.

The paths carry actual letters and finite lengths. Generating means that each
negative L-window occurs in x or on an earlier family's path. Adjacency is
defined by equal, in-bounds (L-1)-letter stretches, not an assumed supplier
closure. Least rank therefore supplies a member whose whole negative path
occurs in a k-unique x. This does not yet define manuscript rules or a decoder.
-/

namespace DeletionCode.RootSelection

open Windows

/-- Side false is negative; side true is positive. Each side has length L+extra.-/
structure Family (B : Type*) where
  rank : B → ℕ
  path : B → Bool → Letters
  extra : B → Bool → ℕ

namespace Family

/-- Every negative window occurs in x or in an earlier path of the family.-/
def Generating {B : Type*} (F : Family B) (x : Letters) (n L : ℕ) : Prop :=
  ∀ b i, i ≤ F.extra b false →
    WordPaths.Occurs x n (F.path b false) i L ∨
      ∃ a side j, F.rank a < F.rank b ∧ j ≤ F.extra a side ∧
        Agree (F.path b false) i (F.path a side) j L

/-- Actual common vertices, with valid offsets on the two finite word paths.-/
def Adjacent {B : Type*} (F : Family B) (L : ℕ) (a b : B) : Prop :=
  ∃ sideA sideB i j,
    i ≤ F.extra a sideA + 1 ∧ j ≤ F.extra b sideB + 1 ∧
    i + (L - 1) ≤ L + F.extra a sideA ∧
    j + (L - 1) ≤ L + F.extra b sideB ∧
    Agree (F.path a sideA) i (F.path b sideB) j (L - 1)

/-- Undirected connectedness of the actual common-vertex relation.-/
def Connected {B : Type*} (F : Family B) (L : ℕ) : B → B → Prop :=
  Relation.EqvGen (F.Adjacent L)

/-- Sharing an entire valid gram also gives a common de Bruijn vertex.
@isnad1 id=adjacent.3h8v.s5.44d52fec2bc2 from=translated src=- shape=e34a1fbf vocab=96f75ae9
-/
theorem supplier_adjacent {B : Type*} (F : Family B) (L : ℕ)
    (b a : B) (side : Bool) (i j : ℕ)
    (hi : i ≤ F.extra b false) (hj : j ≤ F.extra a side)
    (hgram : Agree (F.path b false) i (F.path a side) j L) :
    F.Adjacent L b a := by
  refine ⟨false, side, i, j, by omega, by omega, by omega, by omega, ?_⟩
  intro q hq
  exact hgram q (by omega)

/-- Natural-number rank has a least value in every nonempty component.
@isnad1 id=ex.0h4v.s5.7672f8a72bcb from=translated src=- shape=5f099c51 vocab=7695a73f
-/
theorem exists_minimal_in_component {B : Type*} (F : Family B) (L : ℕ) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ a, F.Connected L a b → F.rank r ≤ F.rank a := by
  classical
  let P : ℕ → Prop := fun k => ∃ a, F.Connected L a b ∧ F.rank a = k
  have hex : ∃ k, P k := ⟨F.rank b, b, Relation.EqvGen.refl b, rfl⟩
  obtain ⟨r, hr, hrank⟩ := Nat.find_spec hex
  refine ⟨r, hr, ?_⟩
  intro a ha
  have hle : Nat.find hex ≤ F.rank a := Nat.find_min' hex ⟨a, ha, rfl⟩
  omega

/-- Every component has a member whose negative windows all occur in x.
No rootedness or supplier-closure hypothesis is assumed.
@isnad1 id=ex.1h6v.s5.bd832928ef66 from=translated src=- shape=c438506b vocab=bf9ff923
-/
theorem component_root_windows {B : Type*} (F : Family B)
    (x : Letters) (n L : ℕ) (hgen : F.Generating x n L) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ i, i ≤ F.extra r false → WordPaths.Occurs x n (F.path r false) i L := by
  obtain ⟨r, hr, hmin⟩ := F.exists_minimal_in_component L b
  refine ⟨r, hr, ?_⟩
  intro i hi
  rcases hgen r i hi with hx | ⟨a, side, j, hearlier, hj, hgram⟩
  · exact hx
  · have hadj : F.Adjacent L r a := F.supplier_adjacent L r a side i j hi hj hgram
    have haconn : F.Connected L a b :=
      Relation.EqvGen.trans a r b
        (Relation.EqvGen.symm r a (Relation.EqvGen.rel r a hadj)) hr
    have hle := hmin a haconn
    omega

/-- A component root's entire negative word is a genuine contiguous subword of x.
@isnad1 id=ex.3h7v.s6.fcc4aab25352 from=translated src=- shape=fb5a636c vocab=9f25cfbd
-/
theorem component_root_subword {B : Type*} (F : Family B)
    (x : Letters) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hgen : F.Generating x n L) (b : B) :
    ∃ r a, F.Connected L r b ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by
  obtain ⟨r, hr, hwindows⟩ := F.component_root_windows x n L hgen b
  obtain ⟨a, ha, hagree⟩ := WordPaths.all_windows_occur_implies_subword
    x (F.path r false) n k L (F.extra r false) hx hk hwindows
  exact ⟨r, a, hr, ha, hagree⟩

end Family

end DeletionCode.RootSelection
