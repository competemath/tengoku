import Tengoku

namespace Lax979537Proofs.PersistentStack

variable {Node Symbol : Type}

abbrev Heap (Node Symbol : Type) := Set (Node × Symbol × Option Node)

def Functional (H : Heap Node Symbol) : Prop :=
  ∀ n a p b q, (n, a, p) ∈ H → (n, b, q) ∈ H → a = b ∧ p = q

def Fresh (H : Heap Node Symbol) (n : Node) : Prop := ∀ a p, (n, a, p) ∉ H

/-- A finite stack is represented by a chain of immutable node records. -/
inductive Chain (H : Heap Node Symbol) : Option Node → List Symbol → Prop
  | nil : Chain H none []
  | cons {n a p xs} : (n, a, p) ∈ H → Chain H p xs → Chain H (some n) (a :: xs)

/--
@isnad1 id=chain.2h6v.s5.a4a1280afcae from=translated src=- shape=c086f3e0 vocab=612993e3
-/
theorem Chain.mono {H G : Heap Node Symbol} (hHG : H ⊆ G) {p : Option Node} {xs : List Symbol}
    (h : Chain H p xs) : Chain G p xs := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (hHG hr) ih

/--
@isnad1 id=eq.3h6v.s5.a7274513f696 from=translated src=- shape=ab46f48c vocab=3f36a82d
-/
theorem Chain.unique {H : Heap Node Symbol} (hH : Functional H) {p : Option Node} {xs ys : List Symbol}
    (hx : Chain H p xs) (hy : Chain H p ys) : xs = ys := by
  induction hx generalizing ys with
  | nil => cases hy; rfl
  | @cons n a p xs hr hx ih =>
      cases hy with
      | @cons _ b q ys hs hy =>
          obtain ⟨rfl, rfl⟩ := hH n a p b q hr hs
          exact congrArg (a :: ·) (ih hy)

/--
@isnad1 id=iff.0h4v.s4.05581eb5d5ce from=translated src=- shape=ec142149 vocab=aef875e6
-/
theorem Chain.none_iff {H : Heap Node Symbol} {xs : List Symbol} : Chain H none xs ↔ xs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

/--
@isnad1 id=iff.0h4v.s4.9513c1263b9c from=translated src=- shape=195ed22a vocab=f22f2dc5
-/
theorem Chain.nil_iff {H : Heap Node Symbol} {p : Option Node} : Chain H p [] ↔ p = none := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

/--
@isnad1 id=iff.0h5v.s6.bd13c83929e5 from=translated src=- shape=651164f0 vocab=a0b244a5
-/
theorem Chain.some_iff {H : Heap Node Symbol} {n : Node} {xs : List Symbol} :
    Chain H (some n) xs ↔ ∃ a p ys, (n, a, p) ∈ H ∧ Chain H p ys ∧ xs = a :: ys := by
  constructor
  · intro h; cases h with | cons hr ht => exact ⟨_, _, _, hr, ht, rfl⟩
  · rintro ⟨a, p, ys, hr, ht, rfl⟩; exact .cons hr ht

/--
@isnad1 id=function.2h6v.s5.38e101b385a9 from=translated src=- shape=29de43ed vocab=9c97df75
-/
theorem insert_functional {H : Heap Node Symbol} (hH : Functional H) {n : Node}
    (hn : Fresh H n) (a : Symbol) (p : Option Node) : Functional (insert (n, a, p) H) := by
  intro m b q c r hb hc
  rcases Set.mem_insert_iff.mp hb with he | hb
  · cases he
    rcases Set.mem_insert_iff.mp hc with he | hc
    · cases he; exact ⟨rfl, rfl⟩
    · exact False.elim (hn c r hc)
  · rcases Set.mem_insert_iff.mp hc with he | hc
    · cases he; exact False.elim (hn b q hb)
    · exact hH m b q c r hb hc

/--
@isnad1 id=chain.1h7v.s6.4c0e872654b8 from=translated src=- shape=74b5d1b4 vocab=6288e8ea
-/
theorem push_chain {H : Heap Node Symbol} {p : Option Node} {xs : List Symbol}
    (h : Chain H p xs) (n : Node) (a : Symbol) : Chain (insert (n, a, p) H) (some n) (a :: xs) :=
  .cons (Set.mem_insert _ _) (h.mono (Set.subset_insert _ _))

/-- Positive lookup: the empty head is explicit, and a nonempty head uses
one node fact. No absence test on the heap is required. -/
def Read (H : Heap Node Symbol) (head : Option Node) (value : Option Symbol) (parent : Option Node) : Prop :=
  (head = none ∧ value = none ∧ parent = none) ∨
    ∃ n a, head = some n ∧ value = some a ∧ (n, a, parent) ∈ H

/--
@isnad1 id=read.2h7v.s5.f80b9710d0ce from=translated src=- shape=970692d7 vocab=237beed5
-/
theorem Read.mono {H G : Heap Node Symbol} (hHG : H ⊆ G) {head parent : Option Node}
    {value : Option Symbol} (h : Read H head value parent) : Read G head value parent := by
  rcases h with he | ⟨n, a, hh, hv, hr⟩
  · exact Or.inl he
  · exact Or.inr ⟨n, a, hh, hv, hHG hr⟩

/--
@isnad1 id=ex.1h5v.s5.e504e9363ad3 from=translated src=- shape=7a81f1fd vocab=d4ab556d
-/
theorem Chain.read_exists {H : Heap Node Symbol} {head : Option Node} {xs : List Symbol}
    (h : Chain H head xs) : ∃ parent, Read H head xs.head? parent ∧ Chain H parent xs.tail := by
  cases h with
  | nil => exact ⟨none, Or.inl ⟨rfl, rfl, rfl⟩, .nil⟩
  | @cons n a p xs hr ht => exact ⟨p, Or.inr ⟨n, a, rfl, rfl, hr⟩, ht⟩

/--
@isnad1 id=and.3h7v.s5.bf45d9bd0fd4 from=translated src=- shape=425b5fde vocab=41eddbdd
-/
theorem read_correct {H : Heap Node Symbol} (hH : Functional H)
    {head parent : Option Node} {xs : List Symbol} {value : Option Symbol}
    (h : Chain H head xs) (hr : Read H head value parent) :
    value = xs.head? ∧ Chain H parent xs.tail := by
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨n, a, rfl, rfl, hr⟩
  · cases h; exact ⟨rfl, .nil⟩
  · cases h with
    | @cons _ b q ys hs ht =>
        obtain ⟨rfl, rfl⟩ := hH n a parent b q hr hs
        exact ⟨rfl, ht⟩

/--
@isnad1 id=and.3h8v.s5.a5a89c90ff7c from=translated src=- shape=0e055d2e vocab=9954c5a8
-/
theorem read_unique {H : Heap Node Symbol} (hH : Functional H) {head p q : Option Node}
    {a b : Option Symbol} (ha : Read H head a p) (hb : Read H head b q) : a = b ∧ p = q := by
  rcases ha with ⟨rfl, rfl, rfl⟩ | ⟨n, a, rfl, rfl, ha⟩
  · rcases hb with ⟨_, rfl, rfl⟩ | ⟨n, b, he, _, _⟩
    · exact ⟨rfl, rfl⟩
    · cases he
  · rcases hb with ⟨he, _, _⟩ | ⟨m, b, he, rfl, hb⟩
    · cases he
    · cases he
      obtain ⟨rfl, rfl⟩ := hH n a p b q ha hb
      exact ⟨rfl, rfl⟩

/--
@isnad1 id=and.4h9v.s6.b8e35b399752 from=translated src=- shape=7c17edec vocab=0ee619b5
-/
theorem read_map_correct {A : Type} (f : A → Symbol) (hf : Function.Injective f)
    {H : Heap Node Symbol} (hH : Functional H) {head parent : Option Node}
    {xs : List A} {value : Option A} (h : Chain H head (xs.map f))
    (hr : Read H head (value.map f) parent) :
    value = xs.head? ∧ Chain H parent (xs.tail.map f) := by
  obtain ⟨hv, ht⟩ := read_correct hH h hr
  rw [List.head?_map] at hv
  refine ⟨Option.map_injective hf hv, ?_⟩
  simpa only [List.map_tail] using ht

end Lax979537Proofs.PersistentStack
