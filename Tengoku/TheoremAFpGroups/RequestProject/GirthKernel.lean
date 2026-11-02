module

public import Tengoku.TheoremAFpGroups.RequestProject.GirthCheck
public import Tengoku.TheoremAFpGroups.RequestProject.TripleSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A kernel-friendly girth checker

The checker of `GirthCheck.lean` is run on a graph with vertex set `ℕ` whose neighbour lists are
stored in a binary tree (`NTree`, logarithmic lookup), and duplicate detection uses bit masks
(`bitsNodup`).  All operations are on natural numbers, for which Lean's kernel has built-in
arithmetic, so the finite checks can be discharged by `decide +kernel` without `native_decide`.

`twelve_le_egirth_incidence` transfers the bound to `TripleSystem.incidenceGraph` along the
injective graph homomorphism `inl v ↦ v`, `inr l ↦ r + l`.
-/

@[expose] public section

namespace GirthKernel

open SimpleGraph

/-- Binary (Braun-indexed) tree of neighbour lists.-/
inductive NTree : Type
  | leaf : NTree
  | node : NTree → List ℕ → NTree → NTree

/-- Lookup: index `0` at the root, odd indices on the left, even positive ones on the right.-/
def NTree.get : NTree → ℕ → List ℕ
  | .leaf, _ => []
  | .node l x r, i => if i = 0 then x else if i % 2 = 1 then l.get (i / 2) else r.get (i / 2 - 1)

/-- Membership in a list of naturals, via `Nat.beq`.-/
def memN (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => Nat.beq a b || memN a l

theorem memN_iff (a : ℕ) (l : List ℕ) : memN a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memN]
  | cons b l ih => rw [memN, Bool.or_eq_true, ih, List.mem_cons, Nat.beq_eq]

/-- Duplicate detection with a bit mask.-/
def bitsNodup : List ℕ → ℕ → Bool
  | [], _ => true
  | x :: xs, acc => !(acc.testBit x) && bitsNodup xs (acc ||| (1 <<< x))

theorem bitsNodup_sound : ∀ (l : List ℕ) (acc : ℕ), bitsNodup l acc = true →
    l.Nodup ∧ ∀ x ∈ l, acc.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: xs, acc, h => by
    simp only [bitsNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hrest⟩ := bitsNodup_sound xs _ h.2
    refine ⟨List.nodup_cons.2 ⟨fun hmem => ?_, hx⟩, ?_⟩
    · have := hrest x hmem
      simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h.1
      · have := hrest y hy
        simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

variable (N : ℕ) (t : NTree)

/-- Symmetrised, bounded neighbour function.-/
def nbrs (a : ℕ) : List ℕ :=
  if a < N then (t.get a).filter (fun b => decide (b < N) && memN a (t.get b) && decide (a ≠ b))
  else []

/-- The graph on `ℕ` described by the tree.-/
def graph : SimpleGraph ℕ where
  Adj a b := a < N ∧ b < N ∧ b ∈ t.get a ∧ a ∈ t.get b ∧ a ≠ b
  symm := ⟨fun _ _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h2, h1, h4, h3, Ne.symm h5⟩⟩
  loopless := ⟨fun _ h => h.2.2.2.2 rfl⟩

theorem adj_iff (a b : ℕ) : (graph N t).Adj a b ↔ b ∈ nbrs N t a := by
  simp only [graph, nbrs]
  split_ifs with ha
  · simp only [List.mem_filter, memN_iff, Bool.and_eq_true, decide_eq_true_eq, ha, true_and]
    tauto
  · simp [ha]

/-- The local check with a bit-mask duplicate test.-/
def localCheckN (nbrs : ℕ → List ℕ) (x : ℕ) : Bool :=
  bitsNodup (((List.range 6).flatMap (GirthCheck.pathsTo nbrs x)).map (fun p => p.headD 0)) 0

theorem pathsTo_ne_nil (nb : ℕ → List ℕ) (x : ℕ) :
    ∀ n, ∀ p ∈ GirthCheck.pathsTo nb x n, p ≠ []
  | 0, p, hp => by simp [GirthCheck.pathsTo] at hp; simp [hp]
  | n + 1, p, hp => by
    simp only [GirthCheck.pathsTo, List.mem_flatMap] at hp
    obtain ⟨q, -, hq⟩ := hp
    rcases q with _ | ⟨v, q⟩
    · simp [GirthCheck.extend] at hq
    · simp only [GirthCheck.extend, List.mem_map] at hq
      obtain ⟨w, -, rfl⟩ := hq
      simp

theorem localCheck_of_localCheckN (nb : ℕ → List ℕ) (x : ℕ) (h : localCheckN nb x = true) :
    GirthCheck.localCheck nb x = true := by
  simp only [GirthCheck.localCheck, decide_eq_true_eq]
  have hnd := (bitsNodup_sound _ _ h).1
  have hmap : ((List.range 6).flatMap (GirthCheck.pathsTo nb x)).map List.head? =
      (((List.range 6).flatMap (GirthCheck.pathsTo nb x)).map (fun p => p.headD 0)).map some := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    obtain ⟨n, -, hn⟩ := List.mem_flatMap.1 hp
    have := pathsTo_ne_nil nb x n p hn
    rcases p with _ | ⟨v, p⟩
    · exact absurd rfl this
    · rfl
  rw [hmap]
  exact hnd.map (Option.some_injective _)

theorem localCheck_of_ge (x : ℕ) (hx : N ≤ x) : GirthCheck.localCheck (nbrs N t) x = true := by
  have h1 : GirthCheck.pathsTo (nbrs N t) x 1 = [] := by
    simp [GirthCheck.pathsTo, GirthCheck.extend, nbrs, Nat.not_lt.2 hx]
  have h : ∀ n, GirthCheck.pathsTo (nbrs N t) x (n + 1) = [] := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih => rw [GirthCheck.pathsTo, ih]; rfl
  simp only [GirthCheck.localCheck, decide_eq_true_eq]
  rw [show List.range 6 = [0, 0 + 1, 1 + 1, 2 + 1, 3 + 1, 4 + 1] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, h]
  simp [GirthCheck.pathsTo]

/-- The bounded girth checker.-/
def girthCheckN (r : ℕ) : Bool :=
  (List.range N).all (fun a => localCheckN (nbrs N t) a &&
    (t.get a).all (fun b => decide ((a < r) ≠ (b < r))))

/-- The incidence condition: every entry `v` of the `l`-th triple is adjacent to `r + l`.-/
def incCheck (r : ℕ) : ℕ → List TripleSystem.Triple → Bool
  | _, [] => true
  | l, x :: T => x.entries.all (fun v => memN (r + l) (t.get v) && memN v (t.get (r + l))) &&
      incCheck r (l + 1) T

theorem incCheck_spec (r : ℕ) : ∀ (T : List TripleSystem.Triple) (l₀ : ℕ),
    incCheck t r l₀ T = true → ∀ (l : ℕ) (hl : l < T.length), ∀ v ∈ T[l].entries,
      r + (l₀ + l) ∈ t.get v ∧ v ∈ t.get (r + (l₀ + l))
  | [], _, _, l, hl => absurd hl (by simp)
  | x :: T, l₀, h, l, hl => by
    simp only [incCheck, Bool.and_eq_true, List.all_eq_true] at h
    rcases l with _ | l
    · intro v hv
      have := h.1 v hv
      simp only [memN_iff] at this
      simpa using this
    · intro v hv
      have := incCheck_spec r T (l₀ + 1) h.2 l (by simpa using hl) v hv
      simpa [Nat.add_assoc, Nat.add_comm 1 l] using this

end GirthKernel

end
