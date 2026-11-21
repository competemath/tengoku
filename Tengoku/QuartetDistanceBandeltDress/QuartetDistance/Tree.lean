import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Circular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Binary phylogenetic trees and their rotation profiles

An unrooted binary phylogenetic tree is cut at a distinguished leaf.  What
remains is a full binary tree; swapping the two sons at every fork enumerates
the rotation systems of the original tree.  We retain multiplicities, since
different rotation systems can have the same frontier.
-/

namespace QuartetDistance

namespace Tree

/-- A (nonempty) full binary tree whose leaves carry labels in `α`.-/
inductive FullTree (α : Type*) where
  | leaf : α → FullTree α
  | fork : FullTree α → FullTree α → FullTree α
deriving DecidableEq, Repr

namespace FullTree

/-- The leaf labels, in the reference planar embedding.-/
def leaves : FullTree α → List α
  | leaf a => [a]
  | fork l r => leaves l ++ leaves r

/-- Number of internal vertices (and hence binary rotation choices).-/
def forks : FullTree α → ℕ
  | leaf _ => 0
  | fork l r => forks l + forks r + 1

/-- All oriented frontiers, with one occurrence for every rotation system.-/
def frontierProfile : FullTree α → Multiset (List α)
  | leaf a => {[a]}
  | fork l r =>
      (frontierProfile l).bind fun xs =>
        (frontierProfile r).bind fun ys =>
          {xs ++ ys, ys ++ xs}

/-- The binary product used at a fork of a rotation profile.-/
def joinProfile (A B : Multiset (List α)) : Multiset (List α) :=
  A.bind fun xs => B.bind fun ys => {xs ++ ys, ys ++ xs}

/--
@isnad1 id=eq.0h2v.s4.bef38fd57507 from=translated src=- shape=1d56102d vocab=2c5969a2
-/
@[simp] theorem leaves_leaf (a : α) : (leaf a).leaves = [a] := rfl

/--
@isnad1 id=eq.0h3v.s5.50be9ee34fdc from=translated src=- shape=d5b129b6 vocab=bb42c629
-/
@[simp] theorem leaves_fork (l r : FullTree α) :
    (fork l r).leaves = l.leaves ++ r.leaves := rfl

/--
@isnad1 id=eq.0h2v.s4.b8ccad7e17bd from=translated src=- shape=d0dfd432 vocab=7e182630
-/
@[simp] theorem forks_leaf (a : α) : (leaf a).forks = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.40ba9512295c from=translated src=- shape=6c8effa6 vocab=0c6e8257
-/
@[simp] theorem forks_fork (l r : FullTree α) :
    (fork l r).forks = l.forks + r.forks + 1 := rfl

/--
@isnad1 id=eq.0h2v.s4.4c69dcc92406 from=translated src=- shape=eb52ed46 vocab=e4b2d7e5
-/
@[simp] theorem frontierProfile_leaf (a : α) :
    (leaf a).frontierProfile = {[a]} := rfl

/--
@isnad1 id=eq.0h3v.s4.cb625f45686b from=translated src=- shape=561ba3c5 vocab=e223ef29
-/
@[simp] theorem frontierProfile_fork (l r : FullTree α) :
    (fork l r).frontierProfile = joinProfile l.frontierProfile r.frontierProfile := rfl

/--
@isnad1 id=eq.0h4v.s6.b64d93fa1989 from=translated src=- shape=f5a65a7f vocab=361a903d
-/
theorem joinProfile_add_left (A B C : Multiset (List α)) :
    joinProfile (A + B) C = joinProfile A C + joinProfile B C := by
  simp [joinProfile, Multiset.add_bind]
  ac_rfl

/--
@isnad1 id=eq.0h4v.s6.0c7aeb6cf354 from=translated src=- shape=3db846ba vocab=cc89bc7b
-/
theorem joinProfile_nsmul_left (k : ℕ) (A B : Multiset (List α)) :
    joinProfile (k • A) B = k • joinProfile A B := by
  induction k with
  | zero => simp [joinProfile]
  | succ k ih =>
      rw [succ_nsmul, joinProfile_add_left, ih, succ_nsmul]

/--
@isnad1 id=eq.0h4v.s6.7564e6fd7a36 from=translated src=- shape=370ec009 vocab=361a903d
-/
theorem joinProfile_add_right (A B C : Multiset (List α)) :
    joinProfile A (B + C) = joinProfile A B + joinProfile A C := by
  simp [joinProfile, Multiset.bind_add]
  ac_rfl

/--
@isnad1 id=eq.0h4v.s6.8f2a5d22c343 from=translated src=- shape=f578dca5 vocab=cc89bc7b
-/
theorem joinProfile_nsmul_right (k : ℕ) (A B : Multiset (List α)) :
    joinProfile A (k • B) = k • joinProfile A B := by
  induction k with
  | zero => simp [joinProfile]
  | succ k ih =>
      rw [succ_nsmul, joinProfile_add_right, ih, succ_nsmul]

/--
@isnad1 id=eq.0h5v.s7.ba56e1448df4 from=translated src=- shape=cf36b653 vocab=6e65bc69
-/
theorem joinProfile_nsmul (k m : ℕ) (A B : Multiset (List α)) :
    joinProfile (k • A) (m • B) = (k * m) • joinProfile A B := by
  rw [joinProfile_nsmul_left, joinProfile_nsmul_right]
  rw [← mul_nsmul, Nat.mul_comm]

/--
@isnad1 id=eq.0h2v.s6.4cbfeb657e2b from=translated src=- shape=48fcb58b vocab=dbcbbb78
-/
@[simp] theorem joinProfile_singleton_nil_left [DecidableEq α]
    (B : Multiset (List α)) :
    joinProfile {[]} B = 2 • B := by
  apply Multiset.ext.mpr
  intro xs
  simp [joinProfile, Multiset.count_nsmul]
  omega

/--
@isnad1 id=eq.0h2v.s6.4ebed9d285d2 from=translated src=- shape=be39d520 vocab=dbcbbb78
-/
@[simp] theorem joinProfile_singleton_nil_right [DecidableEq α]
    (A : Multiset (List α)) :
    joinProfile A {[]} = 2 • A := by
  apply Multiset.ext.mpr
  intro xs
  have hid : A.bind (fun x => {x}) = A := by
    rw [Multiset.bind_singleton]
    exact Multiset.map_id A
  simp [joinProfile, Multiset.count_nsmul, hid]
  omega

/--
@isnad1 id=ne.0h2v.s3.2838cdfe7b99 from=translated src=- shape=9b57408e vocab=110e595b
-/
@[simp] theorem leaves_ne_nil (t : FullTree α) : t.leaves ≠ [] := by
  induction t with
  | leaf => simp
  | fork l r ihl ihr => simp [leaves, ihl]

/--
@isnad1 id=lt.0h2v.s4.a99ae6faa4c1 from=translated src=- shape=ed46282e vocab=b78eb529
-/
@[simp] theorem leaves_length_pos (t : FullTree α) : 0 < t.leaves.length := by
  have h : t.leaves.length ≠ 0 := by
    simp
  omega

/--
@isnad1 id=eq.1h3v.s5.cdcdc7195300 from=translated src=- shape=79f50aaf vocab=82d3c86f
-/
theorem mem_frontierProfile_length (t : FullTree α) {xs : List α}
    (hxs : xs ∈ t.frontierProfile) : xs.length = t.leaves.length := by
  induction t generalizing xs with
  | leaf a =>
      simp only [frontierProfile_leaf, Multiset.mem_singleton] at hxs
      subst xs
      rfl
  | fork l r ihl ihr =>
      simp only [frontierProfile_fork, joinProfile, Multiset.mem_bind] at hxs
      obtain ⟨xl, hxl, xr, hxr, hxs⟩ := hxs
      simp at hxs
      rcases hxs with rfl | rfl
      · simp [ihl hxl, ihr hxr]
      · simp [ihl hxl, ihr hxr, Nat.add_comm]

/--
@isnad1 id=perm.1h3v.s4.b179896a54a5 from=translated src=- shape=78f7a55d vocab=1319ef5c
-/
theorem mem_frontierProfile_perm (t : FullTree α) {xs : List α}
    (hxs : xs ∈ t.frontierProfile) : xs.Perm t.leaves := by
  induction t generalizing xs with
  | leaf a =>
      simp only [frontierProfile_leaf, Multiset.mem_singleton] at hxs
      subst xs
      rfl
  | fork l r ihl ihr =>
      simp only [frontierProfile_fork, joinProfile, Multiset.mem_bind] at hxs
      obtain ⟨xl, hxl, xr, hxr, hxs⟩ := hxs
      simp at hxs
      rcases hxs with rfl | rfl
      · exact (ihl hxl).append (ihr hxr)
      · exact ((ihr hxr).append (ihl hxl)).trans List.perm_append_comm

/--
@isnad1 id=eq.0h2v.s5.a20a9ac0fee9 from=translated src=- shape=7fc28b5b vocab=3f1960b2
-/
@[simp] theorem card_frontierProfile (t : FullTree α) :
    t.frontierProfile.card = 2 ^ t.forks := by
  induction t with
  | leaf => simp [frontierProfile, forks]
  | fork l r ihl ihr =>
      simp [frontierProfile, forks, ihl, ihr, pow_add, Nat.mul_comm]
      omega

/-! ### Combinatorial restriction and suppression -/

/-- Delete labels outside `S` from a linear frontier.-/
def restrictList [DecidableEq α] (S : Finset α) (xs : List α) : List α :=
  xs.filter fun a => a ∈ S

/--
@isnad1 id=eq.0h2v.s4.e52ce0d3aa39 from=translated src=- shape=6fd94109 vocab=53513e03
-/
@[simp] theorem restrictList_nil [DecidableEq α] (S : Finset α) :
    restrictList S [] = [] := rfl

/--
@isnad1 id=eq.0h4v.s5.fd15e63bf321 from=translated src=- shape=30277119 vocab=27dabb9f
-/
@[simp] theorem restrictList_append [DecidableEq α] (S : Finset α)
    (xs ys : List α) :
    restrictList S (xs ++ ys) = restrictList S xs ++ restrictList S ys := by
  simp [restrictList]

/--
@isnad1 id=eq.0h4v.s5.5e4dc45d2302 from=translated src=- shape=498e51e7 vocab=63467de6
-/
theorem map_restrictList_joinProfile [DecidableEq α] (S : Finset α)
    (A B : Multiset (List α)) :
    (joinProfile A B).map (restrictList S) =
      joinProfile (A.map (restrictList S)) (B.map (restrictList S)) := by
  simp [joinProfile, Multiset.map_bind, Multiset.bind_map, restrictList_append]

/-- Restriction to `S`, with empty branches deleted and unary forks suppressed.-/
def prune [DecidableEq α] : FullTree α → Finset α → Option (FullTree α)
  | leaf a, S => if a ∈ S then some (leaf a) else none
  | fork l r, S =>
      match prune l S, prune r S with
      | none, none => none
      | some l', none => some l'
      | none, some r' => some r'
      | some l', some r' => some (fork l' r')

/-- A profile for an optional pruned tree; the empty tree has the empty word.-/
def optionProfile : Option (FullTree α) → Multiset (List α)
  | none => {[]}
  | some t => t.frontierProfile

/-- Fork choices forgotten when restriction deletes or suppresses vertices.-/
def suppressedForks [DecidableEq α] : FullTree α → Finset α → ℕ
  | leaf _, _ => 0
  | fork l r, S =>
      suppressedForks l S + suppressedForks r S +
        match prune l S, prune r S with
        | some _, some _ => 0
        | _, _ => 1

/--
@isnad1 id=eq.0h3v.s5.7781b3fc69ae from=translated src=- shape=b35b837a vocab=34736481
-/
@[simp] theorem prune_leaf [DecidableEq α] (S : Finset α) (a : α) :
    prune (leaf a) S = if a ∈ S then some (leaf a) else none := rfl

/--
@isnad1 id=eq.0h1v.s4.96af6bd0d0b8 from=translated src=- shape=f168b03c vocab=304101ea
-/
@[simp] theorem optionProfile_none : optionProfile (none : Option (FullTree α)) = {[]} := rfl

/--
@isnad1 id=eq.0h2v.s4.fab930c44d3e from=translated src=- shape=bb5dae9b vocab=150d3c41
-/
@[simp] theorem optionProfile_some (t : FullTree α) :
    optionProfile (some t) = t.frontierProfile := rfl

/--
Restriction of boundary words commutes with pruning.  The exact factor records
the rotation choices at vertices which disappear during suppression.
@isnad1 id=eq.0h3v.s6.1dff3284115a from=translated src=- shape=2039ba70 vocab=404bdcd9
-/
theorem map_restrictList_frontierProfile [DecidableEq α]
    (t : FullTree α) (S : Finset α) :
    t.frontierProfile.map (restrictList S) =
      (2 ^ suppressedForks t S) • optionProfile (prune t S) := by
  induction t with
  | leaf a =>
      by_cases ha : a ∈ S <;> simp [frontierProfile, restrictList, prune, suppressedForks, ha,
        optionProfile]
  | fork l r ihl ihr =>
      rw [frontierProfile_fork, map_restrictList_joinProfile, ihl, ihr,
        joinProfile_nsmul]
      simp only [suppressedForks, prune]
      generalize hl : prune l S = ol
      generalize hr : prune r S = or
      cases ol <;> cases or <;>
        simp [optionProfile, pow_add, mul_nsmul, Nat.mul_comm]

/--
@isnad1 id=eq.1h3v.s5.047c2f3300ed from=translated src=- shape=e803609e vocab=8cde83f4
-/
theorem restrictList_eq_nil_of_prune_eq_none [DecidableEq α]
    (t : FullTree α) (S : Finset α) (h : prune t S = none) :
    restrictList S t.leaves = [] := by
  induction t with
  | leaf a =>
      simp only [prune_leaf] at h
      by_cases ha : a ∈ S <;> simp_all [restrictList]
  | fork l r ihl ihr =>
      simp only [prune] at h
      generalize hl : prune l S = ol at h
      generalize hr : prune r S = or at h
      cases ol <;> cases or <;> simp_all [restrictList_append]

/--
@isnad1 id=eq.1h4v.s5.6c810fea2773 from=translated src=- shape=0b40f143 vocab=17877167
-/
theorem prune_leaves [DecidableEq α] (t u : FullTree α)
    (S : Finset α) (h : prune t S = some u) :
    u.leaves = restrictList S t.leaves := by
  induction t generalizing u with
  | leaf a =>
      simp only [prune_leaf] at h
      by_cases ha : a ∈ S
      · simp only [ha, ite_true, Option.some.injEq] at h
        subst u
        simp [restrictList, ha]
      · simp [ha] at h
  | fork l r ihl ihr =>
      simp only [prune] at h
      generalize hl : prune l S = ol at h
      generalize hr : prune r S = or at h
      cases ol with
      | none =>
          cases or with
          | none => simp at h
          | some r' =>
              simp only [Option.some.injEq] at h
              subst u
              rw [leaves_fork, restrictList_append,
                restrictList_eq_nil_of_prune_eq_none l S hl,
                List.nil_append]
              exact ihr r' hr
      | some l' =>
          cases or with
          | none =>
              simp only [Option.some.injEq] at h
              subst u
              rw [leaves_fork, restrictList_append,
                restrictList_eq_nil_of_prune_eq_none r S hr,
                List.append_nil]
              exact ihl l' hl
          | some r' =>
              simp only [Option.some.injEq] at h
              subst u
              simp only [leaves_fork, restrictList_append]
              rw [ihl l' hl, ihr r' hr]

/-! ### Small full-tree classification -/

theorem eq_leaf_of_leaves_length_eq_one (t : FullTree α)
    (h : t.leaves.length = 1) : ∃ a, t = leaf a := by
  cases t with
  | leaf a => exact ⟨a, rfl⟩
  | fork l r =>
      simp only [leaves_fork, List.length_append] at h
      have hl := leaves_length_pos l
      have hr := leaves_length_pos r
      omega

/--
@isnad1 id=ex.1h2v.s5.5521666ded4d from=translated src=- shape=a60ca99e vocab=7f536318
-/
theorem shape_of_leaves_length_eq_two (t : FullTree α)
    (h : t.leaves.length = 2) : ∃ a b, t = fork (leaf a) (leaf b) := by
  cases t with
  | leaf a => simp at h
  | fork l r =>
      simp only [leaves_fork, List.length_append] at h
      have hlp := leaves_length_pos l
      have hrp := leaves_length_pos r
      have hl : l.leaves.length = 1 := by omega
      have hr : r.leaves.length = 1 := by omega
      obtain ⟨a, rfl⟩ := eq_leaf_of_leaves_length_eq_one l hl
      obtain ⟨b, rfl⟩ := eq_leaf_of_leaves_length_eq_one r hr
      exact ⟨a, b, rfl⟩

/--
@isnad1 id=ex.1h2v.s6.c34823d0b8a8 from=translated src=- shape=412a2b61 vocab=7f536318
-/
theorem shape_of_leaves_length_eq_three (t : FullTree α)
    (h : t.leaves.length = 3) :
    ∃ a b c,
      t = fork (leaf a) (fork (leaf b) (leaf c)) ∨
      t = fork (fork (leaf a) (leaf b)) (leaf c) := by
  cases t with
  | leaf a => simp at h
  | fork l r =>
      simp only [leaves_fork, List.length_append] at h
      have hlp := leaves_length_pos l
      have hrp := leaves_length_pos r
      rcases (show l.leaves.length = 1 ∧ r.leaves.length = 2 ∨
          l.leaves.length = 2 ∧ r.leaves.length = 1 by omega) with h12 | h21
      · obtain ⟨a, rfl⟩ := eq_leaf_of_leaves_length_eq_one l h12.1
        obtain ⟨b, c, rfl⟩ := shape_of_leaves_length_eq_two r h12.2
        exact ⟨a, b, c, Or.inl rfl⟩
      · obtain ⟨a, b, rfl⟩ := shape_of_leaves_length_eq_two l h21.1
        obtain ⟨c, rfl⟩ := eq_leaf_of_leaves_length_eq_one r h21.2
        exact ⟨a, b, c, Or.inr rfl⟩

/--
@isnad1 id=ex.1h2v.s7.71824dcedb49 from=translated src=- shape=0120d1e2 vocab=7f536318
-/
theorem shape_of_leaves_length_eq_four (t : FullTree α)
    (h : t.leaves.length = 4) :
    ∃ a b c d,
      t = fork (leaf a) (fork (leaf b) (fork (leaf c) (leaf d))) ∨
      t = fork (leaf a) (fork (fork (leaf b) (leaf c)) (leaf d)) ∨
      t = fork (fork (leaf a) (leaf b)) (fork (leaf c) (leaf d)) ∨
      t = fork (fork (leaf a) (fork (leaf b) (leaf c))) (leaf d) ∨
      t = fork (fork (fork (leaf a) (leaf b)) (leaf c)) (leaf d) := by
  cases t with
  | leaf a => simp at h
  | fork l r =>
      simp only [leaves_fork, List.length_append] at h
      have hlp := leaves_length_pos l
      have hrp := leaves_length_pos r
      rcases (show l.leaves.length = 1 ∧ r.leaves.length = 3 ∨
          l.leaves.length = 2 ∧ r.leaves.length = 2 ∨
          l.leaves.length = 3 ∧ r.leaves.length = 1 by omega) with h13 | h22 | h31
      · obtain ⟨a, rfl⟩ := eq_leaf_of_leaves_length_eq_one l h13.1
        obtain ⟨b, c, d, hshape⟩ := shape_of_leaves_length_eq_three r h13.2
        rcases hshape with rfl | rfl
        · exact ⟨a, b, c, d, Or.inl rfl⟩
        · exact ⟨a, b, c, d, Or.inr (Or.inl rfl)⟩
      · obtain ⟨a, b, rfl⟩ := shape_of_leaves_length_eq_two l h22.1
        obtain ⟨c, d, rfl⟩ := shape_of_leaves_length_eq_two r h22.2
        exact ⟨a, b, c, d, Or.inr (Or.inr (Or.inl rfl))⟩
      · obtain ⟨a, b, c, hshape⟩ := shape_of_leaves_length_eq_three l h31.1
        obtain ⟨d, rfl⟩ := eq_leaf_of_leaves_length_eq_one r h31.2
        rcases hshape with rfl | rfl
        · exact ⟨a, b, c, d, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact ⟨a, b, c, d, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

/-! ### Quartet topologies and crossing channels -/

/-- The canonical unordered split `ab | cd`.  This is definitionally the
same representation as `Circular.QuartetSplit`.-/
def blockSplit [DecidableEq α] (a b c d : α) : Circular.QuartetSplit α :=
  Circular.splitOf a c b d

/-- Cyclic shifts do not change the opposite-position split.
@isnad1 id=eq.0h5v.s4.f34bcd4d204e from=translated src=- shape=c063d92b vocab=305bfaf8
-/
@[simp] theorem splitOf_rotate [DecidableEq α] (a b c d : α) :
    Circular.splitOf a b c d = Circular.splitOf b c d a := by
  ext A
  simp [Circular.splitOf, Circular.pair]
  aesop

/-- Reversing a four-term order does not change its crossing split.
@isnad1 id=eq.0h5v.s4.1d6cd21b0a09 from=translated src=- shape=9aaabc44 vocab=305bfaf8
-/
@[simp] theorem splitOf_reverse [DecidableEq α] (a b c d : α) :
    Circular.splitOf a b c d = Circular.splitOf d c b a := by
  ext A
  simp [Circular.splitOf, Circular.pair]
  aesop

/-- Reflection fixing the first displayed point.
@isnad1 id=eq.0h5v.s4.d56c0661ff0d from=translated src=- shape=cbfcd295 vocab=305bfaf8
-/
@[simp] theorem splitOf_reflect [DecidableEq α] (a b c d : α) :
    Circular.splitOf a b c d = Circular.splitOf a d c b := by
  ext A
  simp [Circular.splitOf, Circular.pair]
  aesop

/-- A half-turn of the four positions.
@isnad1 id=eq.0h5v.s4.8c4581968ce9 from=translated src=- shape=6560309d vocab=305bfaf8
-/
@[simp] theorem splitOf_rotate_two [DecidableEq α] (a b c d : α) :
    Circular.splitOf a b c d = Circular.splitOf c d a b := by
  calc
    Circular.splitOf a b c d = Circular.splitOf b c d a := splitOf_rotate _ _ _ _
    _ = Circular.splitOf c d a b := splitOf_rotate _ _ _ _

/-- The three possible `2+2` splits of a four-term list.-/
def allQuartetSplits [DecidableEq α] : List α → Finset (Circular.QuartetSplit α)
  | [a, b, c, d] =>
      {blockSplit a b c d, blockSplit a c b d, blockSplit a d b c}
  | _ => ∅

/-- Opposite positions in a four-term boundary list give its crossing split.-/
def crossingList [DecidableEq α] : List α → Circular.QuartetSplit α
  | [a, b, c, d] => Circular.splitOf a b c d
  | _ => ∅

/-- The multiset of crossing splits, retaining one copy per rotation system.-/
def crossingProfile [DecidableEq α] (t : FullTree α) :
    Multiset (Circular.QuartetSplit α) :=
  t.frontierProfile.map crossingList

/-- Find the first cherry.  On a four-leaf full tree, it is one side of the
displayed unrooted quartet split.-/
def cherry? [DecidableEq α] : FullTree α → Option (Finset α)
  | leaf _ => none
  | fork (leaf a) (leaf b) => some {a, b}
  | fork l r => (cherry? l).orElse fun _ => cherry? r

/-- The quartet split displayed by a four-leaf full tree.-/
def displayedSplit [DecidableEq α] (t : FullTree α) : Circular.QuartetSplit α :=
  match cherry? t with
  | none => ∅
  | some A => {A, t.leaves.toFinset \ A}

/--
@isnad1 id=eq.0h2v.s7.09c6273ee86c from=translated src=- shape=df174813 vocab=dc070a32
-/
@[simp] theorem crossingList_of_embedding [DecidableEq α] (q : Fin 4 ↪ α) :
    crossingList [q 0, q 1, q 2, q 3] = Circular.crossing q := by
  simp [crossingList, Circular.crossing, Circular.canonicalCrossing,
    Circular.mapSplit, Circular.splitOf, Circular.pair]

private theorem multiset_move_across_four (x y : β) :
    y ::ₘ y ::ₘ y ::ₘ y ::ₘ {x} = x ::ₘ y ::ₘ y ::ₘ y ::ₘ {y} := by
  change y ::ₘ y ::ₘ y ::ₘ y ::ₘ x ::ₘ 0 =
    x ::ₘ y ::ₘ y ::ₘ y ::ₘ y ::ₘ 0
  rw [Multiset.cons_swap y x, Multiset.cons_swap y x,
    Multiset.cons_swap y x, Multiset.cons_swap y x]

/--
@isnad1 id=eq.0h5v.s6.933615b0f73f from=translated src=- shape=6869c269 vocab=0bee399f
-/
theorem crossingProfile_shape_one_three [DecidableEq α] (a b c d : α) :
    crossingProfile (fork (leaf a) (fork (leaf b) (fork (leaf c) (leaf d)))) =
      4 • ({blockSplit a c b d, blockSplit a d b c} :
        Multiset (Circular.QuartetSplit α)) := by
  simp [crossingProfile, frontierProfile, crossingList, blockSplit,
    show (4 : ℕ) = 3 + 1 by omega, succ_nsmul]
  simp only [Multiset.cons_swap]
  exact congrArg
    (fun s => Circular.splitOf a b c d ::ₘ Circular.splitOf a b c d ::ₘ s)
    (multiset_move_across_four (Circular.splitOf a b c d)
      (Circular.splitOf a b d c))

/--
@isnad1 id=eq.0h5v.s6.9a21d36665e5 from=translated src=- shape=9c0b8cc1 vocab=0bee399f
-/
theorem crossingProfile_shape_one_twone [DecidableEq α] (a b c d : α) :
    crossingProfile (fork (leaf a) (fork (fork (leaf b) (leaf c)) (leaf d))) =
      4 • ({blockSplit a b c d, blockSplit a c b d} :
        Multiset (Circular.QuartetSplit α)) := by
  simp [crossingProfile, frontierProfile, crossingList, blockSplit,
    show (4 : ℕ) = 3 + 1 by omega, succ_nsmul]
  simp only [Multiset.cons_swap]

/--
@isnad1 id=eq.0h5v.s6.cefdeaa6985f from=translated src=- shape=312f7e5f vocab=0bee399f
-/
theorem crossingProfile_shape_two_two [DecidableEq α] (a b c d : α) :
    crossingProfile (fork (fork (leaf a) (leaf b)) (fork (leaf c) (leaf d))) =
      4 • ({blockSplit a c b d, blockSplit a d b c} :
        Multiset (Circular.QuartetSplit α)) := by
  simp [crossingProfile, frontierProfile, crossingList, blockSplit,
    show (4 : ℕ) = 3 + 1 by omega, succ_nsmul]
  simp only [Multiset.cons_swap]
  exact congrArg
    (fun s => Circular.splitOf a b c d ::ₘ Circular.splitOf a b c d ::ₘ
      Circular.splitOf a b c d ::ₘ s)
    (multiset_move_across_four (Circular.splitOf a b c d)
      (Circular.splitOf a b d c))

/--
@isnad1 id=eq.0h5v.s6.881b3fa7ab61 from=translated src=- shape=6f90bf09 vocab=0bee399f
-/
theorem crossingProfile_shape_threetwo_one [DecidableEq α] (a b c d : α) :
    crossingProfile (fork (fork (leaf a) (fork (leaf b) (leaf c))) (leaf d)) =
      4 • ({blockSplit a b c d, blockSplit a c b d} :
        Multiset (Circular.QuartetSplit α)) := by
  simp [crossingProfile, frontierProfile, crossingList, blockSplit,
    show (4 : ℕ) = 3 + 1 by omega, succ_nsmul]
  simp only [Multiset.cons_swap]

/--
@isnad1 id=eq.0h5v.s6.342227ae888d from=translated src=- shape=1c87ae91 vocab=0bee399f
-/
theorem crossingProfile_shape_three_one [DecidableEq α] (a b c d : α) :
    crossingProfile (fork (fork (fork (leaf a) (leaf b)) (leaf c)) (leaf d)) =
      4 • ({blockSplit a c b d, blockSplit a d b c} :
        Multiset (Circular.QuartetSplit α)) := by
  simp [crossingProfile, frontierProfile, crossingList, blockSplit,
    show (4 : ℕ) = 3 + 1 by omega, succ_nsmul]
  simp only [Multiset.cons_swap]
  exact congrArg
    (fun s => Circular.splitOf a b c d ::ₘ Circular.splitOf a b c d ::ₘ
      Circular.splitOf a b c d ::ₘ s)
    (multiset_move_across_four (Circular.splitOf a b c d)
      (Circular.splitOf a b d c))

/--
@isnad1 id=eq.1h5v.s5.e45c92bc9e97 from=translated src=- shape=09d26e3f vocab=90832aed
-/
theorem displayedSplit_shape_one_three [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    displayedSplit (fork (leaf a) (fork (leaf b) (fork (leaf c) (leaf d)))) =
      blockSplit a b c d := by
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  have htt := (List.nodup_cons.mp ht).2
  have hc := (List.nodup_cons.mp htt).1
  simp at ha hb hc
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  have hcd : c ≠ d := hc
  have hdiff : ({a, b, c, d} : Finset α) \ {c, d} = {a, b} := by
    ext x
    simp
    aesop
  simp [displayedSplit, cherry?, leaves, blockSplit, Circular.splitOf, Circular.pair]
  rw [hdiff]
  exact Finset.pair_comm ({c, d} : Finset α) ({a, b} : Finset α)

/--
@isnad1 id=eq.1h5v.s5.30d8c3cf7524 from=translated src=- shape=c07c4475 vocab=90832aed
-/
theorem displayedSplit_shape_one_twone [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    displayedSplit (fork (leaf a) (fork (fork (leaf b) (leaf c)) (leaf d))) =
      blockSplit a d b c := by
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  have htt := (List.nodup_cons.mp ht).2
  have hc := (List.nodup_cons.mp htt).1
  simp at ha hb hc
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  have hcd : c ≠ d := hc
  have hdiff : ({a, b, c, d} : Finset α) \ {b, c} = {a, d} := by
    ext x
    simp
    aesop
  simp [displayedSplit, cherry?, leaves, blockSplit, Circular.splitOf, Circular.pair]
  rw [hdiff]
  exact Finset.pair_comm ({b, c} : Finset α) ({a, d} : Finset α)

/--
@isnad1 id=eq.1h5v.s5.301b953d991d from=translated src=- shape=d5d5adc2 vocab=90832aed
-/
theorem displayedSplit_shape_two_two [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    displayedSplit (fork (fork (leaf a) (leaf b)) (fork (leaf c) (leaf d))) =
      blockSplit a b c d := by
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  have htt := (List.nodup_cons.mp ht).2
  have hc := (List.nodup_cons.mp htt).1
  simp at ha hb hc
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  have hcd : c ≠ d := hc
  have hdiff : ({a, b, c, d} : Finset α) \ {a, b} = {c, d} := by
    ext x
    simp
    aesop
  simp [displayedSplit, cherry?, leaves, blockSplit, Circular.splitOf, Circular.pair]
  have hdiff' : ({b, c, d} : Finset α) \ {a, b} = {c, d} := by
    ext x
    simp
    aesop
  rw [hdiff']

/--
@isnad1 id=eq.1h5v.s5.bd14cac896af from=translated src=- shape=683d1770 vocab=90832aed
-/
theorem displayedSplit_shape_threetwo_one [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    displayedSplit (fork (fork (leaf a) (fork (leaf b) (leaf c))) (leaf d)) =
      blockSplit a d b c := by
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  have htt := (List.nodup_cons.mp ht).2
  have hc := (List.nodup_cons.mp htt).1
  simp at ha hb hc
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  have hcd : c ≠ d := hc
  have hdiff : ({a, b, c, d} : Finset α) \ {b, c} = {a, d} := by
    ext x
    simp
    aesop
  simp [displayedSplit, cherry?, leaves, blockSplit, Circular.splitOf, Circular.pair]
  rw [hdiff]
  exact Finset.pair_comm ({b, c} : Finset α) ({a, d} : Finset α)

/--
@isnad1 id=eq.1h5v.s5.99bd18dc1030 from=translated src=- shape=e3e098bf vocab=90832aed
-/
theorem displayedSplit_shape_three_one [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    displayedSplit (fork (fork (fork (leaf a) (leaf b)) (leaf c)) (leaf d)) =
      blockSplit a b c d := by
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  have htt := (List.nodup_cons.mp ht).2
  have hc := (List.nodup_cons.mp htt).1
  simp at ha hb hc
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  have hcd : c ≠ d := hc
  have hdiff : ({a, b, c, d} : Finset α) \ {a, b} = {c, d} := by
    ext x
    simp
    aesop
  simp [displayedSplit, cherry?, leaves, blockSplit, Circular.splitOf, Circular.pair]
  have hdiff' : ({b, c, d} : Finset α) \ {a, b} = {c, d} := by
    ext x
    simp
    aesop
  rw [hdiff']

/--
@isnad1 id=ne.1h5v.s5.b8913bbd2ccd from=translated src=- shape=f080dfa6 vocab=2d38ec27
-/
theorem blockSplit_ab_ne_ac [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    blockSplit a b c d ≠ blockSplit a c b d := by
  intro hs
  have hm : Circular.pair a b ∈ blockSplit a b c d := by
    simp [blockSplit, Circular.splitOf]
  rw [hs] at hm
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  simp at ha hb
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  simp [blockSplit, Circular.splitOf, Circular.pair] at hm
  rcases hm with hm | hm
  · have : b ∈ ({a, c} : Finset α) := by rw [← hm]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with hba | hbc'
    · exact hab hba.symm
    · exact hbc hbc'
  · have : a ∈ ({b, d} : Finset α) := by rw [← hm]; simp
    simp [hab, had] at this

/--
@isnad1 id=ne.1h5v.s5.a8604cd94651 from=translated src=- shape=f631bbd8 vocab=2d38ec27
-/
theorem blockSplit_ab_ne_ad [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    blockSplit a b c d ≠ blockSplit a d b c := by
  intro hs
  have hm : Circular.pair a b ∈ blockSplit a b c d := by
    simp [blockSplit, Circular.splitOf]
  rw [hs] at hm
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  have htt := (List.nodup_cons.mp ht).2
  have hc := (List.nodup_cons.mp htt).1
  simp at ha hb hc
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  have hcd : c ≠ d := hc
  simp [blockSplit, Circular.splitOf, Circular.pair] at hm
  rcases hm with hm | hm
  · have : b ∈ ({a, d} : Finset α) := by rw [← hm]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with hba | hbd'
    · exact hab hba.symm
    · exact hbd hbd'
  · have : a ∈ ({b, c} : Finset α) := by rw [← hm]; simp
    simp [hab, hac] at this

/--
@isnad1 id=ne.1h5v.s5.57085b8c4963 from=translated src=- shape=63219f1b vocab=2d38ec27
-/
theorem blockSplit_ac_ne_ad [DecidableEq α] (a b c d : α)
    (h : [a, b, c, d].Nodup) :
    blockSplit a c b d ≠ blockSplit a d b c := by
  intro hs
  have hm : Circular.pair a c ∈ blockSplit a c b d := by
    simp [blockSplit, Circular.splitOf]
  rw [hs] at hm
  have ha := (List.nodup_cons.mp h).1
  have ht := (List.nodup_cons.mp h).2
  have hb := (List.nodup_cons.mp ht).1
  have htt := (List.nodup_cons.mp ht).2
  have hc := (List.nodup_cons.mp htt).1
  simp at ha hb hc
  rcases ha with ⟨hab, hac, had⟩
  rcases hb with ⟨hbc, hbd⟩
  have hcd : c ≠ d := hc
  simp [blockSplit, Circular.splitOf, Circular.pair] at hm
  rcases hm with hm | hm
  · have : c ∈ ({a, d} : Finset α) := by rw [← hm]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with hca | hcd'
    · exact hac hca.symm
    · exact hcd hcd'
  · have : a ∈ ({b, c} : Finset α) := by rw [← hm]; simp
    simp [hab, hac] at this

/-- The displayed split is absent from the crossing profile.
@isnad1 id=eq.2h2v.s6.bf6165e2a1e2 from=translated src=- shape=9e991454 vocab=f899d588
-/
theorem wrongChannel_true_count [DecidableEq α] (t : FullTree α)
    (hlen : t.leaves.length = 4) (hnodup : t.leaves.Nodup) :
    Multiset.count (displayedSplit t) (crossingProfile t) = 0 := by
  obtain ⟨a, b, c, d, hs⟩ := shape_of_leaves_length_eq_four t hlen
  rcases hs with hs | hs | hs | hs | hs
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    rw [displayedSplit_shape_one_three a b c d hn,
      crossingProfile_shape_one_three]
    simp [blockSplit_ab_ne_ac a b c d hn,
      blockSplit_ab_ne_ad a b c d hn]
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    rw [displayedSplit_shape_one_twone a b c d hn,
      crossingProfile_shape_one_twone]
    have h1 := (blockSplit_ab_ne_ad a b c d hn).symm
    have h2 := (blockSplit_ac_ne_ad a b c d hn).symm
    simp [h1, h2]
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    rw [displayedSplit_shape_two_two a b c d hn,
      crossingProfile_shape_two_two]
    simp [blockSplit_ab_ne_ac a b c d hn,
      blockSplit_ab_ne_ad a b c d hn]
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    rw [displayedSplit_shape_threetwo_one a b c d hn,
      crossingProfile_shape_threetwo_one]
    have h1 := (blockSplit_ab_ne_ad a b c d hn).symm
    have h2 := (blockSplit_ac_ne_ad a b c d hn).symm
    simp [h1, h2]
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    rw [displayedSplit_shape_three_one a b c d hn,
      crossingProfile_shape_three_one]
    simp [blockSplit_ab_ne_ac a b c d hn,
      blockSplit_ab_ne_ad a b c d hn]

/-- Every other valid quartet split occurs in exactly half of the rotation
systems.  The doubled count formulation avoids division and probabilities.
@isnad1 id=eq.4h3v.s6.a5d3a6b1da4f from=translated src=- shape=fd364521 vocab=7bdcd961
-/
theorem wrongChannel_other_count [DecidableEq α] (t : FullTree α)
    (hlen : t.leaves.length = 4) (hnodup : t.leaves.Nodup)
    (s : Circular.QuartetSplit α) (hvalid : s ∈ allQuartetSplits t.leaves)
    (hne : s ≠ displayedSplit t) :
    2 * Multiset.count s (crossingProfile t) = t.frontierProfile.card := by
  obtain ⟨a, b, c, d, hs⟩ := shape_of_leaves_length_eq_four t hlen
  rcases hs with hs | hs | hs | hs | hs
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    simp [leaves, allQuartetSplits] at hvalid
    rw [displayedSplit_shape_one_three a b c d hn] at hne
    rw [crossingProfile_shape_one_three]
    rcases hvalid with rfl | rfl | rfl
    · exact (hne rfl).elim
    · simp [Multiset.count_nsmul, blockSplit_ac_ne_ad a b c d hn,
        frontierProfile]
    · simp [Multiset.count_nsmul, blockSplit_ac_ne_ad a b c d hn,
        frontierProfile]
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    simp [leaves, allQuartetSplits] at hvalid
    rw [displayedSplit_shape_one_twone a b c d hn] at hne
    rw [crossingProfile_shape_one_twone]
    rcases hvalid with rfl | rfl | rfl
    · simp [Multiset.count_nsmul, blockSplit_ab_ne_ac a b c d hn,
        frontierProfile]
    · simp [Multiset.count_nsmul, blockSplit_ab_ne_ac a b c d hn,
        frontierProfile]
    · exact (hne rfl).elim
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    simp [leaves, allQuartetSplits] at hvalid
    rw [displayedSplit_shape_two_two a b c d hn] at hne
    rw [crossingProfile_shape_two_two]
    rcases hvalid with rfl | rfl | rfl
    · exact (hne rfl).elim
    · simp [Multiset.count_nsmul, blockSplit_ac_ne_ad a b c d hn,
        frontierProfile]
    · simp [Multiset.count_nsmul, blockSplit_ac_ne_ad a b c d hn,
        frontierProfile]
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    simp [leaves, allQuartetSplits] at hvalid
    rw [displayedSplit_shape_threetwo_one a b c d hn] at hne
    rw [crossingProfile_shape_threetwo_one]
    rcases hvalid with rfl | rfl | rfl
    · simp [Multiset.count_nsmul, blockSplit_ab_ne_ac a b c d hn,
        frontierProfile]
    · simp [Multiset.count_nsmul, blockSplit_ab_ne_ac a b c d hn,
        frontierProfile]
    · exact (hne rfl).elim
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [leaves] using hnodup
    simp [leaves, allQuartetSplits] at hvalid
    rw [displayedSplit_shape_three_one a b c d hn] at hne
    rw [crossingProfile_shape_three_one]
    rcases hvalid with rfl | rfl | rfl
    · exact (hne rfl).elim
    · simp [Multiset.count_nsmul, blockSplit_ac_ne_ad a b c d hn,
        frontierProfile]
    · simp [Multiset.count_nsmul, blockSplit_ac_ne_ad a b c d hn,
        frontierProfile]
/-- Relabel every leaf.-/
def map (f : α → β) : FullTree α → FullTree β
  | .leaf a => .leaf (f a)
  | .fork l r => .fork (map f l) (map f r)

/--
@isnad1 id=eq.0h4v.s4.7a2c11318e12 from=translated src=- shape=82b556c0 vocab=2b5ddc8e
-/
@[simp] theorem leaves_map (f : α → β) (t : FullTree α) :
    (t.map f).leaves = t.leaves.map f := by
  induction t with
  | leaf => rfl
  | fork l r ihl ihr => simp [map, ihl, ihr]

/--
@isnad1 id=eq.0h4v.s4.8d736bea69db from=translated src=- shape=ddbef6f7 vocab=10c87c3a
-/
@[simp] theorem forks_map (f : α → β) (t : FullTree α) :
    (t.map f).forks = t.forks := by
  induction t with
  | leaf => rfl
  | fork l r ihl ihr => simp [map, ihl, ihr]

/--
@isnad1 id=eq.0h4v.s5.49435fa616ce from=translated src=- shape=6bae3a33 vocab=e07c591f
-/
theorem frontierProfile_map (f : α → β) (t : FullTree α) :
    (t.map f).frontierProfile = t.frontierProfile.map (List.map f) := by
  induction t with
  | leaf a => simp [map, frontierProfile]
  | fork l r ihl ihr =>
      simp [map, frontierProfile, joinProfile, ihl, ihr, Multiset.map_bind,
        Multiset.bind_map, List.map_append]

end FullTree

/--
An unrooted binary phylogenetic tree, rooted at (and cut open at) one leaf.
`crown` contains every other label exactly once.-/
structure PhyloTree (α : Type*) [Fintype α] [DecidableEq α] where
  root : α
  crown : FullTree {a : α // a ≠ root}
  nodup_leaves : crown.leaves.Nodup
  exhaustive : ∀ a : {a : α // a ≠ root}, a ∈ crown.leaves

namespace PhyloTree

variable [Fintype α] [DecidableEq α]

/-- Forget the subtype proof on a frontier of the cut-open tree.-/
def boundaryProfile (T : PhyloTree α) : Multiset (List α) :=
  T.crown.frontierProfile.map fun xs => T.root :: xs.map Subtype.val

/--
@isnad1 id=eq.0h2v.s5.dec48a539af3 from=translated src=- shape=2d15c00b vocab=8361a8d9
-/
@[simp] theorem card_boundaryProfile (T : PhyloTree α) :
    T.boundaryProfile.card = 2 ^ T.crown.forks := by
  simp [boundaryProfile]

/--
@isnad1 id=eq.1h3v.s5.339ed1f62203 from=translated src=- shape=6604c685 vocab=87f97695
-/
theorem mem_boundaryProfile_head (T : PhyloTree α) {xs : List α}
    (hxs : xs ∈ T.boundaryProfile) : xs.head? = some T.root := by
  simp only [boundaryProfile, Multiset.mem_map] at hxs
  obtain ⟨ys, -, rfl⟩ := hxs
  simp

/--
@isnad1 id=nodup.1h3v.s5.e1a63bdb0d53 from=translated src=- shape=59b15d0c vocab=fc8bfad2
-/
theorem mem_boundaryProfile_nodup (T : PhyloTree α) {xs : List α}
    (hxs : xs ∈ T.boundaryProfile) : xs.Nodup := by
  simp only [boundaryProfile, Multiset.mem_map] at hxs
  obtain ⟨ys, hys, rfl⟩ := hxs
  have hp := T.crown.mem_frontierProfile_perm hys
  have hyn : ys.Nodup := hp.nodup_iff.mpr T.nodup_leaves
  rw [List.nodup_cons]
  constructor
  · intro hr
    obtain ⟨y, -, hy⟩ := List.mem_map.mp hr
    exact y.property hy
  · exact hyn.map Subtype.val_injective

/-- The fixed reference order underlying the boundary profile.-/
def referenceLeaves (T : PhyloTree α) : List α :=
  T.root :: T.crown.leaves.map Subtype.val

/--
@isnad1 id=perm.1h3v.s5.74901867905f from=translated src=- shape=1ce96f73 vocab=c6b7ab5b
-/
theorem mem_boundaryProfile_perm (T : PhyloTree α) {xs : List α}
    (hxs : xs ∈ T.boundaryProfile) : xs.Perm T.referenceLeaves := by
  simp only [boundaryProfile, Multiset.mem_map] at hxs
  obtain ⟨ys, hys, rfl⟩ := hxs
  exact (T.crown.mem_frontierProfile_perm hys).map Subtype.val |>.cons T.root

/--
@isnad1 id=mem.0h3v.s4.96529b453a19 from=translated src=- shape=8c5e682c vocab=b8733d5c
-/
theorem mem_referenceLeaves (T : PhyloTree α) (a : α) :
    a ∈ T.referenceLeaves := by
  by_cases ha : a = T.root
  · subst a
    simp [referenceLeaves]
  · simp only [referenceLeaves, List.mem_cons]
    right
    exact List.mem_map.mpr ⟨⟨a, ha⟩, T.exhaustive ⟨a, ha⟩, rfl⟩

/--
@isnad1 id=mem.1h4v.s5.777864eceff1 from=translated src=- shape=5075be8c vocab=40b78731
-/
theorem mem_boundaryProfile_complete (T : PhyloTree α) {xs : List α}
    (hxs : xs ∈ T.boundaryProfile) (a : α) : a ∈ xs := by
  exact (T.mem_boundaryProfile_perm hxs).mem_iff.mpr (T.mem_referenceLeaves a)

/--
@isnad1 id=eq.2h4v.s5.3806451ca3d8 from=translated src=- shape=93009f90 vocab=770a9efd
-/
theorem restrictList_boundary_length (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) {xs : List α} (hxs : xs ∈ T.boundaryProfile) :
    (FullTree.restrictList Q xs).length = 4 := by
  have hn : (FullTree.restrictList Q xs).Nodup :=
    (T.mem_boundaryProfile_nodup hxs).filter _
  have hfin : (FullTree.restrictList Q xs).toFinset = Q := by
    ext a
    simp [FullTree.restrictList, T.mem_boundaryProfile_complete hxs a]
  calc
    (FullTree.restrictList Q xs).length =
        (FullTree.restrictList Q xs).toFinset.card :=
      (List.toFinset_card_of_nodup hn).symm
    _ = Q.card := congrArg Finset.card hfin
    _ = 4 := hQ

/-- Put the distinguished leaf back, obtaining an ordinary full tree.  Its
top fork is an artefact of cutting at the root leaf.-/
def asFullTree (T : PhyloTree α) : FullTree α :=
  .fork (.leaf T.root) (T.crown.map Subtype.val)

/--
@isnad1 id=eq.0h2v.s4.df4627aa7942 from=translated src=- shape=8358e7b5 vocab=6b265684
-/
@[simp] theorem asFullTree_leaves (T : PhyloTree α) :
    T.asFullTree.leaves = T.referenceLeaves := by
  simp [asFullTree, referenceLeaves]

/--
@isnad1 id=nodup.0h2v.s4.80487e83b462 from=translated src=- shape=fe7756e3 vocab=8d342bc6
-/
theorem asFullTree_nodup (T : PhyloTree α) : T.asFullTree.leaves.Nodup := by
  rw [asFullTree_leaves, referenceLeaves, List.nodup_cons]
  constructor
  · intro hr
    obtain ⟨y, -, hy⟩ := List.mem_map.mp hr
    exact y.property hy
  · exact T.nodup_leaves.map Subtype.val_injective

/--
@isnad1 id=mem.0h3v.s4.4a538cbd8833 from=translated src=- shape=245f3739 vocab=fd0a28c8
-/
theorem mem_asFullTree_leaves (T : PhyloTree α) (a : α) :
    a ∈ T.asFullTree.leaves := by
  rw [asFullTree_leaves]
  exact T.mem_referenceLeaves a

/--
@isnad1 id=eq.1h3v.s5.880190045821 from=translated src=- shape=1f900406 vocab=2ccd7285
-/
theorem prune_asFullTree_isSome (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) : (T.asFullTree.prune Q).isSome = true := by
  rw [← Option.ne_none_iff_isSome]
  intro hnone
  obtain ⟨a, ha⟩ : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hempty := FullTree.restrictList_eq_nil_of_prune_eq_none T.asFullTree Q hnone
  have hmem : a ∈ FullTree.restrictList Q T.asFullTree.leaves := by
    simp [FullTree.restrictList, ha, asFullTree_leaves, T.mem_referenceLeaves a]
  rw [hempty] at hmem
  exact (List.not_mem_nil hmem)

/-- The four-leaf tree induced by `Q`, with degree-two vertices suppressed.-/
def restrictedTree (T : PhyloTree α) (Q : Finset α) (hQ : Q.card = 4) :
    FullTree α :=
  (T.asFullTree.prune Q).get (T.prune_asFullTree_isSome Q hQ)

/--
@isnad1 id=eq.1h3v.s5.ab2a67b953a8 from=translated src=- shape=9e478398 vocab=ceaadad4
-/
theorem prune_asFullTree_eq_restrictedTree (T : PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    T.asFullTree.prune Q = some (T.restrictedTree Q hQ) := by
  generalize h : T.asFullTree.prune Q = o
  cases o with
  | none =>
      have hi := T.prune_asFullTree_isSome Q hQ
      rw [h] at hi
      simp at hi
  | some u => simp [restrictedTree, h]

/--
@isnad1 id=eq.1h3v.s5.fe6ca44b0173 from=translated src=- shape=e64d2cb5 vocab=5e2d7d6f
-/
theorem restrictedTree_leaves (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) :
    (T.restrictedTree Q hQ).leaves = FullTree.restrictList Q T.asFullTree.leaves :=
  FullTree.prune_leaves _ _ _ (T.prune_asFullTree_eq_restrictedTree Q hQ)

/--
@isnad1 id=nodup.1h3v.s5.725ddcec455d from=translated src=- shape=9395137f vocab=cc51a6fb
-/
theorem restrictedTree_nodup (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) : (T.restrictedTree Q hQ).leaves.Nodup := by
  rw [restrictedTree_leaves]
  exact T.asFullTree_nodup.filter _

/--
@isnad1 id=eq.1h3v.s5.fd8107ca817d from=translated src=- shape=1a929f32 vocab=c2f9ab27
-/
theorem restrictedTree_leaves_length (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) : (T.restrictedTree Q hQ).leaves.length = 4 := by
  rw [restrictedTree_leaves]
  have hn := T.asFullTree_nodup.filter (fun a => decide (a ∈ Q))
  have hfin : (FullTree.restrictList Q T.asFullTree.leaves).toFinset = Q := by
    ext a
    simp [FullTree.restrictList, asFullTree_leaves, T.mem_referenceLeaves a]
  calc
    (FullTree.restrictList Q T.asFullTree.leaves).length =
        (FullTree.restrictList Q T.asFullTree.leaves).toFinset.card :=
      (List.toFinset_card_of_nodup hn).symm
    _ = Q.card := congrArg Finset.card hfin
    _ = 4 := hQ

/-- The true quartet split displayed by `T` on `Q`.-/
def displayedSplitOn (T : PhyloTree α) (Q : Finset α) (hQ : Q.card = 4) :
    Circular.QuartetSplit α :=
  (T.restrictedTree Q hQ).displayedSplit

/-- Crossing splits obtained by restricting each global boundary word to `Q`.-/
def restrictedCrossingProfile (T : PhyloTree α) (Q : Finset α) :
    Multiset (Circular.QuartetSplit α) :=
  T.boundaryProfile.map fun xs => FullTree.crossingList (FullTree.restrictList Q xs)

omit [Fintype α] in
/--
@isnad1 id=eq.1h3v.s5.d0fbfd8b1dac from=translated src=- shape=32d04291 vocab=05f7e7aa
-/
theorem crossingList_cons_eq_append_singleton (a : α) (zs : List α)
    (hz : zs.length = 3) :
    FullTree.crossingList (a :: zs) = FullTree.crossingList (zs ++ [a]) := by
  obtain ⟨b, c, d, rfl⟩ := List.length_eq_three.mp hz
  exact FullTree.splitOf_rotate _ _ _ _

/--
@isnad1 id=eq.0h2v.s7.fac677e5056f from=translated src=- shape=31ecdc56 vocab=ad3be44c
-/
theorem asFullTree_frontierProfile (T : PhyloTree α) :
    T.asFullTree.frontierProfile =
      T.crown.frontierProfile.bind fun ys =>
        {T.root :: ys.map Subtype.val, ys.map Subtype.val ++ [T.root]} := by
  simp [asFullTree, FullTree.frontierProfile, FullTree.joinProfile,
    FullTree.frontierProfile_map]

private def restrictedBoundaryOutcome (T : PhyloTree α) (Q : Finset α)
    (ys : List {a : α // a ≠ T.root}) : Circular.QuartetSplit α :=
  FullTree.crossingList
    (FullTree.restrictList Q (T.root :: ys.map Subtype.val))

private def restrictedTopReverseOutcome (T : PhyloTree α) (Q : Finset α)
    (ys : List {a : α // a ≠ T.root}) : Circular.QuartetSplit α :=
  FullTree.crossingList
    (FullTree.restrictList Q (ys.map Subtype.val ++ [T.root]))

private theorem restricted_top_reverse_eq (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) {ys : List {a : α // a ≠ T.root}}
    (hys : ys ∈ T.crown.frontierProfile) :
    restrictedTopReverseOutcome T Q ys = restrictedBoundaryOutcome T Q ys := by
  have hbmem : T.root :: ys.map Subtype.val ∈ T.boundaryProfile := by
    apply Multiset.mem_map.mpr
    exact ⟨ys, hys, rfl⟩
  have hlen := T.restrictList_boundary_length Q hQ hbmem
  by_cases hr : T.root ∈ Q
  · let zs := FullTree.restrictList Q (ys.map Subtype.val)
    have hz : zs.length = 3 := by
      simpa [FullTree.restrictList, hr, zs] using hlen
    change FullTree.crossingList
        (FullTree.restrictList Q (ys.map Subtype.val ++ [T.root])) =
      FullTree.crossingList
        (FullTree.restrictList Q (T.root :: ys.map Subtype.val))
    simp [FullTree.restrictList, hr]
    change FullTree.crossingList (zs ++ [T.root]) =
      FullTree.crossingList (T.root :: zs)
    exact (crossingList_cons_eq_append_singleton T.root zs hz).symm
  · change FullTree.crossingList
        (FullTree.restrictList Q (ys.map Subtype.val ++ [T.root])) =
      FullTree.crossingList
        (FullTree.restrictList Q (T.root :: ys.map Subtype.val))
    simp [FullTree.restrictList, hr]

/-- The artificial top fork in `asFullTree` duplicates, but does not change,
the crossing outcome of every genuine boundary rotation.
@isnad1 id=eq.1h3v.s6.68c51f365b76 from=translated src=- shape=428d17ae vocab=458d1a2e
-/
theorem asFullTree_restrictedCrossingProfile (T : PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    T.asFullTree.frontierProfile.map
        (fun xs => FullTree.crossingList (FullTree.restrictList Q xs)) =
      2 • T.restrictedCrossingProfile Q := by
  rw [asFullTree_frontierProfile]
  simp only [Multiset.map_bind]
  change (T.crown.frontierProfile.bind fun ys =>
      {restrictedBoundaryOutcome T Q ys, restrictedTopReverseOutcome T Q ys}) = _
  have heq : (T.crown.frontierProfile.bind fun ys =>
      {restrictedBoundaryOutcome T Q ys, restrictedTopReverseOutcome T Q ys}) =
      T.crown.frontierProfile.bind fun ys =>
        {restrictedBoundaryOutcome T Q ys, restrictedBoundaryOutcome T Q ys} := by
    apply Multiset.bind_congr
    intro ys hys
    rw [restricted_top_reverse_eq T Q hQ hys]
  rw [heq]
  simp [restrictedCrossingProfile, boundaryProfile, restrictedBoundaryOutcome,
    two_nsmul, Multiset.map_map]

/--
@isnad1 id=eq.1h3v.s6.cf6039d97c98 from=translated src=- shape=9d9ea07e vocab=3d95e88b
-/
theorem asFullTree_prunedCrossingProfile (T : PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    T.asFullTree.frontierProfile.map
        (fun xs => FullTree.crossingList (FullTree.restrictList Q xs)) =
      (2 ^ FullTree.suppressedForks T.asFullTree Q) •
        FullTree.crossingProfile (T.restrictedTree Q hQ) := by
  have h := FullTree.map_restrictList_frontierProfile T.asFullTree Q
  rw [T.prune_asFullTree_eq_restrictedTree Q hQ] at h
  have hm := congrArg (Multiset.map FullTree.crossingList) h
  simpa [FullTree.crossingProfile, Multiset.map_map, Multiset.map_nsmul] using hm

/-- The valid split set on the induced quartet.-/
def validSplitsOn (T : PhyloTree α) (Q : Finset α) (hQ : Q.card = 4) :
    Finset (Circular.QuartetSplit α) :=
  FullTree.allQuartetSplits (T.restrictedTree Q hQ).leaves

/-- Global boundary-profile version of the zero-probability true channel.
@isnad1 id=eq.1h3v.s6.d332de2939e3 from=translated src=- shape=12cc6d17 vocab=c9248e61
-/
theorem wrongChannelOn_true_count (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) :
    Multiset.count (T.displayedSplitOn Q hQ) (T.restrictedCrossingProfile Q) = 0 := by
  let R := T.restrictedTree Q hQ
  let k := 2 ^ FullTree.suppressedForks T.asFullTree Q
  have hzero : Multiset.count R.displayedSplit R.crossingProfile = 0 :=
    FullTree.wrongChannel_true_count R (T.restrictedTree_leaves_length Q hQ)
      (T.restrictedTree_nodup Q hQ)
  have hprof : 2 • T.restrictedCrossingProfile Q = k • R.crossingProfile :=
    (T.asFullTree_restrictedCrossingProfile Q hQ).symm.trans
      (T.asFullTree_prunedCrossingProfile Q hQ)
  have hc := congrArg (Multiset.count R.displayedSplit) hprof
  simp only [Multiset.count_nsmul, hzero, Nat.mul_zero] at hc
  change Multiset.count R.displayedSplit (T.restrictedCrossingProfile Q) = 0
  omega

/-- Global exact half law for either non-true valid split.
@isnad1 id=eq.3h4v.s6.86df95e9085a from=translated src=- shape=5b4f5a2e vocab=eb20ef64
-/
theorem wrongChannelOn_other_count (T : PhyloTree α) (Q : Finset α)
    (hQ : Q.card = 4) (s : Circular.QuartetSplit α)
    (hvalid : s ∈ T.validSplitsOn Q hQ) (hne : s ≠ T.displayedSplitOn Q hQ) :
    2 * Multiset.count s (T.restrictedCrossingProfile Q) = T.boundaryProfile.card := by
  let R := T.restrictedTree Q hQ
  let B := T.restrictedCrossingProfile Q
  let k := 2 ^ FullTree.suppressedForks T.asFullTree Q
  have hcore : 2 * Multiset.count s R.crossingProfile = R.frontierProfile.card :=
    FullTree.wrongChannel_other_count R (T.restrictedTree_leaves_length Q hQ)
      (T.restrictedTree_nodup Q hQ) s hvalid hne
  have hprof : 2 • B = k • R.crossingProfile :=
    (T.asFullTree_restrictedCrossingProfile Q hQ).symm.trans
      (T.asFullTree_prunedCrossingProfile Q hQ)
  have hcount := congrArg (Multiset.count s) hprof
  simp only [Multiset.count_nsmul] at hcount
  have hcard := congrArg Multiset.card hprof
  simp only [Multiset.card_nsmul] at hcard
  have hRcard : R.crossingProfile.card = R.frontierProfile.card := by
    simp [R, FullTree.crossingProfile]
  rw [hRcard] at hcard
  have hBcard : B.card = T.boundaryProfile.card := by
    simp [B, restrictedCrossingProfile]
  have htwice : 2 * B.card = 2 * (2 * Multiset.count s B) := by
    calc
      2 * B.card = k * R.frontierProfile.card := hcard
      _ = k * (2 * Multiset.count s R.crossingProfile) := by rw [hcore]
      _ = 2 * (k * Multiset.count s R.crossingProfile) := by
        simp [Nat.mul_left_comm]
      _ = 2 * (2 * Multiset.count s B) := by rw [hcount]
  change 2 * Multiset.count s B = T.boundaryProfile.card
  rw [← hBcard]
  omega

end PhyloTree

end Tree

end QuartetDistance
