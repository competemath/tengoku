import Tengoku.TutteHomotopyLean.TutteFormalization.Homotopy.Cut
import Tengoku.Seed.Data.Fin.Rev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace TutteFormalization
variable {α : Type*} {M : Matroid α}

theorem TutteAdjacent.symm {H K : Set α} (h : TutteAdjacent M H K) : TutteAdjacent M K H := by
  simpa only [TutteAdjacent, Set.inter_comm] using And.intro h.1.symm h.2

namespace TuttePath
/-- A faithful finite vertex word, retaining both endpoint occurrences in a loop.-/
def word (p : TuttePath M) : List (Set α) := List.ofFn p.vertex

def reverse (p : TuttePath M) : TuttePath M where
  length := p.length
  vertex i := p.vertex i.rev
  isHyperplane i := p.isHyperplane i.rev
  adjacent i := by
    simpa only [Fin.rev_castSucc, Fin.rev_succ] using (p.adjacent i.rev).symm

@[simp] theorem reverse_origin (p : TuttePath M) : p.reverse.origin = p.terminus := by
  apply congrArg p.vertex
  apply Fin.ext
  simp [reverse, origin, terminus, Fin.rev, Fin.last]
@[simp] theorem reverse_terminus (p : TuttePath M) : p.reverse.terminus = p.origin := by
  simp [reverse, origin, terminus, Fin.rev_zero, Fin.rev_last]
theorem reverse_off {p : TuttePath M} {Γ : Set (Set α)} (h : p.Off Γ) : p.reverse.Off Γ :=
  fun i => h i.rev

/-- Concatenation retains exactly one copy of the common vertex.-/
def concat (p q : TuttePath M) (h : p.terminus = q.origin) : TuttePath M where
  length := p.length + q.length
  vertex i := if hi : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩
    else q.vertex ⟨i.val - p.length, by omega⟩
  isHyperplane i := by
    split
    · exact p.isHyperplane _
    · exact q.isHyperplane _
  adjacent i := by
    by_cases hi : i.val < p.length
    · simpa [show i.val ≤ p.length by omega, show i.val + 1 ≤ p.length by omega]
        using p.adjacent ⟨i.val, hi⟩
    · have hj : i.val - p.length < q.length := by omega
      have hr : ¬ i.val + 1 ≤ p.length := by omega
      simp only [Fin.val_castSucc, Fin.val_succ, hr, ↓reduceDIte]
      split
      · rename_i hle
        have heq : i.val = p.length := by omega
        have hx : p.vertex ⟨i.val, by omega⟩ = q.vertex ⟨i.val - p.length, by omega⟩ := by
          simpa [heq, origin, terminus, Fin.last] using h
        rw [hx]
        convert q.adjacent ⟨i.val - p.length, hj⟩ using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
      · convert q.adjacent ⟨i.val - p.length, hj⟩ using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega

@[simp] theorem concat_origin (p q : TuttePath M) (h : p.terminus = q.origin) :
    (p.concat q h).origin = p.origin := by simp [concat, origin]
@[simp] theorem concat_terminus (p q : TuttePath M) (h : p.terminus = q.origin) :
    (p.concat q h).terminus = q.terminus := by
  by_cases hq : q.length = 0
  · have heq : q.origin = q.terminus := congrArg q.vertex (Fin.ext (by simp [hq]))
    simpa [concat, terminus, hq, Fin.last] using h.trans heq
  · simp [concat, terminus, Fin.last, show ¬ p.length + q.length ≤ p.length by omega]

theorem concat_off {p q : TuttePath M} {Γ : Set (Set α)} (hp : p.Off Γ) (hq : q.Off Γ)
    (h : p.terminus = q.origin) : (p.concat q h).Off Γ := by
  intro i
  simp only [concat]
  split
  · exact hp _
  · exact hq _
/-- Path equality includes length and every vertex; proof fields are irrelevant.-/
theorem ext_vertices {p q : TuttePath M} (h : p.length = q.length)
    (hv : ∀ i, p.vertex i = q.vertex (Fin.cast (congrArg (· + 1) h) i)) : p = q := by
  cases p with
  | mk lp vp hp ap =>
    cases q with
    | mk lq vq hq aq =>
      dsimp at h
      subst lq
      have hv' : vp = vq := funext hv
      subst vq
      rfl

@[simp] theorem reverse_reverse (p : TuttePath M) : p.reverse.reverse = p := by
  apply ext_vertices (p := p.reverse.reverse) (q := p) rfl
  intro i
  apply congrArg p.vertex
  apply Fin.ext
  simp [reverse, Fin.rev, Fin.cast]
  omega

@[simp] theorem concat_constant (p : TuttePath M) :
    p.concat (constant p.terminus (p.isHyperplane (Fin.last p.length))) rfl = p := by
  apply ext_vertices (p := p.concat _ rfl) (q := p) (Nat.add_zero _)
  intro i
  have hi : i.val ≤ p.length := by
    have := i.isLt
    change i.val < p.length + 0 + 1 at this
    omega
  simp only [Fin.cast, concat, constant, hi, ↓reduceDIte]

@[simp] theorem constant_concat (p : TuttePath M) :
    (constant p.origin (p.isHyperplane 0)).concat p rfl = p := by
  apply ext_vertices (Nat.zero_add _)
  intro i
  by_cases hi : i.val = 0
  · simp [Fin.cast, concat, constant, hi, origin]
  · simp [Fin.cast, concat, constant, show ¬ i.val ≤ 0 by omega]

@[simp] theorem concat_constant_eq (p : TuttePath M) (H : Set α)
    (hH : IsHyperplane M H) (h : p.terminus = H) :
    p.concat (constant H hH) h = p := by
  subst H
  exact concat_constant p

@[simp] theorem constant_concat_eq (p : TuttePath M) (H : Set α)
    (hH : IsHyperplane M H) (h : H = p.origin) :
    (constant H hH).concat p h = p := by
  subst H
  exact constant_concat p

theorem concat_assoc (a b c : TuttePath M) (hab : a.terminus = b.origin)
    (hbc : b.terminus = c.origin) :
    (a.concat b hab).concat c (by simpa using hbc) =
      a.concat (b.concat c hbc) (by simpa using hab) := by
  apply ext_vertices (Nat.add_assoc _ _ _)
  intro i
  by_cases ha : i.val ≤ a.length
  · simp [Fin.cast, concat, Nat.add_comm b.length a.length, ha, show i.val ≤ a.length + b.length by omega]
  · by_cases hb : i.val ≤ a.length + b.length
    · simp [Fin.cast, concat, Nat.add_comm b.length a.length, ha, hb, show i.val - a.length ≤ b.length by omega]
    · simp [Fin.cast, concat, Nat.add_comm b.length a.length, ha, hb, show ¬ i.val - a.length ≤ b.length by omega]
      congr 1
      apply Fin.ext
      simp
      omega
theorem reverse_concat (p q : TuttePath M) (h : p.terminus = q.origin) :
    (p.concat q h).reverse = q.reverse.concat p.reverse (by simpa using h.symm) := by
  apply ext_vertices (Nat.add_comm _ _)
  intro i
  have hi := i.isLt
  change i.val < p.length + q.length + 1 at hi
  simp only [reverse, concat, Fin.cast, Fin.rev, Fin.val_mk]
  split_ifs with h1 h2 h2
  · have heq : i.val = q.length := by omega
    simpa [heq, terminus, origin, Fin.last] using h
  · apply congrArg p.vertex
    apply Fin.ext
    simp
    omega
  · apply congrArg q.vertex
    apply Fin.ext
    simp
    omega
  · omega

@[simp] theorem reverse_constant (H : Set α) (hH : IsHyperplane M H) :
    (constant H hH).reverse = constant H hH := by
  apply ext_vertices (p := (constant H hH).reverse) (q := constant H hH) rfl
  intro i
  rfl
end TuttePath
end TutteFormalization
