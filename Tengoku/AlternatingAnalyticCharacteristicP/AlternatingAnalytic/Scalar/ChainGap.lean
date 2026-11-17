import Tengoku.Seed.Data.List.Infix
import Tengoku.Seed.Data.Set.Finite.Basic
import Tengoku.Seed.Data.Fintype.Defs
import Tengoku
import Tengoku.Seed.Order.Monotone.Basic
import Tengoku.Seed.Data.Finset.Insert

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chain gap in the word tree (Lemma F.3)

Let `L` be a set of labels and `List L` the word tree `L^{<ω}`, ordered by the prefix relation.
A `j`-chain is the range of a sequence `s₀, s₁, …` with `s_r ++ [j] <+: s_{r+1}`. Chains with
different labels share at most one word. If the label set is finite and, for each label `j`, a set
`a j` contains all but finitely many words of every `j`-chain, then the sets `a j` have a common
word.
-/

namespace AlternatingAnalytic.ChainGap

universe u

variable {L : Type u}

/-- A `j`-chain in the word tree `List L`: the set of words of a sequence `s₀, s₁, …` with
`s_r j ⪯ s_{r+1}` (prefix order) for every `r`.-/
def IsLabelChain (j : L) (T : Set (List L)) : Prop :=
  ∃ s : ℕ → List L, (∀ r, s r ++ [j] <+: s (r + 1)) ∧ T = Set.range s

/-- Along a `j`-chain sequence, later words extend earlier ones past the label `j`.-/
theorem append_prefix_of_lt {j : L} {s : ℕ → List L} (hs : ∀ r, s r ++ [j] <+: s (r + 1))
    {r m : ℕ} (hrm : r < m) : s r ++ [j] <+: s m := by
  induction hrm with
  | refl => exact hs r
  | step _ ih => exact ih.trans ((List.prefix_append _ _).trans (hs _))

/-- Two distinct words of a `j`-chain are comparable, the shorter one extended by `j`.-/
theorem append_prefix_of_mem_range {j : L} {s : ℕ → List L}
    (hs : ∀ r, s r ++ [j] <+: s (r + 1)) {w₁ w₂ : List L} (h₁ : w₁ ∈ Set.range s)
    (h₂ : w₂ ∈ Set.range s) (hne : w₁ ≠ w₂) : w₁ ++ [j] <+: w₂ ∨ w₂ ++ [j] <+: w₁ := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact Or.inl (append_prefix_of_lt hs hab)
  · exact absurd rfl hne
  · exact Or.inr (append_prefix_of_lt hs hab)

/-- A word cannot extend both `x ++ [j]` and `x ++ [h]` for different labels `j ≠ h`.-/
theorem not_append_prefix_and {j h : L} (hjh : j ≠ h) {x y : List L} (hx : x ++ [j] <+: y)
    (hy : x ++ [h] <+: y) : False := by
  have hpre := List.prefix_of_prefix_length_le hx hy (by simp)
  have := hpre.eq_of_length (by simp)
  simp at this
  exact hjh this

/-- Chains with different labels have at most one common word (Lemma F.3, part 1).-/
theorem labelChain_inter_subsingleton {j h : L} (hjh : j ≠ h) {T T' : Set (List L)}
    (hT : IsLabelChain j T) (hT' : IsLabelChain h T') : (T ∩ T').Subsingleton := by
  obtain ⟨s, hs, rfl⟩ := hT
  obtain ⟨s', hs', rfl⟩ := hT'
  intro w₁ hw₁ w₂ hw₂
  by_contra hne
  have hlen : ∀ {x y : List L} {k : L}, x ++ [k] <+: y → x.length < y.length := fun hp => by
    have := hp.length_le; simp at this; omega
  rcases append_prefix_of_mem_range hs hw₁.1 hw₂.1 hne with h₁ | h₁ <;>
    rcases append_prefix_of_mem_range hs' hw₁.2 hw₂.2 hne with h₂ | h₂
  · exact not_append_prefix_and hjh h₁ h₂
  · exact absurd (hlen h₁) (hlen h₂).asymm
  · exact absurd (hlen h₁) (hlen h₂).asymm
  · exact not_append_prefix_and hjh h₁ h₂

/-- If `a` contains all but finitely many words of every `j`-chain, then every word `t` has an
extension `s` such that every extension of `s ++ [j]` lies in `a`.-/
theorem exists_extension_forall_mem {j : L} {a : Set (List L)}
    (ha : ∀ T : Set (List L), IsLabelChain j T → (T \ a).Finite) (t : List L) :
    ∃ s, t <+: s ∧ ∀ u, s ++ [j] <+: u → u ∈ a := by
  by_contra hcon
  push Not at hcon
  let g : {s // t <+: s} → {s // t <+: s} := fun s =>
    ⟨(hcon s.1 s.2).choose,
      s.2.trans ((List.prefix_append _ _).trans (hcon s.1 s.2).choose_spec.1)⟩
  let seq : ℕ → List L := fun r => (g^[r] ⟨t, List.prefix_refl t⟩).1
  have hstep : ∀ r, seq (r + 1) = (hcon (seq r) (g^[r] ⟨t, List.prefix_refl t⟩).2).choose :=
    fun r => by simp only [seq, Function.iterate_succ_apply']; rfl
  have hchain : ∀ r, seq r ++ [j] <+: seq (r + 1) := fun r => by
    rw [hstep]; exact (hcon _ (g^[r] ⟨t, List.prefix_refl t⟩).2).choose_spec.1
  have hout : ∀ r, seq (r + 1) ∉ a := fun r => by
    rw [hstep]; exact (hcon _ (g^[r] ⟨t, List.prefix_refl t⟩).2).choose_spec.2
  have hmono : StrictMono fun r => (seq r).length := strictMono_nat_of_lt_succ fun r => by
    have := (hchain r).length_le; simp at this; omega
  have hinj : Function.Injective fun r => seq (r + 1) := fun r m hrm =>
    Nat.succ_injective (hmono.injective (congrArg List.length hrm))
  refine (Set.infinite_range_of_injective hinj).mono ?_ (ha _ ⟨seq, hchain, rfl⟩)
  rintro _ ⟨r, rfl⟩
  exact ⟨⟨r + 1, rfl⟩, hout r⟩

/-- Chain gap (Lemma F.3, part 2): if, for each label `j`, the set `a j` contains all but
finitely many words of every `j`-chain, then the sets `a j` have a common word.-/
theorem iInter_nonempty_of_cofinite_on_chains [Fintype L] (a : L → Set (List L))
    (ha : ∀ j : L, ∀ T : Set (List L), IsLabelChain j T → (T \ a j).Finite) :
    (⋂ j, a j).Nonempty := by
  classical
  have key : ∀ S : Finset L, ∃ t : List L, ∀ j ∈ S, ∀ u, t <+: u → u ∈ a j := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨[], by simp⟩
    | insert j S _ ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨s, hts, hs⟩ := exists_extension_forall_mem (ha j) t
      refine ⟨s ++ [j], fun i hi u hu => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hs u hu
      · exact ht i hi u (hts.trans ((List.prefix_append _ _).trans hu))
  obtain ⟨t, ht⟩ := key Finset.univ
  exact ⟨t, Set.mem_iInter.2 fun j => ht j (Finset.mem_univ j) t (List.prefix_refl t)⟩

end AlternatingAnalytic.ChainGap
