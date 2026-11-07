module

public import Tengoku.Seed.Order.PFilter
public import Tengoku.Seed.Data.Set.Countable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace Nat

/--
@isnad1 id=var.3h4v.s5.f822a841f80e from=translated src=- shape=a9cb7561 vocab=9f93770a
-/
lemma monotone_of_succ_monotone {r : ℕ → ℕ → Prop} (rfx : Std.Refl r) (tr : IsTrans ℕ r)
    (succ : ∀ n, r n (n + 1)) : n ≤ m → r n m := by
  revert n m
  suffices ∀ n d, r n (n + d) by
    intro n m hnm
    have := this n (m - n)
    grind
  intro n d
  induction d
  case zero => simp [rfx.refl n]
  case succ d ih =>
    simpa using! tr.trans _ _ _ ih (succ (n + d))

end Nat

namespace DirectedOn

variable {α : Type*} {r : α → α → Prop}

end DirectedOn

namespace Order

variable {α : Type*} [Preorder α]

/-! ### Compatibility and incompatibility -/

def IsCompatiblePair (a b : α) : Prop := ∃ c, c ≤ a ∧ c ≤ b

scoped infix:50 " ‖ " => IsCompatiblePair

/--
@isnad1 id=iscompat.0h2v.s3.8b4cf66f6b38 from=translated src=- shape=e6608552 vocab=00100528
-/
@[simp, refl] protected lemma IsCompatiblePair.refl (a : α) : a ‖ a := ⟨a, by simp⟩

/--
@isnad1 id=iff.0h3v.s4.5cdec4d0075e from=translated src=- shape=bc89b7d4 vocab=00100528
-/
@[symm] protected lemma IsCompatiblePair.symm_iff {a b : α} : a ‖ b ↔ b ‖ a := by
  constructor
  · rintro ⟨c, hca, hcb⟩; exact ⟨c, hcb, hca⟩
  · rintro ⟨c, hcb, hca⟩; exact ⟨c, hca, hcb⟩

/--
@isnad1 id=iscompat.1h3v.s4.cdc22886085b from=translated src=- shape=2da0c23b vocab=00100528
-/
alias ⟨IsCompatiblePair.symm, _⟩ := IsCompatiblePair.symm_iff

def IsIncompatiblePair (a b : α) : Prop := ¬(a ‖ b)

scoped infix:50 " ⟂ " => IsIncompatiblePair

/--
@isnad1 id=not.0h2v.s3.3a62c80020bb from=translated src=- shape=d8399986 vocab=d3300c62
-/
@[simp] lemma IsIncompatiblePair.antirefl (a : α) : ¬(a ⟂ a) := by simp [IsIncompatiblePair]

/--
@isnad1 id=iff.0h3v.s4.3c24bf94b68c from=translated src=- shape=bc89b7d4 vocab=d3300c62
-/
lemma IsIncompatiblePair.symm_iff {a b : α} : a ⟂ b ↔ b ⟂ a := by
  contrapose; simpa [IsIncompatiblePair] using IsCompatiblePair.symm_iff

/--
@isnad1 id=isincomp.1h3v.s4.a8c3ead31256 from=translated src=- shape=2da0c23b vocab=d3300c62
-/
alias ⟨IsIncompatiblePair.symm, _⟩ := IsIncompatiblePair.symm_iff

/--
@isnad1 id=iff.0h3v.s4.a6a40b6a9b70 from=translated src=- shape=158c7052 vocab=b1d1dd32
-/
@[simp, grind =] lemma not_isCompatiblePair_iff_isIncompatiblePair {a b : α} : ¬(a ‖ b) ↔ a ⟂ b := by
  rfl

/--
@isnad1 id=iff.0h3v.s4.753eb899de2b from=translated src=- shape=158c7052 vocab=b1d1dd32
-/
@[simp, grind =] lemma not_isIncompatiblePair_iff_isCompatiblePair {a b : α} : ¬(a ⟂ b) ↔ a ‖ b := by
  simp [IsIncompatiblePair, IsCompatiblePair]

/-! ### Density -/

def IsDense (s : Set α) : Prop := ∀ p, ∃ q ≤ p, q ∈ s

def IsDenseBelow (s : Set α) (a : α) : Prop := ∀ p ≤ a, ∃ q ≤ p, q ∈ s

variable (α)

@[ext] structure DenseSet where
  set : Set α
  is_dense : IsDense set

variable {α}

namespace DenseSet

instance : SetLike (DenseSet α) α where
  coe s := s.set
  coe_injective s t e := by ext; simp_all

noncomputable def choose (d : DenseSet α) (a : α) : α := (d.is_dense a).choose

/--
@isnad1 id=le.0h3v.s4.2876c2b050af from=translated src=- shape=016e4879 vocab=46a1c0ba
-/
@[simp] lemma choose_le (d : DenseSet α) (a : α) : d.choose a ≤ a := (d.is_dense a).choose_spec.1

/--
@isnad1 id=mem.0h3v.s4.eac941976143 from=translated src=- shape=ccccc6fc vocab=fe375397
-/
@[simp] lemma choose_mem (d : DenseSet α) (a : α) : d.choose a ∈ d := (d.is_dense a).choose_spec.2

end DenseSet

namespace PFilter

def ofDescendingChain (s : ℕ → α) (hs : ∀ i j, i ≤ j → s i ≥ s j) : PFilter α :=
  IsPFilter.toPFilter <| Order.IsPFilter.of_def (F := {x | ∃ i, s i ≤ x})
    ⟨s 0, 0, by rfl⟩
    (by rintro x₁ ⟨i₁, h₁⟩ x₂ ⟨i₂, h₂⟩
        wlog hi : i₁ ≤ i₂
        · have z : i₂ ≤ i₁ := by exact Nat.le_of_not_ge hi
          rcases this s hs x₂ i₂ h₂ x₁ i₁ h₁ (Nat.le_of_not_ge hi) with ⟨z, hz⟩
          exact ⟨z, hz.1, hz.2.2, hz.2.1⟩
        exact ⟨s i₂, ⟨i₂, by rfl⟩, le_trans (hs i₁ i₂ hi) h₁, by simp [h₂]⟩)
    (by rintro x y hxy ⟨i, hix⟩
        exact ⟨i, le_trans hix hxy⟩)

/--
@isnad1 id=iff.1h3v.s6.5e969373d082 from=translated src=- shape=4225e430 vocab=4466628e
-/
@[simp] lemma mem_descendingChain_iff (s : ℕ → α) (hs : ∀ i j, i ≤ j → s i ≥ s j) :
    x ∈ ofDescendingChain s hs ↔ ∃ i, s i ≤ x := by rfl

class IsGeneric (F : PFilter α) (𝓓 : Set (DenseSet α)) where
  isGeneric : ∀ d ∈ 𝓓, ∃ a ∈ F, a ∈ d

/--
@isnad1 id=isgeneri.0h2v.s4.c7d442291424 from=translated src=- shape=9d886063 vocab=5df4b0bf
-/
@[simp] instance IsGeneric.empty (F : PFilter α) : F.IsGeneric ∅ := ⟨by simp⟩

/--
@isnad1 id=ex.1h3v.s5.eba699d2b2da from=translated src=- shape=c883bf10 vocab=a152f9b5
-/
theorem exists_genericFilter_of_countable
    (𝓓 : Set (DenseSet α)) (ctb : Set.Countable 𝓓) (a : α) :
    ∃ G : PFilter α, G.IsGeneric 𝓓 ∧ a ∈ G := by
  by_cases emp : 𝓓.Nonempty
  case neg =>
    exact ⟨principal a, by simp [Set.not_nonempty_iff_eq_empty.mp emp], by simp⟩
  have : ∃ D : ℕ → 𝓓, Function.Surjective D := ctb.exists_surjective emp
  rcases this with ⟨D, hD⟩
  let s (n : ℕ) : α := n.rec a fun i ↦ (D i).val.choose
  have hs : ∀ i j, i ≤ j → s i ≥ s j := fun i j hij ↦
    Nat.monotone_of_succ_monotone (r := fun i j ↦ s i ≥ s j)
      ⟨fun _ ↦ le_refl _⟩
      ⟨fun _ _ _ ↦ ge_trans⟩
      (by simp [s]) hij
  refine ⟨ofDescendingChain s hs, ⟨?_⟩, ?_⟩
  · intro d hd
    rcases show ∃ i, D i = ⟨d, hd⟩ from hD ⟨d, hd⟩ with ⟨i, hi⟩
    refine ⟨s (i + 1), ?_, ?_⟩
    · simp only [mem_descendingChain_iff]
      exact ⟨i + 1, by rfl⟩
    · simp [s, hi]
  · suffices ∃ i, s i ≤ a by simpa
    refine ⟨0, by simp [s]⟩

end PFilter

end Order
