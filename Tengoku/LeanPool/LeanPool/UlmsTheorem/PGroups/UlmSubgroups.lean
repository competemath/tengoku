/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.UlmsTheorem.PGroups.Subgroups

/-!
# Ordinal Ulm subgroups

This file contains the transfinite Ulm filtration `ulmSubgroup` and its basic
structural lemmas.
-/

@[expose] public section

namespace UlmsTheorem

open Ordinal

variable (p : ℕ)

/-- `p^α·G` by transfinite recursion:
`p^0·G = G`, `p^(α+1)·G = {p•x | x ∈ p^α·G}`, and
`p^λ·G = ⋂_{β<λ} p^β·G`. -/
noncomputable def ulmSubgroup {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddSubgroup G :=
  α.limitRecOn
    ⊤
    (fun _β Hβ ↦ pImage p Hβ)
    (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)

section UlmSubgroupLemmas

variable {G : Type*} [AddCommGroup G]

/--
@isnad1 id=eq.0h2v.s5.affd132e26b4 from=translated src=- shape=4d105b1f vocab=aebc0a2e
-/
@[simp] lemma ulmSubgroup_zero : ulmSubgroup p (0 : Ordinal) (G := G) = ⊤ := by
  rw [ulmSubgroup, Ordinal.limitRecOn_zero]

/--
@isnad1 id=eq.0h3v.s5.e7bfc9af99a8 from=translated src=- shape=02c6d235 vocab=ad24e18d
-/
lemma ulmSubgroup_add_one (α : Ordinal) :
    ulmSubgroup p (α + 1) (G := G) = pImage p (ulmSubgroup p α) := by
  rw [ulmSubgroup, Ordinal.limitRecOn_add_one, ulmSubgroup]

/--
@isnad1 id=eq.0h3v.s5.547748392c57 from=translated src=- shape=2efb4eb9 vocab=2a695740
-/
lemma ulmSubgroup_succ (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) = pImage p (ulmSubgroup p α) := by
  simpa using ulmSubgroup_add_one p (G := G) α

/--
@isnad1 id=eq.1h3v.s6.8c07e8269d70 from=translated src=- shape=790faac0 vocab=b99b8ca3
-/
lemma ulmSubgroup_limit (o : Ordinal) (ho : Order.IsSuccLimit o) :
    ulmSubgroup p o (G := G) = ⨅ (β : Ordinal) (_ : β < o), ulmSubgroup p β := by
  unfold ulmSubgroup
  simpa using
    (Ordinal.limitRecOn_limit o
      (⊤ : AddSubgroup G)
      (fun _β Hβ ↦ pImage p Hβ)
      (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)
      ho)

/--
@isnad1 id=iff.0h4v.s6.cc6b5cfbe3be from=translated src=- shape=b6cf69b3 vocab=364ff1bb
-/
lemma mem_ulmSubgroup_succ_iff (α : Ordinal) (x : G) :
    x ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by
  rw [ulmSubgroup_succ, mem_pImage]

/--
@isnad1 id=iff.0h4v.s6.f74ad44b6680 from=translated src=- shape=701313e9 vocab=542a66d2
-/
@[simp] lemma mem_ulmSubgroup_add_one_iff (α : Ordinal) (x : G) :
    x ∈ ulmSubgroup p (α + 1) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by
  rw [ulmSubgroup_add_one, mem_pImage]

/--
@isnad1 id=iff.1h4v.s6.b4acace81799 from=translated src=- shape=813d50ad vocab=03007c1a
-/
lemma mem_ulmSubgroup_limit_iff {o : Ordinal} (ho : Order.IsSuccLimit o) (x : G) :
    x ∈ ulmSubgroup p o (G := G) ↔ ∀ β < o, x ∈ ulmSubgroup p β := by
  rw [ulmSubgroup_limit (p := p) (G := G) o ho]
  simp only [AddSubgroup.mem_iInf]

/--
@isnad1 id=antitone.0h2v.s5.5cc61647ae81 from=translated src=- shape=0f0b298a vocab=971a7c5c
-/
lemma ulmSubgroup_antitone : Antitone (fun α ↦ ulmSubgroup p α (G := G)) := by
  let P : Ordinal → Prop := fun β ↦ ∀ α, α ≤ β → ulmSubgroup p β (G := G) ≤ ulmSubgroup p α
  have hP : ∀ β, P β := by
    intro β
    induction β using Ordinal.limitRecOn with
    | zero =>
        intro α hαβ
        have h0 : α = 0 := le_antisymm hαβ bot_le
        simp [h0]
    | add_one β ih =>
        intro α hαβ
        have hs : ulmSubgroup p (β + 1) (G := G) ≤ ulmSubgroup p β := by
          rw [ulmSubgroup_add_one]
          intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          simpa using (ulmSubgroup p β (G := G)).nsmul_mem hy p
        rcases lt_or_eq_of_le hαβ with hlt | rfl
        · exact hs.trans (ih α (Order.le_of_lt_succ hlt))
        · exact le_rfl
    | limit o ho IH =>
        intro α hαβ
        rcases lt_or_eq_of_le hαβ with hlt | rfl
        · rw [ulmSubgroup_limit p o ho]
          exact iInf_le_of_le α (iInf_le _ hlt)
        · exact le_rfl
  intro α β hαβ
  exact hP β α hαβ

/--
@isnad1 id=eq.0h3v.s4.71095321ecb3 from=translated src=- shape=bf54ffc1 vocab=19b045f7
-/
lemma ulmSubgroup_nat (n : ℕ) : ulmSubgroup p (n : Ordinal) (G := G) = pPow p n := by
  induction n with
  | zero =>
      rw [show ((0 : ℕ) : Ordinal) = 0 by simp, ulmSubgroup_zero, pPow_zero_eq]
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : Ordinal) = (n : Ordinal) + 1 by simp]
      rw [ulmSubgroup_add_one, ih, pImage_pPow]

/--
@isnad1 id=iff.0h4v.s6.48eccd6ea8a8 from=translated src=- shape=44563350 vocab=ab3fcfd9
-/
lemma mem_ulmSubgroup_nat_iff (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (n : Ordinal) (G := G) ↔ ∃ y : G, p ^ n • y = x := by
  rw [ulmSubgroup_nat, pPow_mem_iff]

/--
@isnad1 id=iff.0h5v.s6.08fb509809fe from=translated src=- shape=ce583363 vocab=2d70e592
-/
lemma mem_ulmSubgroup_add_nat_iff (α : Ordinal) (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (α + n) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x := by
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : Ordinal) = (n : Ordinal) + 1 by simp,
        ← add_assoc, mem_ulmSubgroup_add_one_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases (ih z).1 hz with ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        rw [pow_succ, mul_smul, smul_comm]
      · rintro ⟨y, hy, hxy⟩
        refine ⟨p ^ n • y, (ih _).2 ⟨y, hy, rfl⟩, ?_⟩
        rw [← hxy, pow_succ, mul_smul, smul_comm]

/--
@isnad1 id=eq.0h4v.s6.e50caa35f2ea from=translated src=- shape=a7ec586a vocab=1e299e1c
-/
lemma ulmSubgroup_add_nat (α : Ordinal) (n : ℕ) :
    ulmSubgroup p (α + n) (G := G) =
      { x | ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x } := by
  ext x
  exact mem_ulmSubgroup_add_nat_iff (p := p) (G := G) α n x

/--
@isnad1 id=le.0h5v.s6.c6c042315fa6 from=translated src=- shape=702060be vocab=6518251c
-/
lemma map_ulmSubgroup_le {H : Type*} [AddCommGroup H] (φ : G →+ H) (α : Ordinal) :
    (ulmSubgroup p α (G := G)).map φ ≤ ulmSubgroup p α (G := H) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      simp [ulmSubgroup]
  | add_one α ih =>
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [ulmSubgroup_add_one] at hx ⊢
      rcases hx with ⟨z, hz, rfl⟩
      exact ⟨φ z, ih ⟨z, hz, rfl⟩, by simp⟩
  | limit o ho IH =>
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change x ∈ ulmSubgroup p o at hx
      rw [mem_ulmSubgroup_limit_iff p ho] at hx ⊢
      intro β hβ
      exact IH β hβ ⟨x, hx β hβ, rfl⟩

/-- Translating by a multiple of an element already in `G_β` does not change
membership in `G_β`.
@isnad1 id=iff.1h6v.s6.89dba85cdc4c from=translated src=- shape=92793a50 vocab=8261e7b2
-/
lemma add_zsmul_mem_iff_of_mem {β : Ordinal.{0}} {x c : G}
    (hx : x ∈ ulmSubgroup p β (G := G)) (n : ℤ) :
    c + n • x ∈ ulmSubgroup p β (G := G) ↔ c ∈ ulmSubgroup p β (G := G) := by
  constructor
  · intro h
    simpa using (ulmSubgroup p β (G := G)).sub_mem h
      ((ulmSubgroup p β (G := G)).zsmul_mem hx n)
  · intro h
    exact (ulmSubgroup p β (G := G)).add_mem h
      ((ulmSubgroup p β (G := G)).zsmul_mem hx n)

end UlmSubgroupLemmas

end UlmsTheorem
