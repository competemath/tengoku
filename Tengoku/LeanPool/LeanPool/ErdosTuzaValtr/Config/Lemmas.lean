/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/
module

public import Tengoku.LeanPool.LeanPool.ErdosTuzaValtr.Config.Defs
import Tengoku.LeanPool.LeanPool.ErdosTuzaValtr.Lib.List.Chain3
import Tengoku.LeanPool.LeanPool.ErdosTuzaValtr.Lib.List.Lemmas
public import Tengoku

/-!
# LeanPool.ErdosTuzaValtr.Config.Lemmas

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Config.Lemmas`.
-/

@[expose] public section

variable {α : Type _} [LinearOrder α] {C : Config α}

namespace Config

namespace Cap

/--
@isnad1 id=cap.0h2v.s3.949178d79236 from=translated src=- shape=fa25e355 vocab=ebbb739d
-/
@[simp]
protected theorem nil : C.Cap [] := by rw [Config.Cap]; tauto

/--
@isnad1 id=cap.0h3v.s4.56eb6def87ca from=translated src=- shape=c45fec91 vocab=0fa3d5d6
-/
@[simp]
protected theorem singleton (a : α) : C.Cap [a] := by rw [Config.Cap]; simp

/--
@isnad1 id=iff.0h4v.s5.7d3e7d7c7836 from=translated src=- shape=6c9e3d65 vocab=b87b244e
-/
@[simp]
protected theorem pair {a b : α} : C.Cap [a, b] ↔ a < b := by rw [Config.Cap]; simp

/--
@isnad1 id=iff.0h6v.s6.94b23e16b2ed from=translated src=- shape=1440fe65 vocab=e4501847
-/
@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cap (a::b::c::l) ↔ a < b ∧ C.Cap3 a b c ∧ C.Cap (b::c::l) := by
  simp only [Config.Cap, List.isChain_cons_cons, List.chain3'_cons]
  tauto

/--
@isnad1 id=iff.0h7v.s6.bee87ad91bb4 from=translated src=- shape=ce554b95 vocab=c6e1851f
-/
@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cap (l1 ++ a::b::c::l2) ↔ C.Cap (l1 ++ [a, b]) ∧ C.Cap3 a b c ∧ C.Cap (b::c::l2) := by
  simp only [Config.Cap, List.chain3'_append_cons3, List.isChain_append_cons_cons,
    List.isChain_cons_cons]
  tauto

/--
@isnad1 id=cap.1h3v.s4.42c368f62a18 from=translated src=- shape=6aae355c vocab=df44fbfa
-/
protected theorem dropLast {l : List α} (h : C.Cap l) : C.Cap l.dropLast :=
  ⟨h.left.dropLast, h.right.dropLast⟩

/--
@isnad1 id=cap.1h3v.s4.d44f79931a72 from=translated src=- shape=6aae355c vocab=f660ef19
-/
protected theorem tail {l : List α} (h : C.Cap l) : C.Cap l.tail :=
  ⟨h.left.tail, h.right.tail⟩

end Cap

namespace NCap

/--
@isnad1 id=ncap.1h4v.s5.416e8a3e142a from=translated src=- shape=eac1c845 vocab=6c58598b
-/
protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.dropLast :=
  ⟨h.1.dropLast, by rw [List.length_dropLast, h.2, Nat.add_sub_cancel]⟩

/--
@isnad1 id=ncap.1h4v.s5.2cfb5dcea76a from=translated src=- shape=eac1c845 vocab=76d8570b
-/
protected theorem tail {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.tail :=
  ⟨h.1.tail, by rw [List.length_tail, h.2, Nat.add_sub_cancel]⟩

end NCap

namespace Cup

/--
@isnad1 id=cup.0h2v.s3.c81e85735139 from=translated src=- shape=fa25e355 vocab=25fb2b28
-/
@[simp]
protected theorem nil : C.Cup [] := by rw [Config.Cup]; tauto

/--
@isnad1 id=cup.0h3v.s4.be9d53970847 from=translated src=- shape=c45fec91 vocab=bc9edc63
-/
@[simp]
protected theorem singleton (a : α) : C.Cup [a] := by rw [Config.Cup]; simp

/--
@isnad1 id=iff.0h4v.s5.a017b34e1839 from=translated src=- shape=6c9e3d65 vocab=3f8d7f91
-/
@[simp]
protected theorem pair {a b : α} : C.Cup [a, b] ↔ a < b := by rw [Config.Cup]; simp

/--
@isnad1 id=iff.0h6v.s6.f7b4ecb7daa3 from=translated src=- shape=1440fe65 vocab=9e845585
-/
@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cup (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.Cup (b::c::l) := by
  simp only [Config.Cup, List.isChain_cons_cons, List.chain3'_cons]
  tauto

/--
@isnad1 id=iff.0h7v.s6.d1d627163037 from=translated src=- shape=ce554b95 vocab=f3e11766
-/
@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cup (l1 ++ a::b::c::l2) ↔ C.Cup (l1 ++ [a, b]) ∧ C.Cup3 a b c ∧ C.Cup (b::c::l2) := by
  simp only [Config.Cup, List.chain3'_append_cons3, List.isChain_append_cons_cons,
    List.isChain_cons_cons]
  tauto

/--
@isnad1 id=cup.1h3v.s4.b8242edd4cd9 from=translated src=- shape=6aae355c vocab=47dd2477
-/
protected theorem dropLast {l : List α} (h : C.Cup l) : C.Cup l.dropLast :=
  ⟨h.left.dropLast, h.right.dropLast⟩

/--
@isnad1 id=cup.1h4v.s4.7554ea3496fc from=translated src=- shape=b6195af4 vocab=a26407d3
-/
protected theorem take {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.take n) :=
  ⟨h.left.take n, h.right.take n⟩

/--
@isnad1 id=cup.1h4v.s4.605d4f4c9e49 from=translated src=- shape=b6195af4 vocab=f09e48d6
-/
protected theorem drop {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.drop n) :=
  ⟨h.left.drop n, h.right.drop n⟩

/--
@isnad1 id=cup.1h3v.s4.6c776a6bd3a7 from=translated src=- shape=6aae355c vocab=5190236f
-/
protected theorem tail {l : List α} (h : C.Cup l) : C.Cup l.tail :=
  ⟨h.left.tail, h.right.tail⟩

/--
@isnad1 id=lt.4h5v.s6.414f7c017ed8 from=translated src=- shape=55acef45 vocab=6bf9e1e5
-/
theorem head_lt_getLast {l : List α} (l_cup : C.Cup l) (p q : α) (hl : 2 ≤ l.length)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q := by
  cases l with
  | nil => exact absurd hp (Option.not_mem_none p)
  | cons x l =>
    rw [List.head?_cons, Option.mem_some_iff] at hp
    subst hp
    have l_nnil : l ≠ [] := by
      rintro rfl
      simp_all
    rcases List.takeLast l_nnil with ⟨q', l', eq_l⟩
    rw [eq_l, ← List.cons_append, List.getLast?_concat, Option.mem_some_iff] at hq
    have l_sorted := List.isChain_iff_pairwise.mp l_cup.left
    simp_all

end Cup

namespace NCup

/--
@isnad1 id=ncup.0h2v.s4.4fb475c96526 from=translated src=- shape=7384657a vocab=96ed99f0
-/
@[simp]
protected theorem nil : C.NCup 0 [] := by rw [Config.NCup, Config.Cup]; tauto

/--
@isnad1 id=ncup.0h3v.s4.9043b6d24eb3 from=translated src=- shape=dc476e3c vocab=4a728446
-/
@[simp]
protected theorem singleton (a : α) : C.NCup 1 [a] := by rw [Config.NCup, Config.Cup]; simp

/--
@isnad1 id=iff.0h4v.s5.cf4282c6fe0a from=translated src=- shape=ea31b95d vocab=96a40c24
-/
@[simp]
protected theorem pair {a b : α} : C.NCup 2 [a, b] ↔ a < b := by
  rw [Config.NCup, Config.Cup]; simp

/--
@isnad1 id=iff.0h7v.s6.d5655d85e580 from=translated src=- shape=14a9b8e5 vocab=dc986010
-/
@[simp]
protected theorem cons3 {n : ℕ} {a b c : α} {l : List α} :
    C.NCup (n + 1) (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.NCup n (b::c::l) := by
  simp only [Config.NCup, Cup.cons3, List.length_cons, Nat.add_right_cancel_iff]
  tauto

/--
@isnad1 id=ncup.1h4v.s5.31dabd847fed from=translated src=- shape=eac1c845 vocab=d73eb239
-/
protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.dropLast :=
  ⟨h.1.dropLast, by rw [List.length_dropLast, h.2, Nat.add_sub_cancel]⟩

/--
@isnad1 id=ex.1h4v.s6.89e92735c67b from=translated src=- shape=ea00a424 vocab=094e7477
-/
protected theorem dropLast_append_last {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (l' : List α) (a : α), l = l' ++ [a] ∧ C.NCup n l' := by
  have nnil : l ≠ [] := by
    rintro rfl
    rw [Config.NCup] at h
    simp_all
  exact ⟨l.dropLast, l.getLast nnil, (List.dropLast_append_getLast nnil).symm, h.dropLast⟩

/--
@isnad1 id=ncup.1h4v.s5.e44a210e5f67 from=translated src=- shape=eac1c845 vocab=1576a18a
-/
protected theorem tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.tail :=
  ⟨h.1.tail, by rw [List.length_tail, h.2, Nat.add_sub_cancel]⟩

/--
@isnad1 id=ex.1h4v.s5.fe7c92b96df9 from=translated src=- shape=bbca3d5e vocab=f2720a93
-/
protected theorem cons_head_tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (a : α) (l' : List α), (l = a::l') ∧ C.NCup n l' := by
  cases l with
  | nil =>
    rw [Config.NCup] at h
    simp_all
  | cons a l => exact ⟨a, l, rfl, h.tail⟩

/--
@isnad1 id=ex.1h4v.s6.82a94c26d5b7 from=translated src=- shape=363e7fc1 vocab=094e7477
-/
protected theorem take_head_last {n : ℕ} {l : List α} (h : C.NCup (n + 2) l) :
    ∃ (a : α) (l' : List α) (b : α), l = (a::l') ++ [b] ∧ C.NCup n l' := by
  rcases h.cons_head_tail with ⟨a, l', eq_l, cup_l'⟩
  rcases cup_l'.dropLast_append_last with ⟨l'', b, eq_l', cup_l''⟩
  simp_all

/--
@isnad1 id=ex.4h6v.s6.4bebbb60479c from=translated src=- shape=1cf3f600 vocab=4cf6567b
-/
theorem take_left_with_head {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.head? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.head? := by
  intro one_le_m m_le_n l_last
  refine ⟨l.take m, List.take_subset m l, ⟨h.left.take m, ?_⟩, ?_⟩
  · rw [List.length_take, h.right, Nat.min_eq_left m_le_n]
  · rw [← List.take_append_drop m l] at l_last
    rw [List.head?_append_of_ne_nil] at l_last
    · exact l_last
    · intro hnil
      rw [List.take_eq_nil_iff] at hnil
      rcases hnil with hm | hl
      · omega
      · simp_all

/--
@isnad1 id=ex.4h6v.s6.a433a9d403c7 from=translated src=- shape=1cf3f600 vocab=ba2b70bb
-/
theorem take_right_with_last {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.getLast? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.getLast? := by
  intro one_le_m m_le_n l_last
  refine ⟨l.drop (n - m), List.drop_subset (n - m) l, ⟨h.left.drop (n - m), ?_⟩, ?_⟩
  · rw [List.length_drop, h.right]
    omega
  · rw [← List.take_append_drop (n - m) l] at l_last
    rw [List.getLast?_append_of_ne_nil] at l_last
    · exact l_last
    · intro hnil
      have hlen : (l.drop (n - m)).length = 0 := by rw [hnil, List.length_nil]
      rw [List.length_drop, h.right] at hlen
      omega

/--
@isnad1 id=lt.3h6v.s6.9981eeac02f8 from=translated src=- shape=0a67331b vocab=23f1e3d4
-/
theorem head_lt_getLast {n : ℕ} {l : List α} (l_ncup : C.NCup (n + 2) l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q :=
  l_ncup.left.head_lt_getLast p q (by rw [l_ncup.right]; omega) hp hq

/--
@isnad1 id=le.3h6v.s6.99258a971aa0 from=translated src=- shape=4e44c9e2 vocab=fd00b879
-/
theorem head_le_getLast {n : ℕ} {l : List α} (l_ncup : C.NCup n l) (p q : α) (hp : p ∈ l.head?)
    (hq : q ∈ l.getLast?) : p ≤ q := by
  have l_sorted : l.Pairwise (· < ·) := List.isChain_iff_pairwise.mp l_ncup.left.left
  cases l with
  | nil => exact absurd hp (Option.not_mem_none p)
  | cons x rest =>
    rw [List.head?_cons, Option.mem_some_iff] at hp
    subst hp
    cases rest with
    | nil =>
      simp_all
    | cons p' rest =>
      rw [List.getLast?_cons_cons] at hq
      rw [List.pairwise_cons] at l_sorted
      exact le_of_lt (l_sorted.1 q (List.mem_of_mem_getLast? hq))

end NCup

end Config

/--
@isnad1 id=hasngon.2h4v.s5.8db08391d0bd from=translated src=- shape=240f6055 vocab=3fdd27e4
-/
theorem ncup_is_ngon {n : ℕ} {S : Finset α} (hn : 2 ≤ n) (h : C.HasNCup n S) : C.HasNGon n S := by
  rcases h with ⟨c, ⟨⟨c_cup, c_length⟩, c_in_S⟩⟩
  have hc : c ≠ [] := by
    rintro rfl
    rw [List.length_nil] at c_length
    omega
  rcases List.takeLast hc with ⟨y, c, eq_c⟩; subst eq_c
  have hc : c ≠ [] := by
    rintro rfl
    simp only [List.nil_append, List.length_cons, List.length_nil] at c_length
    omega
  rcases List.takeHead hc with ⟨x, c, eq_c⟩; subst eq_c
  clear hc
  have hxy : x < y :=
    c_cup.head_lt_getLast x y (by rw [c_length]; omega) (by simp) (by simp)
  refine ⟨[x, y], (x :: c) ++ [y], ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp
  · simp_all
  · simp_all
  · exact c_cup
  · simp
  · simp
  · simp only [List.length_cons, List.length_append, List.length_nil] at c_length ⊢
    omega
  · simp_all
  · exact c_in_S

/--
@isnad1 id=hasncap.2h5v.s5.8df4b31864f9 from=translated src=- shape=7888ab6c vocab=deadee63
-/
theorem hasNCap_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCap n S1) :
    C.HasNCap n S2 := by
  obtain ⟨c1, h1⟩ := h1
  exact ⟨c1, h1.left, fun a a_c1 => h (h1.right a a_c1)⟩

/--
@isnad1 id=hasncup.2h5v.s5.4f7c1f55c041 from=translated src=- shape=7888ab6c vocab=17ec6803
-/
theorem hasNCup_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCup n S1) :
    C.HasNCup n S2 := by
  obtain ⟨c1, h1⟩ := h1
  exact ⟨c1, h1.left, fun a a_c1 => h (h1.right a a_c1)⟩

/--
@isnad1 id=hasngon.2h5v.s5.3019a4a1063d from=translated src=- shape=7888ab6c vocab=b0a0beab
-/
theorem hasNGon_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNGon n S1) :
    C.HasNGon n S2 := by
  rcases h1 with ⟨c1, c2, ⟨gon, c1_in, c2_in⟩⟩
  exact ⟨c1, c2, gon, fun a a_c1 => h (c1_in a a_c1), fun a a_c2 => h (c2_in a a_c2)⟩

/--
@isnad1 id=hasncup.2h5v.s5.a3f14a3c0c33 from=translated src=- shape=94497edc vocab=17ec6803
-/
theorem hasNCup_le {n m : ℕ} {S : Finset α} (h : n ≤ m) : C.HasNCup m S → C.HasNCup n S := by
  rintro ⟨c, ⟨⟨c_cup, c_length⟩, c_in⟩⟩
  refine ⟨c.take n, ⟨c_cup.take n, ?_⟩, fun a ha => c_in a (List.take_subset _ _ ha)⟩
  rw [List.length_take, c_length, Nat.min_eq_left h]
