/-
OEIS A347722: the number of perfect matchings of `K_n` is `(n-1)!!` for even `n` and 0 for
odd `n`.

Proof: generalise to matchings covering an arbitrary vertex set `A` (`pmOn A`), and induct on
`A.card`, splitting by the partner `p` of a fixed vertex `v ∈ A`.
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs
import Tengoku.Seed.Algebra.Group.Nat.Even
import Tengoku.Seed.Data.Fintype.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.card_pms` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722.Matchings

open Finset

variable {n : ℕ}

/--
@isnad1 id=iff.0h3v.s6.303619781a14 from=translated src=- shape=2135564b vocab=ae9bf85f
-/
lemma deg_eq_one_iff {S : Finset (Finset (Fin n))} {v : Fin n} :
    deg S v = 1 ↔ ∃ e ∈ S, v ∈ e ∧ ∀ g ∈ S, v ∈ g → g = e := by
  unfold deg
  rw [card_eq_one]
  constructor
  · rintro ⟨e, he⟩
    have h1 : e ∈ S.filter fun e => v ∈ e := by rw [he]; exact mem_singleton_self e
    rw [mem_filter] at h1
    refine ⟨e, h1.1, h1.2, fun g hg hvg => ?_⟩
    have h2 : g ∈ S.filter fun e => v ∈ e := mem_filter.2 ⟨hg, hvg⟩
    rw [he] at h2
    exact mem_singleton.1 h2
  · rintro ⟨e, heS, hve, huniq⟩
    refine ⟨e, ?_⟩
    ext g
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hg, hvg⟩
      exact huniq g hg hvg
    · intro h
      rw [h]
      exact ⟨heS, hve⟩

/--
@isnad1 id=ex.2h3v.s6.54f9cea29686 from=translated src=- shape=3ee5806f vocab=3059f1c0
-/
lemma exists_pair {e : Finset (Fin n)} {v : Fin n} (h : e.card = 2) (hv : v ∈ e) :
    ∃ p, p ≠ v ∧ e = {v, p} := by
  rw [card_eq_two] at h
  obtain ⟨x, y, hxy, rfl⟩ := h
  rw [mem_insert, mem_singleton] at hv
  rcases hv with h | h
  · rw [h]
    exact ⟨y, hxy.symm, rfl⟩
  · rw [h]
    exact ⟨x, hxy, pair_comm _ _⟩

/-- The perfect matchings of the complete graph on the vertex set `A`.-/
def pmOn (A : Finset (Fin n)) : Finset (Finset (Finset (Fin n))) :=
  (A.powersetCard 2).powerset.filter fun S => ∀ v ∈ A, deg S v = 1

/--
@isnad1 id=iff.0h3v.s7.5c5199409e3d from=translated src=- shape=7b375857 vocab=60f83df0
-/
lemma mem_pmOn {A : Finset (Fin n)} {S : Finset (Finset (Fin n))} :
    S ∈ pmOn A ↔ (∀ e ∈ S, e ⊆ A ∧ e.card = 2) ∧
      ∀ w ∈ A, ∃ e ∈ S, w ∈ e ∧ ∀ g ∈ S, w ∈ g → g = e := by
  unfold pmOn
  rw [mem_filter, mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun e he => mem_powersetCard.1 (h1 he), fun w hw => deg_eq_one_iff.1 (h2 w hw)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun e he => mem_powersetCard.2 (h1 e he), fun w hw => deg_eq_one_iff.2 (h2 w hw)⟩

/--
@isnad1 id=not.3h5v.s6.a257075e7a73 from=translated src=- shape=29fa4a4e vocab=cacbdd22
-/
lemma notMem_of_mem_pmOn {B : Finset (Fin n)} {S : Finset (Finset (Fin n))} (hS : S ∈ pmOn B)
    {g : Finset (Fin n)} (hg : g ∈ S) {x : Fin n} (hx : x ∉ B) : x ∉ g :=
  fun h => hx (((mem_pmOn.1 hS).1 g hg).1 h)

/--
@isnad1 id=mem.3h5v.s7.6b6157bc03a1 from=translated src=- shape=ff83a67f vocab=f9100db0
-/
lemma insert_mem_pmOn {A : Finset (Fin n)} {v p : Fin n} (hv : v ∈ A) (hp : p ∈ A.erase v)
    {S' : Finset (Finset (Fin n))} (hS : S' ∈ pmOn ((A.erase v).erase p)) :
    insert {v, p} S' ∈ pmOn A := by
  have hpv : p ≠ v := ne_of_mem_erase hp
  have hpA : p ∈ A := mem_of_mem_erase hp
  have hvB : v ∉ (A.erase v).erase p := fun h => notMem_erase v A (mem_of_mem_erase h)
  have hpB : p ∉ (A.erase v).erase p := notMem_erase p _
  obtain ⟨h1, h2⟩ := mem_pmOn.1 hS
  rw [mem_pmOn]
  constructor
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · refine ⟨?_, card_pair hpv.symm⟩
      intro x hx
      rcases mem_insert.1 hx with h | h
      · rw [h]; exact hv
      · rw [mem_singleton.1 h]; exact hpA
    · exact ⟨(h1 e he).1.trans ((erase_subset _ _).trans (erase_subset _ _)), (h1 e he).2⟩
  · intro w hw
    by_cases hwv : w = v
    · refine ⟨{v, p}, mem_insert_self _ _, by rw [hwv]; exact mem_insert_self _ _,
        fun g hg hwg => ?_⟩
      rcases mem_insert.1 hg with h | h
      · exact h
      · rw [hwv] at hwg
        exact absurd hwg (notMem_of_mem_pmOn hS h hvB)
    by_cases hwp : w = p
    · refine ⟨{v, p}, mem_insert_self _ _, by rw [hwp]; simp, fun g hg hwg => ?_⟩
      rcases mem_insert.1 hg with h | h
      · exact h
      · rw [hwp] at hwg
        exact absurd hwg (notMem_of_mem_pmOn hS h hpB)
    · have hwB : w ∈ (A.erase v).erase p := mem_erase.2 ⟨hwp, mem_erase.2 ⟨hwv, hw⟩⟩
      obtain ⟨e, he, hwe, hu⟩ := h2 w hwB
      refine ⟨e, mem_insert_of_mem he, hwe, fun g hg hwg => ?_⟩
      rcases mem_insert.1 hg with h | h
      · rw [h, mem_insert, mem_singleton] at hwg
        rcases hwg with h' | h'
        · exact absurd h' hwv
        · exact absurd h' hwp
      · exact hu g h hwg

/--
@isnad1 id=mem.4h5v.s7.f46f6a85f89b from=translated src=- shape=0e99676e vocab=f9100db0
-/
lemma erase_mem_pmOn {A : Finset (Fin n)} {v p : Fin n} {S : Finset (Finset (Fin n))}
    (hS : S ∈ pmOn A) (hv : v ∈ A) (hpA : p ∈ A) (he : {v, p} ∈ S) :
    S.erase {v, p} ∈ pmOn ((A.erase v).erase p) := by
  obtain ⟨h1, h2⟩ := mem_pmOn.1 hS
  have hvp : ∀ g ∈ S, v ∈ g → g = {v, p} := by
    intro g hg hvg
    obtain ⟨e, _, _, hu⟩ := h2 v hv
    exact (hu g hg hvg).trans (hu _ he (mem_insert_self _ _)).symm
  have hpp : ∀ g ∈ S, p ∈ g → g = {v, p} := by
    intro g hg hpg
    obtain ⟨e, _, _, hu⟩ := h2 p hpA
    exact (hu g hg hpg).trans (hu _ he (by simp)).symm
  rw [mem_pmOn]
  constructor
  · intro g hg
    obtain ⟨hne, hgS⟩ := mem_erase.1 hg
    refine ⟨fun x hx => ?_, (h1 g hgS).2⟩
    refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, (h1 g hgS).1 hx⟩⟩
    · intro h
      rw [h] at hx
      exact hne (hpp g hgS hx)
    · intro h
      rw [h] at hx
      exact hne (hvp g hgS hx)
  · intro w hw
    obtain ⟨hwp, hw'⟩ := mem_erase.1 hw
    obtain ⟨hwv, hwA⟩ := mem_erase.1 hw'
    obtain ⟨e, heS, hwe, hu⟩ := h2 w hwA
    refine ⟨e, mem_erase.2 ⟨?_, heS⟩, hwe, fun g hg hwg => hu g (mem_of_mem_erase hg) hwg⟩
    intro h
    rw [h, mem_insert, mem_singleton] at hwe
    rcases hwe with h' | h'
    · exact hwv h'
    · exact hwp h'

/--
@isnad1 id=eq.1h3v.s7.5ade7c41e1ca from=translated src=- shape=68598365 vocab=5884aba0
-/
lemma pmOn_eq_biUnion {A : Finset (Fin n)} {v : Fin n} (hv : v ∈ A) :
    pmOn A = (A.erase v).biUnion fun p =>
      (pmOn ((A.erase v).erase p)).image (insert {v, p}) := by
  ext S
  rw [mem_biUnion]
  constructor
  · intro hS
    obtain ⟨h1, h2⟩ := mem_pmOn.1 hS
    obtain ⟨e, heS, hve, -⟩ := h2 v hv
    obtain ⟨p, hpv, rfl⟩ := exists_pair (h1 e heS).2 hve
    have hpA : p ∈ A := (h1 _ heS).1 (by simp)
    exact ⟨p, mem_erase.2 ⟨hpv, hpA⟩,
      mem_image.2 ⟨_, erase_mem_pmOn hS hv hpA heS, insert_erase heS⟩⟩
  · rintro ⟨p, hp, hS⟩
    obtain ⟨S', hS', rfl⟩ := mem_image.1 hS
    exact insert_mem_pmOn hv hp hS'

/--
@isnad1 id=eq.1h3v.s6.da0bab8ad494 from=translated src=- shape=312ceac6 vocab=fea8cd17
-/
lemma card_pmOn_rec {A : Finset (Fin n)} {v : Fin n} (hv : v ∈ A) :
    (pmOn A).card = ∑ p ∈ A.erase v, (pmOn ((A.erase v).erase p)).card := by
  have hvB : ∀ p, v ∉ (A.erase v).erase p := fun p h => notMem_erase v A (mem_of_mem_erase h)
  rw [pmOn_eq_biUnion hv, card_biUnion]
  · refine sum_congr rfl fun p hp => card_image_of_injOn ?_
    intro S hS T hT hST
    have h1 : ({v, p} : Finset (Fin n)) ∉ S :=
      fun h => notMem_of_mem_pmOn (mem_coe.1 hS) h (hvB p) (mem_insert_self _ _)
    have h2 : ({v, p} : Finset (Fin n)) ∉ T :=
      fun h => notMem_of_mem_pmOn (mem_coe.1 hT) h (hvB p) (mem_insert_self _ _)
    have hST' : insert {v, p} S = insert {v, p} T := hST
    calc S = (insert {v, p} S).erase {v, p} := (erase_insert h1).symm
      _ = (insert {v, p} T).erase {v, p} := by rw [hST']
      _ = T := erase_insert h2
  · intro p hp q hq hpq
    rw [Function.onFun, disjoint_left]
    intro S hSp hSq
    obtain ⟨S', hS', rfl⟩ := mem_image.1 hSp
    obtain ⟨T', hT', hT⟩ := mem_image.1 hSq
    have hmem : ({v, p} : Finset (Fin n)) ∈ insert {v, q} T' := by
      rw [hT]; exact mem_insert_self _ _
    rcases mem_insert.1 hmem with h | h
    · have hp' : p ∈ ({v, q} : Finset (Fin n)) := by rw [← h]; simp
      rw [mem_insert, mem_singleton] at hp'
      rcases hp' with h' | h'
      · exact ne_of_mem_erase (mem_coe.1 hp) h'
      · exact hpq h'
    · exact notMem_of_mem_pmOn hT' h (hvB q) (mem_insert_self _ _)

/--
@isnad1 id=eq.0h1v.s5.0fc820ac2eb7 from=translated src=- shape=b33b02a9 vocab=82efcdcf
-/
lemma pmOn_empty : pmOn (∅ : Finset (Fin n)) = {∅} := by
  ext S
  rw [mem_pmOn, mem_singleton]
  constructor
  · rintro ⟨h1, -⟩
    refine eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨h3, h4⟩ := h1 e he
    rw [subset_empty.1 h3, card_empty] at h4
    exact absurd h4 (by decide)
  · intro h
    rw [h]
    exact ⟨fun e he => absurd he (notMem_empty e), fun w hw => absurd hw (notMem_empty w)⟩

/--
@isnad1 id=eq.1h3v.s5.0c61509a965f from=translated src=- shape=5719e90d vocab=8d4f995c
-/
lemma card_pmOn : ∀ (k : ℕ) (A : Finset (Fin n)), A.card = k →
    (pmOn A).card = if Even k then Nat.doubleFactorial (k - 1) else 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA
    rcases k with _ | _ | m
    · rw [card_eq_zero.1 hA, pmOn_empty]
      simp
    · obtain ⟨v, hv⟩ : A.Nonempty := card_pos.1 (by omega)
      have h0 : A.erase v = ∅ := card_eq_zero.1 (by rw [card_erase_of_mem hv, hA])
      rw [card_pmOn_rec hv, h0]
      simp
    · obtain ⟨v, hv⟩ : A.Nonempty := card_pos.1 (by omega)
      have h : ∀ p ∈ A.erase v, (pmOn ((A.erase v).erase p)).card =
          if Even m then Nat.doubleFactorial (m - 1) else 0 := fun p hp =>
        ih m (by omega) _ (by
          have h3 := card_erase_of_mem hp
          have h4 := card_erase_of_mem hv
          omega)
      have he : Even (m + 1 + 1) ↔ Even m := by
        rw [add_assoc, Nat.even_add]
        simp
      rw [card_pmOn_rec hv, sum_const_nat h, card_erase_of_mem hv, hA]
      simp only [he]
      split_ifs with hm
      · cases m with
        | zero => rfl
        | succ j => exact (Nat.doubleFactorial_add_two j).symm
      · exact Nat.mul_zero _

end A347722.Matchings

namespace A347722

open Finset

/-- The number of perfect matchings of `K_n` is `(n-1)!!` when `n` is even and 0 otherwise.
@isnad1 id=eq.0h1v.s5.cb5932da80a6 from=translated src=- shape=e17c37dc vocab=48030e9e
-/
theorem card_pms (n : ℕ) :
    ((verts n).powerset.filter PM).card = if Even n then Nat.doubleFactorial (n - 1) else 0 := by
  have h : (verts n).powerset.filter PM = Matchings.pmOn (univ : Finset (Fin n)) := by
    unfold Matchings.pmOn verts
    exact filter_congr fun S _ => by simp [PM]
  rw [h]
  exact Matchings.card_pmOn n univ (by simp)

end A347722

