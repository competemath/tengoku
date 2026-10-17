import Tengoku.ImmermanVardi.Lax979537Proofs.TimedNodes
import Tengoku

namespace Lax979537Proofs.NodeInput

open Turing PersistentStack NodeMachine TimedNodes

variable {Id Symbol Initial : Type}

def head (xs : List (Id × Symbol)) : Option Id := xs.head?.map Prod.fst

def records : List (Id × Symbol) → Heap Id Symbol
  | [] => ∅
  | (n, a) :: xs => insert (n, a, head xs) (records xs)

/--
@isnad1 id=mem.1h6v.s6.921af5af342b from=translated src=- shape=7024a5ec vocab=0414910b
-/
theorem records_key {xs : List (Id × Symbol)} {n : Id} {a : Symbol} {p : Option Id}
    (h : (n, a, p) ∈ records xs) : n ∈ xs.map Prod.fst := by
  induction xs with
  | nil => exact False.elim h
  | cons x xs ih =>
      rcases x with ⟨m, b⟩
      rcases Set.mem_insert_iff.mp h with he | hr
      · cases he; simp
      · exact List.mem_cons_of_mem _ (ih hr)

/--
@isnad1 id=function.1h3v.s4.b2b665bdfd88 from=translated src=- shape=a8faab0a vocab=97881ab6
-/
theorem records_functional (xs : List (Id × Symbol)) (hn : (xs.map Prod.fst).Nodup) :
    Functional (records xs) := by
  induction xs with
  | nil => intro n a p b q h; exact False.elim h
  | cons x xs ih =>
      rcases x with ⟨n, a⟩
      have h : n ∉ xs.map Prod.fst ∧ (xs.map Prod.fst).Nodup := by simpa using hn
      exact insert_functional (ih h.2) (fun a p hp => h.1 (records_key hp)) a (head xs)

/--
@isnad1 id=chain.0h3v.s4.b22fd0e59670 from=translated src=- shape=ad912180 vocab=6cba9d04
-/
theorem records_chain (xs : List (Id × Symbol)) : Chain (records xs) (head xs) (xs.map Prod.snd) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact push_chain ih x.1 x.2

variable (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (ids : Fin xs.length → Initial)

/-- The identifiers are abstract and may later be tuples encoding input
blocks. This construction does not require arithmetic flat bit addresses. -/
def entries : List (Node Initial × Sigma tm.Γ) :=
  List.ofFn (fun i => (Sum.inl (ids i), Sigma.mk tm.k₀ (xs.get i)))

def heap : Records (Node Initial) tm.Γ := records (entries tm xs ids)

def config : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (Node Initial) :=
  ⟨.boundary (some tm.main), tm.initialState,
    Function.update (fun _ => none) tm.k₀ (head (entries tm xs ids))⟩

/--
@isnad1 id=eq.0h4v.s6.0378b0a698a3 from=translated src=- shape=cacee4fa vocab=3788d163
-/
theorem entries_values : (entries tm xs ids).map Prod.snd = xs.map (Sigma.mk tm.k₀) := by
  rw [entries, List.map_ofFn]
  simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map (Sigma.mk tm.k₀)) (List.ofFn_get xs)

/--
@isnad1 id=function.1h4v.s5.32af159ff6ed from=translated src=- shape=dfeac63f vocab=19a0d2dd
-/
theorem heap_functional (hi : Function.Injective ids) : Functional (heap tm xs ids) := by
  apply records_functional
  rw [entries, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro i j he
  exact hi (Sum.inl.inj he)

/--
@isnad1 id=bounded.0h4v.s5.08bee0353ca4 from=translated src=- shape=3387c291 vocab=58e38ce4
-/
theorem heap_bounded : Bounded (heap tm xs ids) 0 := by
  intro n a p hn
  have hk := records_key hn
  obtain ⟨entry, hm, he⟩ := List.mem_map.mp hk
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  cases he
  trivial

/--
@isnad1 id=matches.0h4v.s5.41cc8905940b from=translated src=- shape=02a0a753 vocab=8d5536a6
-/
theorem config_matches : Matches (heap tm xs ids) (config tm xs ids) (TM2Micro.boundary (initList tm xs)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro k
  by_cases hk : k = tm.k₀
  · subst k
    have h := records_chain (entries tm xs ids)
    rw [entries_values] at h
    simpa [config, TM2Micro.boundary, initList, heap] using h
  · simpa [config, TM2Micro.boundary, initList, hk] using (Chain.nil (H := heap tm xs ids))

/-- Every input has a complete persistent-node run, whose represented
configuration agrees with the normalized TM2 at every time.
@isnad1 id=ex.1h5v.s7.670b2160c215 from=translated src=- shape=c5e1bed8 vocab=e8a9c3ff
-/
theorem represented_run (hi : Function.Injective ids) (t : Nat) :
    ∃ H c, Run tm.m (heap tm xs ids) (config tm xs ids) t H c ∧
      Functional H ∧ Bounded H t ∧
      Matches H c ((TM2Micro.next tm.m)^[t] (TM2Micro.boundary (initList tm xs))) := by
  obtain ⟨H, c, hr⟩ := run_exists tm.m (heap tm xs ids) (config tm xs ids)
    (heap_functional tm xs ids hi) (heap_bounded tm xs ids) _ (config_matches tm xs ids) t
  exact ⟨H, c, hr, run_sound hr (heap_functional tm xs ids hi) (heap_bounded tm xs ids)
    _ (config_matches tm xs ids)⟩

end Lax979537Proofs.NodeInput
