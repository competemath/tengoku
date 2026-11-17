import Tengoku.AdianRabin.GroupUndecidability.Thue.Matiyasevich.Reduction
import Tengoku.Seed.Data.Set.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace FiniteReindex

noncomputable section

variable {α β : Type*}

/-- Number of genuine relations in a finite set.-/
def ruleCount (T : ThueSystem α) (hT : T.Finite) : ℕ :=
  @Fintype.card T hT.fintype

def ruleEquiv (T : ThueSystem α) (hT : T.Finite) :
    T ≃ Fin (ruleCount T hT) := by
  letI : Fintype T := hT.fintype
  exact Fintype.equivFin T

/-- Enumerate a finite relation set and adjoin one harmless identity rule at
index zero.  The extra rule makes the index type provably nonempty even when
the supplied set happens to be empty.-/
def enumeratedF (T : ThueSystem α) (hT : T.Finite) :
    Fin (ruleCount T hT + 1) → List α :=
  Fin.cases [] fun i => (ruleEquiv T hT).symm i |>.1.1

def enumeratedE (T : ThueSystem α) (hT : T.Finite) :
    Fin (ruleCount T hT + 1) → List α :=
  Fin.cases [] fun i => (ruleEquiv T hT).symm i |>.1.2

/--
@isnad1 id=eq.1h2v.s6.36ee2d4f45b5 from=translated src=- shape=516c22a8 vocab=ee91eb12
-/
theorem enumeratedSystem_eq (T : ThueSystem α) (hT : T.Finite) :
    finiteSystem (enumeratedF T hT) (enumeratedE T hT) =
      insert ([], []) T := by
  ext pair
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · exact Set.mem_insert_iff.mpr (Or.inr ((ruleEquiv T hT).symm j).2)
  · intro hp
    rcases Set.mem_insert_iff.mp hp with hid | hTpair
    · subst pair
      exact ⟨0, rfl⟩
    · let z : T := ⟨pair, hTpair⟩
      refine ⟨Fin.succ (ruleEquiv T hT z), ?_⟩
      have hz : (ruleEquiv T hT).symm (ruleEquiv T hT z) = z :=
        (ruleEquiv T hT).symm_apply_apply z
      exact Prod.ext (congrArg (fun w => w.1.1) hz)
        (congrArg (fun w => w.1.2) hz)

private theorem step_insert_identity {T : ThueSystem α}
    {X Y : List α} (h : ThueStep (insert ([], []) T) X Y) :
    X = Y ∨ ThueStep T X Y := by
  rcases h with ⟨l, r, x, y, hxy, hwords⟩
  rcases Set.mem_insert_iff.mp hxy with hid | hT
  · injection hid with hx hy
    subst x
    subst y
    rcases hwords with ⟨hX, hY⟩ | ⟨hX, hY⟩
    · exact Or.inl (hX.trans hY.symm)
    · exact Or.inl (hX.trans hY.symm)
  · exact Or.inr ⟨l, r, x, y, hT, hwords⟩

/--
@isnad1 id=iff.0h4v.s5.d4d9e345d9fc from=translated src=- shape=eeca511f vocab=5ef0572f
-/
theorem insert_identity_iff (T : ThueSystem α) (X Y : List α) :
    ThueEq (insert ([], []) T) X Y ↔ ThueEq T X Y := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
        rcases step_insert_identity hstep with heq | hT
        · subst heq
          exact ih
        · exact ih.tail hT
  · intro h
    exact h.lift id fun _ _ hstep => by
      rcases hstep with ⟨l, r, x, y, hxy, hwords⟩
      exact ⟨l, r, x, y, Set.mem_insert_iff.mpr (Or.inr hxy), hwords⟩

/--
@isnad1 id=iff.1h4v.s5.2bc8062cb9db from=translated src=- shape=ff36638e vocab=ab0110f7
-/
theorem enumerated_iff (T : ThueSystem α) (hT : T.Finite)
    (X Y : List α) :
    ThueEq (finiteSystem (enumeratedF T hT) (enumeratedE T hT)) X Y ↔
      ThueEq T X Y := by
  rw [enumeratedSystem_eq, insert_identity_iff]

/-- Homomorphic word transport along an equivalence of finite alphabets.-/
def mapWord (e : α ≃ β) (W : List α) : List β := W.map e

/--
@isnad1 id=eq.0h5v.s5.7619a3291958 from=translated src=- shape=fc6ea939 vocab=5e832ec4
-/
@[simp] theorem mapWord_append (e : α ≃ β) (X Y : List α) :
    mapWord e (X ++ Y) = mapWord e X ++ mapWord e Y := by
  simp [mapWord]

/--
@isnad1 id=eq.0h4v.s4.b810c02dacaa from=translated src=- shape=2ce9bb00 vocab=c1c89c7f
-/
@[simp] theorem mapWord_symm_mapWord (e : α ≃ β) (W : List α) :
    mapWord e.symm (mapWord e W) = W := by
  simp [mapWord]

/--
@isnad1 id=computab.0h3v.s5.2b550b8a9be1 from=translated src=- shape=7bbdad61 vocab=18dea13d
-/
theorem mapWord_computable [Primcodable α] [Primcodable β] [Finite α]
    (e : α ≃ β) : Computable (mapWord e) :=
  (Primrec.list_map Primrec.id
    ((Primrec.dom_finite e).comp₂ Primrec₂.right)).to_comp

def mappedF {s : ℕ} (e : α ≃ β) (F : Fin s → List α) :
    Fin s → List β := fun i => mapWord e (F i)

def mappedE {s : ℕ} (e : α ≃ β) (E : Fin s → List α) :
    Fin s → List β := fun i => mapWord e (E i)

private theorem mapped_step {s : ℕ} (e : α ≃ β)
    (F E : Fin s → List α) {X Y : List α}
    (h : ThueStep (finiteSystem F E) X Y) :
    ThueStep (finiteSystem (mappedF e F) (mappedE e E))
      (mapWord e X) (mapWord e Y) := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  refine ⟨mapWord e l, mapWord e r, mappedF e F i, mappedE e E i,
    ⟨i, rfl⟩, ?_⟩
  rcases hwords with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · exact Or.inl ⟨by simpa [mappedF, mapWord_append] using congrArg (mapWord e) hX,
      by simpa [mappedE, mapWord_append] using congrArg (mapWord e) hY⟩
  · exact Or.inr ⟨by simpa [mappedE, mapWord_append] using congrArg (mapWord e) hX,
      by simpa [mappedF, mapWord_append] using congrArg (mapWord e) hY⟩

private theorem decoded_step {s : ℕ} (e : α ≃ β)
    (F E : Fin s → List α) {X Y : List β}
    (h : ThueStep (finiteSystem (mappedF e F) (mappedE e E)) X Y) :
    ThueStep (finiteSystem F E) (mapWord e.symm X) (mapWord e.symm Y) := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  refine ⟨mapWord e.symm l, mapWord e.symm r, F i, E i,
    ⟨i, rfl⟩, ?_⟩
  rcases hwords with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · left
    constructor
    · simpa [mappedF, mapWord_append] using congrArg (mapWord e.symm) hX
    · simpa [mappedE, mapWord_append] using congrArg (mapWord e.symm) hY
  · right
    constructor
    · simpa [mappedE, mapWord_append] using congrArg (mapWord e.symm) hX
    · simpa [mappedF, mapWord_append] using congrArg (mapWord e.symm) hY

def alphabetEmbedding {s : ℕ} [Primcodable α] [Primcodable β] [Finite α]
    (e : α ≃ β) (F E : Fin s → List α) :
    Embedding (finiteSystem F E)
      (finiteSystem (mappedF e F) (mappedE e E)) where
  encode := mapWord e
  encode_computable := mapWord_computable e
  thueEq_iff := fun X Y => by
    constructor
    · intro h
      exact h.lift (mapWord e) fun _ _ hstep => mapped_step e F E hstep
    · intro h
      have hd := h.lift (mapWord e.symm)
        fun _ _ hstep => decoded_step e F E hstep
      change Relation.ReflTransGen (ThueStep (finiteSystem F E))
        (mapWord e.symm (mapWord e X)) (mapWord e.symm (mapWord e Y)) at hd
      change Relation.ReflTransGen (ThueStep (finiteSystem F E)) X Y
      simpa using hd

/-- Convert any finite fixed-target Thue problem over a nonempty finite
alphabet into the exact `Fin n`/`Fin r` seed expected by the compression
theorem.
@isnad1 id=ex.2h3v.s6.5e0ad74b5535 from=translated src=- shape=caab224e vocab=62db7e7f
-/
theorem seed_of_finite_system [Fintype α] [Nonempty α] [Primcodable α]
    (T : ThueSystem α) (hT : T.Finite) (P : List α)
    (hund : ¬ ComputablePred fun Q : List α => ThueEq T Q P) :
    ∃ seed : FiniteFixedTargetSeed,
      seed.alphabetSize = Fintype.card α ∧
      seed.relationCount = ruleCount T hT + 1 := by
  let e := Fintype.equivFin α
  let Fα := enumeratedF T hT
  let Eα := enumeratedE T hT
  let Ffin := mappedF e Fα
  let Efin := mappedE e Eα
  have henum : ¬ ComputablePred fun Q : List α =>
      ThueEq (finiteSystem Fα Eα) Q P := by
    intro hdec
    apply hund
    exact hdec.of_eq fun Q => enumerated_iff T hT Q P
  have hmapped : ¬ ComputablePred fun Q : List (Fin (Fintype.card α)) =>
      ThueEq (finiteSystem Ffin Efin) Q (mapWord e P) :=
    (alphabetEmbedding e Fα Eα).target_undecidable P henum
  refine ⟨{
    alphabetSize := Fintype.card α
    relationCount := ruleCount T hT + 1
    alphabetSize_pos := Fintype.card_pos
    relationCount_pos := by omega
    F := Ffin
    E := Efin
    P := mapWord e P
    undecidable := hmapped
  }, rfl, rfl⟩

end
end FiniteReindex
end Matiyasevich1993
end Thue
end Undecidability
