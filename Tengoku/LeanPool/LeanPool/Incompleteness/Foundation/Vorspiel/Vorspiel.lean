/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku

/-! # Vorspiel -/

@[expose] public section

namespace Nat
variable {α : ℕ → Sort u}

/-- Imported declaration from the Incompleteness formalization. -/
def cases (hzero : α 0) (hsucc : ∀ n, α (n + 1)) : ∀ n, α n
  | 0     => hzero
  | n + 1 => hsucc n

/-- Imported declaration from the Incompleteness formalization. -/
infixr:70 " :>ₙ " => cases

/--
@isnad1 id=eq.0h3v.s5.1879621b537f from=translated src=- shape=e00cd555 vocab=65fd84c8
-/
@[simp] lemma cases_zero (hzero : α 0) (hsucc : ∀ n, α (n + 1)) :
    (hzero :>ₙ hsucc) 0 = hzero := rfl

/--
@isnad1 id=eq.0h4v.s6.a8d3b028fd8d from=translated src=- shape=27716164 vocab=65fd84c8
-/
@[simp] lemma cases_succ (hzero : α 0) (hsucc : ∀ n, α (n + 1)) (n : ℕ) :
    (hzero :>ₙ hsucc) (n + 1) = hsucc n := rfl

/--
@isnad1 id=ne.0h2v.s4.2d3022eed7d8 from=translated src=- shape=104b0572 vocab=ab6c7516
-/
@[simp 1100] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt <| Nat.lt_succ_of_le <| by simp

/--
@isnad1 id=ne.0h2v.s4.f3baed99e5a9 from=translated src=- shape=9208c8cd vocab=ab6c7516
-/
lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt <| Nat.lt_succ_of_le <| by simp

/--
@isnad1 id=eq.1h5v.s5.89983cb6d7c8 from=translated src=- shape=a5e43217 vocab=515d8573
-/
lemma rec_eq {α : Sort*} (a : α) (f₁ f₂ : ℕ → α → α) (n : ℕ) (H : ∀ m < n, ∀ a, f₁ m a = f₂ m a) :
    (n.rec a f₁ : α) = n.rec a f₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (n.rec a f₁ : α) = n.rec a f₂ := ih (fun m hm a => H m (Nat.lt_succ_of_lt hm) a)
    simpa [this] using H n (Nat.lt_add_one n) (n.rec a f₂)

/--
@isnad1 id=ex.1h1v.s5.85c565ee1850 from=translated src=- shape=52d1329b vocab=7f9bb019
-/
lemma least_number (P : ℕ → Prop) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ z < x, ¬P z := by
  classical
  exact ⟨Nat.find hP, Nat.find_spec hP, fun z hz => Nat.find_min hP hz⟩

/-- Imported declaration from the Incompleteness formalization. -/
def toFin (n : ℕ) : ℕ → Option (Fin n) := fun x => if hx : x < n then some ⟨x, hx⟩ else none

end Nat

lemma eq_finZeroElim {α : Sort u} (x : Fin 0 → α) : x = finZeroElim :=
  funext (by rintro ⟨_, _⟩; contradiction)

namespace Matrix
open _root_.Matrix.Fin
section «lp_section_1»
variable {n : ℕ} {α : Type u}

/-- Imported declaration from the Incompleteness formalization. -/
infixr:70 " :> " => vecCons

/--
@isnad1 id=eq.0h4v.s4.d872dbbdd324 from=translated src=- shape=8747a370 vocab=843c31bb
-/
@[simp 1100] lemma vecCons_zero :
    (a :> s) 0 = a := by simp

/--
@isnad1 id=eq.0h5v.s4.40f40e074d5e from=translated src=- shape=286a283f vocab=85b76dd5
-/
@[simp 1100] lemma vecCons_succ (i : Fin n) :
    (a :> s) (Fin.succ i) = s i := by simp

/--
@isnad1 id=eq.0h4v.s5.0df9f9d6d38d from=translated src=- shape=4f641898 vocab=01476789
-/
@[simp] lemma vecCons_last (a : C) (s : Fin (n + 1) → C) :
    (a :> s) (Fin.last (n + 1)) = s (Fin.last n) := vecCons_succ (Fin.last n)

/-- Imported declaration from the Incompleteness formalization. -/
def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t

/--
@isnad1 id=eq.0h4v.s5.48fa452a3af5 from=translated src=- shape=2a8d0aa3 vocab=1fd599ce
-/
@[simp] lemma cons_app_one {n : ℕ} (a : α) (s : Fin n.succ → α) : (a :> s) 1 = s 0 := rfl

/--
@isnad1 id=eq.0h4v.s5.ace2f7d82661 from=translated src=- shape=d77f5e7a vocab=1fd599ce
-/
@[simp] lemma cons_app_two {n : ℕ} (a : α) (s : Fin n.succ.succ → α) : (a :> s) 2 = s 1 := rfl

/--
@isnad1 id=eq.0h4v.s5.94a759591990 from=translated src=- shape=06984ee5 vocab=1fd599ce
-/
@[simp] lemma cons_app_three {n : ℕ} (a : α) (s : Fin n.succ.succ.succ → α) : (a :> s) 3 = s 2 :=
  rfl

section «lp_section_2»
open Lean PrettyPrinter Delaborator SubExpr

/-- Imported declaration from the Incompleteness formalization. -/
meta def unexpandVecEmpty : Unexpander
  | `($(_)) => `(![])

/-- Imported declaration from the Incompleteness formalization. -/
meta def unexpandVecCons : Unexpander
  | `($(_) $a ![])      => `(![$a])
  | `($(_) $a ![$as,*]) => `(![$a, $as,*])
  | _                   => throw ()

end «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
infixl:70 " <: " => vecConsLast

/--
@isnad1 id=eq.0h4v.s4.cd104b5661d8 from=translated src=- shape=6a8847d6 vocab=448a6cab
-/
@[simp] lemma rightConcat_last :
    (s <: a) (Fin.last n) = a := by simp [vecConsLast]

/--
@isnad1 id=eq.0h5v.s4.3450c3afa815 from=translated src=- shape=adb3a051 vocab=95d00e9a
-/
@[simp] lemma rightConcat_castSucc (i : Fin n) :
    (s <: a) (Fin.castSucc i) = s i := by simp [vecConsLast]

/--
@isnad1 id=eq.0h4v.s5.b022993f85bc from=translated src=- shape=4e220a46 vocab=c6f35706
-/
@[simp] lemma rightConcat_zero (a : α) (s : Fin n.succ → α) :
    (s <: a) 0 = s 0 := rightConcat_castSucc 0

/--
@isnad1 id=eq.0h1v.s6.a0b91f98d25e from=translated src=- shape=599278d5 vocab=4b19adfc
-/
@[simp] lemma zero_succ_eq_id {n} : (0 : Fin (n + 1)) :> Fin.succ = id :=
  funext <| Fin.cases (by simp) (by simp)

/--
@isnad1 id=eq.0h3v.s6.03617677bd3b from=translated src=- shape=f021961a vocab=45f36e8e
-/
@[simp] lemma zero_cons_succ_eq_self (f : Fin (n + 1) → α) : (f 0 :> (f ·.succ) :
    Fin (n + 1) → α) = f := by
    funext x; cases x using Fin.cases <;> simp

lemma eq_vecCons (s : Fin (n + 1) → C) : s = s 0 :> s ∘ Fin.succ :=
   funext <| Fin.cases (by simp) (by simp)

/--
@isnad1 id=iff.0h6v.s5.96aeaa2c9b95 from=translated src=- shape=dde4cd28 vocab=843c31bb
-/
@[simp 1100] lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by simp_all,
   by intros h; simp [h]⟩

/--
@isnad1 id=eq.0h5v.s5.2b188efeb19e from=translated src=- shape=6110b283 vocab=c82a9443
-/
lemma vecCons_assoc (a b : α) (s : Fin n → α) :
    a :> (s <: b) = (a :> s) <: b := by
  funext x
  cases x using Fin.cases with
  | zero => simp
  | succ x =>
    cases x using Fin.lastCases
    · simp
    · rename_i i
      simp only [Nat.succ_eq_add_one, vecCons_succ, rightConcat_castSucc]
      rw [Fin.succ_castSucc]
      exact ((rightConcat_castSucc (a := b) (s := a :> s) i.succ).trans
        (vecCons_succ i)).symm

/-- Imported declaration from the Incompleteness formalization. -/
def decVec {α : Type _} : {n : ℕ} → (v w :
    Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simpa [Matrix.empty_eq] using isTrue trivial
  | n + 1, v, w, d => by
      rw [eq_vecCons v, eq_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simpa using d _)
      refine instDecidableAnd

/--
@isnad1 id=eq.0h6v.s5.da2e9a19c1d2 from=translated src=- shape=e8090c5d vocab=e4ca62f8
-/
lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f <| (a :> s) x) = f a :> f ∘ s :=
funext (fun i => Fin.cases (by simp) (by simp) i)

/--
@isnad1 id=eq.0h6v.s5.7a27b1eb5e4e from=translated src=- shape=1e77a79e vocab=843c31bb
-/
lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f <| (a :> s) x) = f a :> fun i => f (s i) :=
  comp_vecCons f a s

/--
@isnad1 id=eq.0h6v.s5.b9e2922dbd1c from=translated src=- shape=cebe2927 vocab=e4ca62f8
-/
lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) : f ∘ (a :> s) = f a :> f ∘ s :=
  comp_vecCons f a s

/--
@isnad1 id=eq.0h3v.s4.c73b467b1e71 from=translated src=- shape=cfb04557 vocab=4a301899
-/
@[simp] lemma comp₀ : f ∘ (![] : Fin 0 → α) = ![] := by simp [Matrix.empty_eq]

/--
@isnad1 id=eq.0h4v.s5.17eb4af28dcd from=translated src=- shape=b71d4f75 vocab=3dd43b50
-/
@[simp] lemma comp₁ (a : α) : f ∘ ![a] = ![f a] := by simp [comp_vecCons'']

/--
@isnad1 id=eq.0h5v.s6.8b6f3901576b from=translated src=- shape=a9bb82fc vocab=3dd43b50
-/
@[simp] lemma comp₂ (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by simp [comp_vecCons'']

/--
@isnad1 id=eq.0h6v.s6.5371acfb47a7 from=translated src=- shape=8c8515c6 vocab=3dd43b50
-/
@[simp] lemma comp₃ (a₁ a₂ a₃ : α) :
    f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by
  simp [comp_vecCons'']

/--
@isnad1 id=eq.0h6v.s5.a401154f5761 from=translated src=- shape=e0971c1a vocab=87ca8339
-/
lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f <| (s <: a) x) = f ∘ s <: f a :=
funext (fun i => Fin.lastCases (by simp) (by simp) i)

/--
@isnad1 id=eq.0h5v.s5.10e90404ef49 from=translated src=- shape=c9fc1092 vocab=f38551cf
-/
@[simp 1100] lemma vecHead_comp (f : α → β) (v : Fin (n + 1) → α) :
    vecHead (f ∘ v) = f (vecHead v) :=
  by simp [vecHead]

/--
@isnad1 id=eq.0h5v.s5.2167f51dd534 from=translated src=- shape=c7fb7468 vocab=366033b5
-/
lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) := by
  simp [vecTail, Function.comp_assoc]

/--
@isnad1 id=eq.0h3v.s5.d47d19cde16c from=translated src=- shape=b401356f vocab=760aa2be
-/
lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : s <: a = ![a] :=
  funext (fun x => by
    cases x using Fin.cases with
    | zero => rw [show (0 : Fin 1) = Fin.last 0 from rfl, rightConcat_last, cons_val_fin_one]
    | succ i => exact absurd i.isLt (by simp))

/--
@isnad1 id=eq.0h2v.s5.6a8f05ac6c3a from=translated src=- shape=1dd93c5d vocab=4e3792ea
-/
lemma constant_eq_singleton {a : α} : (fun _ => a) = ![a] := by funext x; simp

/--
@isnad1 id=eq.0h2v.s5.b0faef6113cd from=translated src=- shape=b5b7e1e9 vocab=c2a09f20
-/
lemma constant_eq_singleton' {v : Fin 1 → α} : v = ![v 0] := by funext x; simp [Fin.eq_zero]

/--
@isnad1 id=eq.0h2v.s5.806859fa78dc from=translated src=- shape=71e11587 vocab=4e3792ea
-/
lemma constant_eq_vec₂ {a : α} : (fun _ => a) = ![a, a] := by
  funext x; cases x using Fin.cases <;> simp [Fin.eq_zero]

/--
@isnad1 id=eq.0h2v.s6.c3997ffe67d7 from=translated src=- shape=0cabfa5e vocab=4e3792ea
-/
lemma fun_eq_vec₂ {v : Fin 2 → α} : v = ![v 0, v 1] := by
  funext x; cases x using Fin.cases <;> simp [Fin.eq_zero]

/--
@isnad1 id=injectiv.2h4v.s5.2dcd477bc9f2 from=translated src=- shape=21615416 vocab=bd008ede
-/
lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) :
    Function.Injective (a :> f) := by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases
  · simp
  · simp [*]
  · simp [*]
  · simpa using @h _ _

end «lp_section_1»

variable {α : Type _}

/-- Imported declaration from the Incompleteness formalization. -/
def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)

/--
@isnad1 id=eq.0h2v.s4.c74b85395062 from=translated src=- shape=d706415c vocab=7e225416
-/
@[simp] lemma toList_zero (v : Fin 0 → α) : toList v = [] := rfl

/--
@isnad1 id=eq.0h3v.s6.a03ff3fc1b78 from=translated src=- shape=701003be vocab=9902f9c3
-/
@[simp] lemma toList_succ (v : Fin (n + 1) → α) : toList v = v 0 :: toList (v ∘ Fin.succ) := rfl

/--
@isnad1 id=eq.0h3v.s4.7163581ac1e7 from=translated src=- shape=49dad9db vocab=8366606a
-/
@[simp] lemma toList_length (v : Fin n → α) : (toList v).length = n :=
  by induction n <;> simp [*]

/--
@isnad1 id=iff.0h4v.s5.c63ceec8b311 from=translated src=- shape=5e31e1b1 vocab=ba433c80
-/
@[simp] lemma mem_toList_iff {v : Fin n → α} {a} : a ∈ toList v ↔ ∃ i, v i = a := by
  induction n
  · simp [*]
  · suffices (a = v 0 ∨ ∃ i : Fin _, v i.succ = a) ↔ ∃ i, v i = a by simp [*]
    constructor
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
    · rintro ⟨i, rfl⟩; cases i using Fin.cases <;> simp

variable {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}

/-- Imported declaration from the Incompleteness formalization. -/
def getM : {n : ℕ} → {β : Fin n → Type u} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0,     _, _ => pure finZeroElim
  | _ + 1, _, f => Fin.cases <$> f 0 <*> getM (f ·.succ)

/--
@isnad1 id=eq.0h4v.s6.094f57fc746a from=translated src=- shape=d402a7c8 vocab=dd34ee0c
-/
lemma getM_pure [LawfulMonad m] {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (pure (v i) : m (β i))) = pure v := by
  induction n with
  | zero =>
    unfold getM; congr; funext x; exact x.elim0
  | succ n ih =>
    simp only [getM, map_pure, ih, seq_pure]
    exact congr_arg _ (funext <| Fin.cases rfl fun i ↦ rfl)

/--
@isnad1 id=eq.0h3v.s5.27a3c55c9385 from=translated src=- shape=563a9aa2 vocab=8863229d
-/
@[simp] lemma getM_some {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (some (v i) : Option (β i))) = some v := getM_pure v

/-- Imported declaration from the Incompleteness formalization. -/
def appendr {n m} (v : Fin n → α) (w : Fin m → α) : Fin (m + n) → α :=
  Matrix.vecAppend (add_comm m n) v w

/--
@isnad1 id=eq.0h3v.s5.67d0a6a4bdc2 from=translated src=- shape=590887a2 vocab=eb83267a
-/
@[simp] lemma appendr_nil {m} (w : Fin m → α) : appendr ![] w = w := by funext i; simp [appendr]

/--
@isnad1 id=eq.0h6v.s5.5cf9886baee4 from=translated src=- shape=6529e634 vocab=06ca0c7f
-/
@[simp] lemma appendr_cons {m n} (x : α) (v : Fin n → α) (w : Fin m → α) :
    appendr (x :> v) w = x :> appendr v w := by
  funext i; simp [appendr]

section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
def vecToNat : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0,     _ => 0
  | _ + 1, v => Nat.pair (v 0) (vecToNat <| v ∘ Fin.succ) + 1

open Encodable

/--
@isnad1 id=eq.0h1v.s4.1cd92a3f74fe from=translated src=- shape=4c9eca03 vocab=9d7c98b3
-/
@[simp] lemma vecToNat_empty (v : Fin 0 → ℕ) : vecToNat v = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.a4de61002db9 from=translated src=- shape=67b1dc72 vocab=9b792c8f
-/
@[simp] lemma encode_succ {n} (x : ℕ) (v : Fin n → ℕ) :
    vecToNat (x :> v) = Nat.pair x (vecToNat v) + 1 := by
  simp [vecToNat, Function.comp_def]

end «lp_section_3»

end Matrix

namespace DMatrix

/-- Imported declaration from the Incompleteness formalization. -/
def vecEmpty : Fin 0 → α :=
  Fin.elim0

variable {n} {α : Fin (n + 1) → Type*}

/-- Imported declaration from the Incompleteness formalization. -/
def vecCons (h : α 0) (t : (i : Fin n) → α i.succ) : (i : Fin n.succ) → α i :=
  Fin.cons h t

/-- Imported declaration from the Incompleteness formalization. -/
infixr:70 " ::> " => vecCons

/--
@isnad1 id=eq.0h4v.s6.58305af64d7b from=translated src=- shape=aca7bf84 vocab=ee683319
-/
@[simp] lemma vecCons_zero (h : α 0) (t : (i : Fin n) → α i.succ) : (h ::> t) 0 = h := rfl

/--
@isnad1 id=eq.0h5v.s6.b5f00fb74c7a from=translated src=- shape=1cf5d119 vocab=e98fbdb5
-/
@[simp] lemma vecCons_succ (h : α 0) (t : (i : Fin n) → α i.succ) (i : Fin n) :
    (h ::> t) i.succ = t i :=
  rfl

lemma eq_vecCons (s : (i : Fin (n + 1)) → α i) : s = s 0 ::> fun i => s i.succ :=
   funext <| Fin.cases (by simp) (by simp)

/--
@isnad1 id=iff.0h6v.s7.86bce4b1c4b4 from=translated src=- shape=4f5735b3 vocab=ee683319
-/
@[simp] lemma vecCons_ext (a₁ a₂ : α 0) (s₁ s₂ : (i : Fin n) → α i.succ) :
    a₁ ::> s₁ = a₂ ::> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h i.succ),
   by intros h; simp [h]⟩

/-- Imported declaration from the Incompleteness formalization. -/
def decVec {n : ℕ} {α : Fin n → Type _}
  (v w : (i : Fin n) → α i) (h : ∀ i, Decidable (v i = w i)) : Decidable (v = w) := by
    induction n with
    | zero => exact isTrue (by funext x; exact finZeroElim (α := fun x => v x = w x) x)
    | succ n ih =>
      rw [eq_vecCons v, eq_vecCons w, vecCons_ext]
      haveI := ih (fun i => v i.succ) (fun i => w i.succ) (fun i => h i.succ)
      refine instDecidableAnd

end DMatrix

namespace Option

/--
@isnad1 id=eq.0h2v.s4.baae56cc4043 from=translated src=- shape=fd3b2b4d vocab=91387296
-/
lemma pure_eq_some (a : α) : pure a = some a := rfl

/--
@isnad1 id=iff.0h3v.s4.7fa96c669958 from=translated src=- shape=0065ffb2 vocab=64937914
-/
@[simp 1100] lemma toList_eq_iff {o : Option α} {a} :
    o.toList = [a] ↔ o = some a := by rcases o <;> simp

end Option

/-- Imported declaration from the Incompleteness formalization. -/
def Nat.natToVec : ℕ → (n : ℕ) → Option (Fin n → ℕ)
  | 0,     0     => some Matrix.vecEmpty
  | e + 1, n + 1 => Nat.natToVec e.unpair.2 n |>.map (e.unpair.1 :> ·)
  | _,     _     => none

namespace Nat
open Matrix
variable {n : ℕ}

/--
@isnad1 id=eq.0h2v.s4.d19538180ec2 from=translated src=- shape=8daf1934 vocab=2bd80956
-/
@[simp] lemma natToVec_vecToNat (v : Fin n → ℕ) : (vecToNat v).natToVec n = some v := by
  induction n
  · simp [*, Nat.natToVec, vecToNat, Matrix.empty_eq]
  · suffices v 0 :> v ∘ Fin.succ = v by simp [*, Nat.natToVec, vecToNat]
    exact funext (fun i ↦ i.cases (by simp []) (by simp ))

/--
@isnad1 id=lt.1h4v.s5.1cb0ce7acf71 from=translated src=- shape=b64c7df3 vocab=4857f765
-/
lemma lt_of_eq_natToVec {e : ℕ} {v : Fin n → ℕ} (h : e.natToVec n = some v) (i : Fin n) :
    v i < e := by
  induction n generalizing e with
  | zero => exact i.elim0
  | succ n ih =>
    cases e with
    | zero => simp [natToVec] at h
    | succ e =>
      simp only [natToVec, Option.map_eq_some_iff] at h
      rcases h with ⟨v, hnv, rfl⟩
      cases i using Fin.cases with
      | zero => simp [Nat.lt_succ_iff, unpair_left_le]
      | succ i =>
        simp only [cons_val_succ]
        exact lt_trans (ih hnv i) (Nat.lt_succ_iff.mpr <| unpair_right_le e)

/--
@isnad1 id=le.1h1v.s4.fb657e1539a7 from=translated src=- shape=b27d46fe vocab=e3b513dd
-/
lemma one_le_of_bodd {n : ℕ} (h : n.bodd = true) : 1 ≤ n :=
by induction n <;> simp  at h ⊢

/--
@isnad1 id=le.2h4v.s4.c491ac46c2dd from=translated src=- shape=47ba7c8b vocab=92a7f352
-/
lemma pair_le_pair_of_le {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁.pair b₁ ≤ a₂.pair b₂ := by
  rcases lt_or_eq_of_le ha with (ha | rfl) <;> rcases lt_or_eq_of_le hb with (hb | rfl)
  { exact le_of_lt (lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb)) }
  { exact le_of_lt (Nat.pair_lt_pair_left b₁ ha) }
  { exact le_of_lt (Nat.pair_lt_pair_right a₁ hb) }
  { rfl }

end Nat

namespace Fin

/--
@isnad1 id=lt.1h2v.s6.23dfe71161a2 from=translated src=- shape=95ed959b vocab=dea0168a
-/
lemma pos_of_coe_ne_zero {i : Fin (n + 1)} (h : (i : ℕ) ≠ 0) :
    0 < i := Nat.pos_of_ne_zero h

/--
@isnad1 id=lt.0h1v.s6.a59530405cef from=translated src=- shape=2a6a86db vocab=fd14ba27
-/
@[simp 1100] lemma one_pos'' : (0 : Fin (n + 2)) < 1 := pos_of_coe_ne_zero (Nat.succ_ne_zero 0)

/--
@isnad1 id=lt.0h1v.s6.60876f173b38 from=translated src=- shape=2a6a86db vocab=fd14ba27
-/
@[simp] lemma two_pos : (0 : Fin (n + 3)) < 2 := pos_of_coe_ne_zero (Nat.succ_ne_zero 1)

/--
@isnad1 id=lt.0h1v.s6.184683151b1e from=translated src=- shape=2a6a86db vocab=fd14ba27
-/
@[simp] lemma three_pos : (0 : Fin (n + 4)) < 3 := pos_of_coe_ne_zero (Nat.succ_ne_zero 2)

/--
@isnad1 id=lt.0h1v.s6.6a3a82994698 from=translated src=- shape=2a6a86db vocab=fd14ba27
-/
@[simp] lemma four_pos : (0 : Fin (n + 5)) < 4 := pos_of_coe_ne_zero (Nat.succ_ne_zero 3)

/--
@isnad1 id=lt.0h1v.s6.b4257672a37d from=translated src=- shape=2a6a86db vocab=fd14ba27
-/
@[simp] lemma five_pos : (0 : Fin (n + 6)) < 5 := pos_of_coe_ne_zero (Nat.succ_ne_zero 4)

end Fin

namespace Fintype
variable {ι : Type _} [Fintype ι]

section «lp_section_4»

variable {α : Type _} [SemilatticeSup α] [OrderBot α]

/-- Imported declaration from the Incompleteness formalization. -/
def sup (f : ι → α) : α := (Finset.univ : Finset ι).sup f

/--
@isnad1 id=le.0h4v.s5.d91f63fb351a from=translated src=- shape=27920fdd vocab=46dc84bf
-/
@[simp] lemma elem_le_sup (f : ι → α) (i : ι) : f i ≤ sup f := Finset.le_sup (by simp)

/--
@isnad1 id=le.1h5v.s5.4cb4ab2c9584 from=translated src=- shape=ae0a9743 vocab=46dc84bf
-/
lemma le_sup {a : α} {f : ι → α} (i : ι) (le : a ≤ f i) : a ≤ sup f := le_trans le (elem_le_sup _ _)

/--
@isnad1 id=iff.0h4v.s5.9d426319b2e1 from=translated src=- shape=75c342ad vocab=46dc84bf
-/
@[simp] lemma sup_le_iff {f : ι → α} {a : α} :
    sup f ≤ a ↔ (∀ i, f i ≤ a) := by simp [sup]

/--
@isnad1 id=eq.0h3v.s5.c8daede0405a from=translated src=- shape=8ecf756b vocab=d1fbd729
-/
@[simp] lemma finsup_eq_0_of_empty [IsEmpty ι] (f : ι → α) : sup f = ⊥ := by simp [sup]

end «lp_section_4»

/-- Imported declaration from the Incompleteness formalization. -/
def decideEqPi {β : ι → Type*} (a b : (i : ι) → β i) (_ : (i : ι) → Decidable (a i = b i)) :
    Decidable (a = b) :=
  decidable_of_iff (∀ i, a i = b i) funext_iff.symm

end Fintype

namespace String

/-- Imported declaration from the Incompleteness formalization. -/
def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

end String

namespace Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)

end Empty

namespace IsEmpty
variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim

end IsEmpty

namespace Function

variable {α : Type u} {β : Type v}

/-- Imported declaration from the Incompleteness formalization. -/
def funEqOn (φ : α → Prop) (f g : α → β) : Prop := ∀ a, φ a → f a = g a

lemma _root_.Function.funEqOn.of_subset {φ ψ : α → Prop} {f g : α → β} (e : funEqOn φ f g) (h :
    ∀ a, ψ a → φ a) :
    funEqOn ψ f g :=
  by intro a ha; exact e a (h a ha)

end Function

namespace Quotient
open Matrix
variable {α : Type u} [s : Setoid α] {β : Sort v}

/--
@isnad1 id=var.0h5v.s5.f826a449c001 from=translated src=- shape=509953a7 vocab=53f0ba4d
-/
@[elab_as_elim]
lemma inductionOnVec {φ : (Fin n → Quotient s) → Prop} (v : Fin n → Quotient s)
  (h : ∀ v : Fin n → α, φ (fun i => Quotient.mk s (v i))) : φ v :=
  Quotient.induction_on_pi v h

/-- Imported declaration from the Incompleteness formalization. -/
def liftVec : ∀ {n} (f : (Fin n → α) → β),
  (∀ v₁ v₂ : Fin n → α, (∀ n, v₁ n ≈ v₂ n) → f v₁ = f v₂) → (Fin n → Quotient s) → β
| 0,     f, _, _ => f ![]
| n + 1, f, h, v =>
  let ih : α → (Fin n → Quotient s) → β :=
    fun a v => liftVec (n := n) (fun v => f (a :> v))
      (fun v₁ v₂ hv => h (a :> v₁) (a :> v₂) (Fin.cases (by simpa using refl a) hv)) v
  Quot.liftOn (vecHead v) (ih · (vecTail v))
    (fun a b hab => by
      have : ∀ v, f (a :> v) = f (b :> v) :=
        fun v ↦ h _ _ (Fin.cases hab (by simpa using fun x ↦ refl _))
      simp [this, ih])

/--
@isnad1 id=eq.1h4v.s6.4a62c2c08386 from=translated src=- shape=04d7b02b vocab=8cbfed83
-/
@[simp] lemma liftVec_zero (f : (Fin 0 → α) → β) (h) (v : Fin 0 → Quotient s) :
    liftVec f h v = f ![] :=
  rfl

/--
@isnad1 id=eq.1h5v.s6.30912289f621 from=translated src=- shape=f01d7f65 vocab=8ae9ceb8
-/
lemma liftVec_mk {n} (f : (Fin n → α) → β) (h) (v : Fin n → α) :
    liftVec f h (Quotient.mk s ∘ v) = f v := by
  induction n with
  | zero => simp [liftVec, empty_eq]
  | succ n ih =>
    simp [liftVec]
    simpa [Function.comp_def, Matrix.vecHead, Matrix.vecTail, Quotient.liftOn_mk] using
      ih (fun v' => f (vecHead v :> v'))
        (fun v₁ v₂ hv => h (vecHead v :> v₁) (vecHead v :> v₂) (Fin.cases (refl _) hv)) (vecTail v)

/--
@isnad1 id=eq.1h4v.s6.8d0e5ee16bd8 from=translated src=- shape=f7d99864 vocab=95344d57
-/
@[simp] lemma liftVec_mk₁ (f : (Fin 1 → α) → β) (h) (a : α) :
    liftVec f h ![Quotient.mk s a] = f ![a] := liftVec_mk f h ![a]

/--
@isnad1 id=eq.1h5v.s7.569d7d30a949 from=translated src=- shape=7f69ef87 vocab=95344d57
-/
@[simp] lemma liftVec_mk₂ (f : (Fin 2 → α) → β) (h) (a₁ a₂ : α) :
    liftVec f h ![Quotient.mk s a₁, Quotient.mk s a₂] = f ![a₁, a₂] := liftVec_mk f h ![a₁, a₂]

end Quotient

namespace List

variable {α : Type u} {β : Type v}

/--
@isnad1 id=eq.1h4v.s5.21f794178540 from=translated src=- shape=f96ba74e vocab=16c63f88
-/
lemma getI_map_range [Inhabited α] (f : ℕ → α) (h : i < n) :
    ((List.range n).map f).getI i = f i := by
  simpa [h] using List.getI_eq_getElem ((List.range n).map f) (n := i) (by simpa using h)

/-- Imported declaration from the Incompleteness formalization. -/
def subsetSet (l : List α) (s : Set α) [DecidablePred s] : Bool :=
  l.foldr (fun a ih => s a && ih) true

/-- Imported declaration from the Incompleteness formalization. -/
def upper : List ℕ → ℕ
  | []      => 0
  | n :: ns => max (n + 1) ns.upper

/--
@isnad1 id=eq.0h0v.s3.52cccfb34b75 from=translated src=- shape=c15d4c7a vocab=8b5b6f6c
-/
@[simp] lemma upper_nil : upper [] = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.45485d0270c2 from=translated src=- shape=692a6db9 vocab=bea65686
-/
@[simp] lemma upper_cons (n : ℕ) (ns : List ℕ) : upper (n :: ns) = max (n + 1) ns.upper := rfl

/--
@isnad1 id=lt.1h2v.s4.14f0ad77b403 from=translated src=- shape=b2bb38c8 vocab=b8ec61ea
-/
lemma lt_upper (l : List ℕ) {n} (h : n ∈ l) : n < l.upper := by
  induction l with
  | nil => simp at h
  | cons m ns ih =>
    suffices n < m + 1 ∨ n < ns.upper by simpa
    rcases show n = m ∨ n ∈ ns by simpa using h with (rfl | h)
    · exact Or.inl (Nat.lt_succ_self _)
    · exact Or.inr (ih h)

section «lp_section_5»

variable [DecidableEq α] [DecidableEq β]

/--
@isnad1 id=eq.0h4v.s5.3131e56840fc from=translated src=- shape=eaed807b vocab=fbfd4fa2
-/
lemma toFinset_map {f : α → β} (l : List α) : (l.map f).toFinset = Finset.image f l.toFinset := by
  induction l <;> simp [*]

/--
@isnad1 id=le.1h3v.s5.9f18491bf032 from=translated src=- shape=c597b56f vocab=5a390b70
-/
lemma toFinset_mono {l l' : List α} (h : l ⊆ l') : l.toFinset ⊆ l'.toFinset :=
  fun _ ha => mem_toFinset.mpr (h (mem_toFinset.mp ha))

end «lp_section_5»

section «lp_section_6»

variable [SemilatticeSup α] [OrderBot α]

/-- Imported declaration from the Incompleteness formalization. -/
def sup : List α → α
  |      [] => ⊥
  | a :: as => a ⊔ as.sup

/--
@isnad1 id=eq.0h1v.s5.c567649caf88 from=translated src=- shape=691bf2e9 vocab=42b1b50c
-/
@[simp] lemma sup_nil : ([] : List α).sup = ⊥ := rfl

/--
@isnad1 id=eq.0h3v.s5.ebb1c9edcca5 from=translated src=- shape=96afa169 vocab=48040b37
-/
@[simp] lemma sup_cons (a : α) (as : List α) : (a :: as).sup = a ⊔ as.sup := rfl

/--
@isnad1 id=le.1h3v.s5.7e8e94ea0cf1 from=translated src=- shape=518df509 vocab=ce6a36e0
-/
lemma le_sup {a} {l : List α} : a ∈ l → a ≤ l.sup := by
  induction l with
  | nil => simp
  | cons b l ih =>
    intro h
    rcases show a = b ∨ a ∈ l by simpa using h with (rfl | h)
    · simp
    · exact le_sup_of_le_right (ih h)

/--
@isnad1 id=eq.0h3v.s5.65c371cdc234 from=translated src=- shape=e18182b0 vocab=574c936a
-/
lemma sup_ofFn (f : Fin n → α) : (ofFn f).sup = Finset.sup Finset.univ f := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ) := by
      ext i; simp
    have h₂ : Finset.sup Finset.univ (fun i ↦ f (Fin.succ i)) = Finset.sup {0}ᶜ f := by
      simpa [Function.comp_def] using Eq.symm <|
          Finset.sup_image (Finset.univ : Finset (Fin n)) Fin.succ f
    calc
      (ofFn f).sup = (f 0 ⊔ Finset.univ.sup fun i : Fin _ ↦ f i.succ) := by simp [ih]
      _            = f 0 ⊔ Finset.sup {0}ᶜ f                          := by rw [h₂]
      _            = Finset.univ.sup f                                := by
        rw [h₁, Finset.sup_insert]; simp

end «lp_section_6»

/--
@isnad1 id=eq.1h5v.s5.6f23577444bb from=translated src=- shape=239189f6 vocab=74862934
-/
lemma ofFn_get_eq_map_cast {n} (g : α → β) (as : List α) {h} :
    ofFn (fun i => g (as.get (i.cast h)) : Fin n → β) = as.map g := by
  simp_all

variable {m : Type _ → Type _} {α : Type _} {β : Type _} [Monad m]

/--
@isnad1 id=subset.1h4v.s5.7a37ad23ea68 from=translated src=- shape=3976eef2 vocab=9b06306b
-/
lemma append_subset_append {l₁ l₂ l : List α} (h : l₁ ⊆ l₂) : l₁ ++ l ⊆ l₂ ++ l :=
  List.append_subset.mpr ⟨List.subset_append_of_subset_left _ h, subset_append_right l₂ l⟩

/--
@isnad1 id=subset.1h3v.s4.756a2166eacc from=translated src=- shape=a106a43a vocab=0b846caf
-/
lemma subset_of_eq {l₁ l₂ : List α} (e : l₁ = l₂) : l₁ ⊆ l₂ := by simp [e]

section «lp_section_7»

/-- Imported declaration from the Incompleteness formalization. -/
def remove [DecidableEq α] (a : α) : List α → List α := List.filter (· ≠ a)

variable [DecidableEq α]

/--
@isnad1 id=eq.0h2v.s4.c775bfe01230 from=translated src=- shape=1b0d3146 vocab=c162c494
-/
@[simp]
lemma remove_nil (a : α) : [].remove a = [] := by simp [List.remove]

@[simp 1100]
lemma eq_remove_cons {l : List α} :
    (ψ :: l).remove ψ = l.remove ψ := by
  induction l <;> simp_all [List.remove];

/--
@isnad1 id=eq.1h3v.s4.61d85a1b4a7e from=translated src=- shape=211dde5e vocab=214f060a
-/
@[simp]
lemma remove_singleton_of_ne {φ ψ : α} (h : φ ≠ ψ) :
    [φ].remove ψ = [φ] := by simp_all [List.remove]

/--
@isnad1 id=iff.0h4v.s5.cf11fb0bb9eb from=translated src=- shape=3c9b98ac vocab=d84002bc
-/
lemma mem_remove_iff {l : List α} : b ∈ l.remove a ↔ b ∈ l ∧ b ≠ a := by simp [List.remove]

/--
@isnad1 id=mem.1h4v.s5.ba8e8aba8a0b from=translated src=- shape=9b5ab587 vocab=d84002bc
-/
lemma mem_of_mem_remove {a b : α} {l : List α} (h : b ∈ l.remove a) : b ∈ l :=
  (mem_remove_iff.mp h).1

/--
@isnad1 id=eq.0h3v.s4.1260c6b0723e from=translated src=- shape=2f56b9d6 vocab=42c6e35f
-/
lemma remove_cons_self (l : List α) (a) :
  (a :: l).remove a = l.remove a := by simp [remove]

/--
@isnad1 id=eq.1h4v.s5.69778a399cb2 from=translated src=- shape=7073d6d6 vocab=42c6e35f
-/
lemma remove_cons_of_ne (l : List α) {a b} (ne : a ≠ b) :
  (a :: l).remove b = a :: l.remove b := by simp_all [remove];

/--
@isnad1 id=subset.0h3v.s4.afb13218e3a4 from=translated src=- shape=c2c1051c vocab=8d28d94a
-/
lemma remove_subset (a) (l : List α) :
    l.remove a ⊆ l := fun _ h => (mem_remove_iff.mp h).1

/--
@isnad1 id=subset.1h4v.s5.299799ba13f1 from=translated src=- shape=88bb954d vocab=8d28d94a
-/
lemma remove_subset_remove (a) {l₁ l₂ : List α} (h : l₁ ⊆ l₂) :
    l₁.remove a ⊆ l₂.remove a := by
  simp only [subset_def, mem_remove_iff, ne_eq, and_imp]
  intros
  simpa [*] using h (by assumption)

/--
@isnad1 id=subset.0h4v.s5.b8c961fd809f from=translated src=- shape=9314444b vocab=aafbbd13
-/
lemma remove_cons_subset_cons_remove (a b) (l : List α) :
    (a :: l).remove b ⊆ a :: l.remove b := by
  intro x
  simp only [mem_remove_iff, mem_cons, ne_eq, and_imp]
  rintro (rfl | hx) nex <;> simp [*]

/--
@isnad1 id=subset.0h5v.s5.62afef0600b5 from=translated src=- shape=dbf53f4c vocab=1a24ce1a
-/
lemma remove_map_substet_map_remove [DecidableEq β] (f : α → β) (l : List α) (a) :
    (l.map f).remove (f a) ⊆ (l.remove a).map f := by
  simp only [subset_def, mem_remove_iff, mem_map, ne_eq, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂]
  intro b hb neb;
  exact ⟨b, ⟨hb, by rintro rfl; exact neb rfl⟩, rfl⟩

end «lp_section_7»

/--
@isnad1 id=var.0h6v.s5.f03642bce4bf from=translated src=- shape=ab4d0173 vocab=53cff65c
-/
@[elab_as_elim]
lemma induction_with_singleton
  {motive : List F → Prop}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a as, as ≠ [] → motive as → motive (a :: as)) : ∀ as, motive as := by
  intro as;
  induction as with
  | nil => exact hnil;
  | cons a as ih => cases as with
    | nil => exact hsingle a;
    | cons b bs => exact hcons a (b :: bs) (by simp) ih;

end List

namespace List
namespace Vector

variable {α : Type*}

/--
@isnad1 id=eq.1h4v.s5.28bcf14d9cc9 from=translated src=- shape=e2ef3393 vocab=64a9977a
-/
lemma get_mk_eq_get {n} (l : List α) (h : l.length = n) (i : Fin n) : List.Vector.get (⟨l, h⟩ :
    List.Vector α n) i = l.get (i.cast h.symm) :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.0975d3587e28 from=translated src=- shape=04cc8713 vocab=29299ee7
-/
lemma get_one {α : Type*} {n} (v : Vector α (n + 2)) : v.get 1 = v.tail.head := by
  simpa [Vector.get_zero] using (Vector.get_tail_succ v 0).symm

/--
@isnad1 id=eq.0h4v.s5.31906f08aaf7 from=translated src=- shape=06f9ffc4 vocab=ea2550b8
-/
lemma ofFn_vecCons (a : α) (v : Fin n → α) :
    ofFn (a :> v) = a ::ᵥ ofFn v := by
  ext i; cases i using Fin.cases <;> simp

end Vector
end List

namespace Finset

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def rangeOfFinite {ι : Sort v} [Finite ι] (f : ι → α) : Finset α :=
  Set.Finite.toFinset (s := Set.range f) (Set.finite_range f)

/--
@isnad1 id=iff.0h4v.s5.380ceb9d5ebc from=translated src=- shape=14c036ca vocab=f0ee551a
-/
lemma mem_rangeOfFinite_iff {ι : Sort v} [Finite ι] {f : ι → α} {a : α} :
    a ∈ rangeOfFinite f ↔ ∃ i : ι, f i = a := by simp [rangeOfFinite]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def imageOfFinset [DecidableEq β] (s : Finset α) (f : (a : α) → a ∈ s → β) :
    Finset β :=
  Finset.biUnion s (rangeOfFinite <| f ·)

/--
@isnad1 id=iff.0h5v.s6.abebcf4b9478 from=translated src=- shape=f9595e5b vocab=6a539716
-/
lemma mem_imageOfFinset_iff [DecidableEq β] {s : Finset α} {f : (a : α) → a ∈ s → β} {b : β} :
    b ∈ imageOfFinset s f ↔ ∃ (a : α) (ha : a ∈ s), f a ha = b := by
  simp [imageOfFinset, mem_rangeOfFinite_iff]

/--
@isnad1 id=mem.1h5v.s5.73c25e96e925 from=translated src=- shape=1d231285 vocab=6a539716
-/
@[simp] lemma mem_imageOfFinset [DecidableEq β] {s : Finset α} (f : (a : α) → a ∈ s → β) (a :
    α) (ha :
    a ∈ s) :
    f a ha ∈ imageOfFinset s f := by simpa [mem_imageOfFinset_iff] using ⟨a, ha, rfl⟩

/--
@isnad1 id=eq.0h4v.s5.3a6330374906 from=translated src=- shape=f74db4b3 vocab=db19d44c
-/
lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} :
  (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp [and_or_left]

/--
@isnad1 id=eq.0h3v.s5.ac8c66c0280d from=translated src=- shape=dc31e7df vocab=c2c23ed7
-/
@[simp 1100] lemma equiv_univ {α α'} [Fintype α] [Fintype α'] [DecidableEq α'] (e : α ≃ α') :
    (Finset.univ : Finset α).image e = Finset.univ := by ext x; simp

/--
@isnad1 id=eq.0h5v.s6.73e463b2ab91 from=translated src=- shape=d40dca5c vocab=4630598a
-/
@[simp] lemma sup_univ_equiv
    {α α'} [Fintype α] [Fintype α'] [SemilatticeSup β] [OrderBot β] (f :
    α → β) (e :
    α' ≃ α) :
    Finset.sup Finset.univ (fun i => f (e i)) = Finset.sup Finset.univ f := by
  classical
  simpa [Function.comp_def] using Eq.symm <| Finset.sup_image Finset.univ e f

/--
@isnad1 id=eq.1h4v.s6.9541e8bb253c from=translated src=- shape=99fee274 vocab=db6ecf12
-/
lemma sup_univ_cast {α : Type _} [SemilatticeSup α] [OrderBot α] {n} (f : Fin n → α) (n') {h :
    n' = n} :
    Finset.sup Finset.univ (fun (i : Fin n') =>
      f (i.cast h)) = Finset.sup Finset.univ f := by rcases h with rfl; simp

end Finset

namespace Denumerable

/--
@isnad1 id=lt.1h2v.s4.c40d5f28ddde from=translated src=- shape=e6eb1a25 vocab=0fc718e6
-/
lemma lt_of_mem_list : ∀ n i, i ∈ Denumerable.ofNat (List ℕ) n → i < n
  |     0 => by simp
  | n + 1 => by
    have : n.unpair.2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    suffices (Nat.unpair n).1 < n + 1 ∧ ∀ a ∈ ofNat (List ℕ) (Nat.unpair n).2, a < n + 1 by simpa
    constructor
    · exact Nat.lt_succ_of_le (Nat.unpair_left_le n)
    · intro i hi
      have : i < n.unpair.2 := lt_of_mem_list n.unpair.2 i hi
      exact lt_trans this (Nat.lt_succ_of_le <| Nat.unpair_right_le n)

end Denumerable

namespace Part

/--
@isnad1 id=iff.0h4v.s5.762e77de95b0 from=translated src=- shape=fb946f3c vocab=4f845458
-/
@[simp] lemma mem_vector_mOfFn : ∀ {n : ℕ} {w : List.Vector α n} {v : Fin n →. α},
    w ∈ List.Vector.mOfFn v ↔ ∀ i, w.get i ∈ v i
  |     0, _, _ => by simp [List.Vector.mOfFn, List.Vector.eq_nil]
  | n + 1, w, v => by
    suffices (∃ a ∈ v 0, ∃ u, (∀ (i : Fin n), u.get i ∈ v i.succ) ∧ w = a ::ᵥ u) ↔
      ∀ (i : Fin (n + 1)), w.get i ∈ v i by
      simpa [List.Vector.mOfFn, mem_vector_mOfFn (n := n) (v := fun i => v i.succ)]
    constructor
    · rintro ⟨a, ha, v, hv, rfl⟩ i; cases i using Fin.cases <;> simp [ha, hv]
    · intro h
      have hhead : w.head ∈ v 0 := by
        rw [←List.Vector.get_zero w]
        exact h 0
      refine ⟨w.head, hhead, w.tail, ?_, (List.Vector.cons_head_tail w).symm⟩
      intro i
      have htail : w.tail.get i = w.get i.succ := List.Vector.get_tail_succ w i
      exact htail.symm ▸ h i.succ

end Part

namespace Set

variable {α : Type*}

/--
@isnad1 id=ex.4h3v.s6.9c3982adbacf from=translated src=- shape=17e57dd3 vocab=f0cec1b7
-/
lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain :
    IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on s hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by
          have : (∃ t ∈ c, a ∈ t) ∧ s ⊆ ⋃₀ c := by simpa [Set.insert_subset_iff] using h
          exact this.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)

end Set

/-- Imported declaration from the Incompleteness formalization. -/
class Exp (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  exp : α → α
export Exp (exp)

/-- Class for `α` has at least `n` elements -/
class Atleast (n : ℕ+) (α) where
  mapping : ∃ f : Fin n → α, Function.HasLeftInverse f
