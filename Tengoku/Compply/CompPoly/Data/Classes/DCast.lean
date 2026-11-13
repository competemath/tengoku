/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Tengoku.Seed.Data.Fin.Basic
public import Tengoku.Seed.Tactic.DepRewrite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Dependent casts

This file contains type classes for dependent or custom cast operations

This allows us to state theorems with more refined casts, without which we cannot make progress in
proving them -/

@[expose] public section
namespace Tengoku.Compply end Tengoku.Compply open Tengoku.Compply 
universe u v w

section Prelude

-- Some missing theorems about `cast` and `congrArg`

/--
@isnad1 id=iff.2h5v.s5.c0a4eb8cc570 from=translated src=- shape=3776f1b6 vocab=a550bca0
-/
theorem _root_.Tengoku.Compply.cast_eq_cast_iff {α β γ : Sort u} {h : α = γ} {h' : β = γ} {a : α} {b : β} :
    cast h a = cast h' b ↔ a = cast (h'.trans h.symm) b := by cases h'; cases h; simp

/--
@isnad1 id=iff.1h4v.s4.07bd93ec1a58 from=translated src=- shape=9825eedc vocab=830205cc
-/
theorem _root_.Tengoku.Compply.cast_symm {α β : Sort u} {h : α = β} {a : α} {b : β} :
    cast h a = b ↔ a = cast h.symm b := by
  cases h; simp

end Prelude

/-- `DCast` is a type class for custom cast operations on an indexed type family `β a`

We require the cast operation `dcast`, along with the property that `dcast` reduces to `id` under
reflexivity.-/
class _root_.Tengoku.Compply.DCast (α : Sort*) (β : α → Sort*) where
  dcast : ∀ {a a' : α}, a = a' → β a → β a'
  dcast_id : ∀ {a : α}, dcast (Eq.refl a) = id

export DCast (dcast dcast_id)
attribute [simp] dcast_id

section DCast

variable {α : Sort*} {β : α → Sort*} [DCast α β] {a a' a'' : α} {b : β a} {b' : β a'}

/-- The default instance for `DCast`-/
instance (priority := low) : DCast α β where
  dcast h := cast (congrArg β h)
  dcast_id := by intro a; funext b; simp only [cast_eq, id_eq]

/--
@isnad1 id=eq.0h4v.s4.13d0db850506 from=translated src=- shape=a14ce85c vocab=07290b4c
-/
@[simp]
theorem _root_.Tengoku.Compply.dcast_eq : dcast (Eq.refl a) b = b := by
  simp

/--
@isnad1 id=eq.2h6v.s5.b110ad7cc0b8 from=translated src=- shape=8f7c2dfe vocab=1ae34964
-/
theorem _root_.Tengoku.Compply.dcast_symm (ha : a = a') (hb : dcast ha b = b') : dcast (ha.symm) b' = b := by
  cases ha; cases hb; simp

/--
@isnad1 id=eq.2h6v.s5.5856e9c18fb4 from=translated src=- shape=52e3df37 vocab=9d003c66
-/
@[simp]
theorem _root_.Tengoku.Compply.dcast_trans (h : a = a') (h' : a' = a'') :
    dcast h' (dcast h b) = dcast (h.trans h') b := by
  cases h; cases h'; simp

/--
@isnad1 id=iff.2h7v.s6.b776375298fe from=translated src=- shape=2d30f242 vocab=47519c05
-/
theorem _root_.Tengoku.Compply.dcast_eq_dcast_iff (h : a = a'') (h' : a' = a'') :
    dcast h b = dcast h' b' ↔ b = dcast (h'.trans h.symm) b' := by
  cases h; cases h'; simp

/--
@isnad1 id=heq.2h6v.s5.40be919285ec from=translated src=- shape=a2320859 vocab=f97a86f4
-/
theorem _root_.Tengoku.Compply.heq_of_dcast (ha : a = a') (hb : dcast ha b = b') : HEq b b' := by
  cases ha; cases hb; simp

/--
@isnad1 id=eq.0h6v.s6.d3df2dabe48e from=translated src=- shape=3e534c16 vocab=2e6265f6
-/
theorem _root_.Tengoku.Compply.dcast_fun {γ : (a : α) → β a → Sort*} {f : (b : β a) → γ a b} :
    f (dcast rfl b) = dcast (α := β a) (β := γ a) dcast_eq.symm (f b) := by
  rw! [dcast_eq]
  exact dcast_eq.symm

-- TODO: figure out the most general form of these composition / naturality theorems

/--
@isnad1 id=eq.1h5v.s5.91945dacb171 from=translated src=- shape=5eeb73e0 vocab=a1e909d7
-/
theorem _root_.Tengoku.Compply.dcast_eq_root_cast (h : a = a') : dcast h b = _root_.cast (congrArg β h) b := by
  cases h; simp

end DCast

/-- `DCast₂` is a type class for custom cast operations on a doubly-indexed type family `γ a b`,
  given an underlying dependent cast `DCast α β`

We require the cast operation `dcast₂`, along with the property that `dcast₂` reduces to `id` under
reflexivity.-/
class _root_.Tengoku.Compply.DCast₂ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*) [DCast α β] where
  dcast₂ : ∀ {a a' : α} {b : β a} {b' : β a'},
    (ha : a = a') → (dcast ha b = b') → γ a b → γ a' b'
  dcast₂_id : ∀ {a : α} {b : β a}, dcast₂ (Eq.refl a) dcast_eq = (id : γ a b → γ a b)

export DCast₂ (dcast₂ dcast₂_id)
attribute [simp] dcast₂_id

section DCast₂

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*} [DCast α β] [DCast₂ α β γ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''} {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}

/-- Default instance for `DCast₂`-/
instance (priority := low) : DCast₂ α β γ where
  dcast₂ ha hb c := by
    refine cast ?_ c
    cases ha; simp at hb; cases hb; rfl
  dcast₂_id := by intros; rfl

/--
@isnad1 id=eq.0h6v.s5.2ef22e35f724 from=translated src=- shape=e1c3d0f9 vocab=42061355
-/
@[simp]
theorem _root_.Tengoku.Compply.dcast₂_eq : dcast₂ (Eq.refl a) dcast_eq c = c := by
  simp

/--
@isnad1 id=eq.2h6v.s6.4cf53d053c1c from=translated src=- shape=7709cd7c vocab=8b486a58
-/
@[simp]
theorem _root_.Tengoku.Compply.dcast₂_eq' (h : a = a) (h' : dcast h b = b) : dcast₂ h h' c = c := by
  cases h; simp

/--
@isnad1 id=eq.4h10v.s7.6c77ba05bd08 from=translated src=- shape=f1de7054 vocab=88d5e85a
-/
@[simp]
theorem _root_.Tengoku.Compply.dcast₂_trans (ha : a = a') (ha' : a' = a'')
    (hb : dcast ha b = b') (hb' : dcast ha' b' = b'') :
      dcast₂ ha' hb' (dcast₂ ha hb c) = dcast₂ (ha.trans ha') (by simp [← hb', ← hb]) c := by
  cases ha; simp at hb; cases hb; simp

instance _root_.Tengoku.Compply.instDCast₁₂ : DCast (β a) (γ a) where
  dcast hb c := dcast₂ (Eq.refl a) (by simp [hb]) c
  dcast_id := by intros; ext c; exact dcast₂_eq

instance _root_.Tengoku.Compply.instDCastPSigma : DCast ((a : α) ×' β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (by cases hab; simp) (by cases hab; simp) c
  dcast_id := by intros; ext c; simp

instance _root_.Tengoku.Compply.instDCastSigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    [DCast α β] [DCast₂ α β γ] : DCast ((a : α) × β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (by cases hab; simp) (by cases hab; simp) c
  dcast_id := by intros; ext c; simp

instance _root_.Tengoku.Compply.instDCastForall : DCast α (fun a => ∀ b : β a, γ a b) where
  dcast ha f := fun b => dcast₂ ha ((dcast_trans ha.symm ha).trans dcast_eq) (f (dcast ha.symm b))
  dcast_id := by
    intros a; funext f; funext b
    simp only [id_eq]
    rw! [dcast_eq]
    simp

end DCast₂

/-- `DCast₃` is a type class for custom cast operations on a triply-indexed type family `δ a b c`,
  given underlying dependent casts `DCast α β` and `DCast₂ α β γ`

We require the cast operation `dcast₃`, along with the property that `dcast₃` reduces to `id` under
reflexivity.-/
class _root_.Tengoku.Compply.DCast₃ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*)
    (δ : (a : α) → (b : β a) → γ a b → Sort*) [DCast α β] [DCast₂ α β γ] where
  dcast₃ : ∀ {a a' : α} {b : β a} {b' : β a'} {c : γ a b} {c' : γ a' b'},
    (ha : a = a') → (hb : dcast ha b = b') → (hc : dcast₂ ha hb c = c') → δ a b c → δ a' b' c'
  dcast₃_id : ∀ {a : α} {b : β a} {c : γ a b},
    dcast₃ (Eq.refl a) dcast_eq dcast₂_eq = (id : δ a b c → δ a b c)

export DCast₃ (dcast₃ dcast₃_id)
attribute [simp] dcast₃_id

section DCast₃

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*}
  {δ : (a : α) → (b : β a) → γ a b → Sort*}
  [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''}
  {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}
  {d : δ a b c} {d' : δ a' b' c'} {d'' : δ a'' b'' c''}

/-- Default instance for `DCast₃`-/
instance (priority := low) : DCast₃ α β γ δ where
  dcast₃ ha hb hc d := by
    refine cast ?_ d
    cases ha; simp at hb; cases hb; simp at hc; cases hc; rfl
  dcast₃_id := by intros; rfl

/--
@isnad1 id=eq.0h8v.s6.734f9b892218 from=translated src=- shape=bc2787b3 vocab=fcd4b9cc
-/
@[simp]
theorem _root_.Tengoku.Compply.dcast₃_eq : dcast₃ (Eq.refl a) dcast_eq dcast₂_eq d = d := by
  simp

/--
@isnad1 id=eq.6h14v.s7.0495cd7737cf from=translated src=- shape=e9f18aef vocab=5d8a5156
-/
@[simp]
theorem _root_.Tengoku.Compply.dcast₃_trans (ha : a = a') (ha' : a' = a'')
    (hb : dcast ha b = b') (hb' : dcast ha' b' = b'')
    (hc : dcast₂ ha hb c = c') (hc' : dcast₂ ha' hb' c' = c'') :
    dcast₃ ha' hb' hc' (dcast₃ ha hb hc d) =
    dcast₃ (ha.trans ha') (by simp [← hb', ← hb]) (by simp [← hc', ← hc]) d := by
  cases ha; simp at hb; cases hb; simp at hc; cases hc; simp

instance _root_.Tengoku.Compply.instDCast₂₃ {a : α} : DCast₂ (β a) (γ a) (δ a) where
  dcast₂ ha hb c := dcast₃ (Eq.refl a) (by cases ha; simp) (by cases ha; cases hb; simp) c
  dcast₂_id := by intros; funext; simp

instance _root_.Tengoku.Compply.instDCast₁₃ {a : α} {b : β a} : DCast (γ a b) (δ a b) where
  dcast hc d := dcast₃ (Eq.refl a) dcast_eq (by cases hc; simp) d
  dcast_id := by intros; ext; simp

instance _root_.Tengoku.Compply.instDCast₂PSigma : DCast₂ ((a : α) ×' β a) (fun a => γ a.1 a.2) (fun a => δ a.1 a.2)
    where
  dcast₂ ha hb c := dcast₃ (by cases ha; simp) (by cases ha; simp) (by cases ha; cases hb; simp) c
  dcast₂_id := by intros; funext; simp

instance _root_.Tengoku.Compply.instDCast₂Sigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast₂ ((a : α) × β a) (fun a => γ a.1 a.2) (fun a => δ a.1 a.2) where
  dcast₂ ha hb c := dcast₃ (by cases ha; simp) (by cases ha; simp) (by cases ha; cases hb; simp) c
  dcast₂_id := by intros; funext; simp

instance _root_.Tengoku.Compply.instDCast₂Forall :
    DCast₂ α (fun a => ∀ b : β a, γ a b) (fun a f => ∀ b : β a, δ a b (f b)) where
  dcast₂ ha hb c := fun b => dcast₃ ha (by simp)
    (by cases ha; cases hb; rw! [dcast_eq]; simp) (c (dcast ha.symm b))
  dcast₂_id := by intros; funext; simp; rw! [dcast_eq]; simp

instance _root_.Tengoku.Compply.instDCastPSigmaPSigma :
    DCast ((a : α) ×' (b : β a) ×' γ a b) (fun a => δ a.1 a.2.1 a.2.2) where
  dcast hc d := dcast₃ (by cases hc; simp) (by cases hc; simp) (by cases hc; simp) d
  dcast_id := by intros; ext; simp

instance _root_.Tengoku.Compply.instDCastSigmaSigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast ((a : α) × (b : β a) × γ a b) (fun a => δ a.1 a.2.1 a.2.2) where
  dcast hc d := dcast₃ (by cases hc; simp) (by cases hc; simp) (by cases hc; simp) d
  dcast_id := by intros; ext; simp

instance _root_.Tengoku.Compply.instDCastForallForall :
    DCast α (fun a => ∀ b : β a, ∀ c : γ a b, δ a b c) where
  dcast ha d := fun b c => dcast₃ ha (by cases ha; simp) (by cases ha; simp)
    (d (dcast ha.symm b) (dcast₂ ha.symm rfl c))
  dcast_id := by intros; funext; simp; rw! [dcast_eq]; rw! [dcast₂_eq]; simp

instance _root_.Tengoku.Compply.instDCastPSigmaForall :
    DCast ((a : α) ×' (β a)) (fun ab => ∀ c : γ ab.1 ab.2, δ ab.1 ab.2 c) where
  dcast hab d := fun c => dcast₃ (by cases hab; simp) (by cases hab; simp) (by cases hab; simp)
    (d (dcast₂ (by cases hab; simp) (by cases hab; simp) c))
  dcast_id := by intros; funext; simp; rw! [dcast₂_eq]; simp

instance _root_.Tengoku.Compply.instDCastSigmaForallForall {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast ((a : α) × (β a)) (fun ab => ∀ c : γ ab.1 ab.2, δ ab.1 ab.2 c) where
  dcast hab d := fun c => dcast₃ (by cases hab; simp) (by cases hab; simp) (by cases hab; simp)
    (d (dcast₂ (by cases hab; simp) (by cases hab; simp) c))
  dcast_id := by intros; funext; simp; rw! [dcast₂_eq]; simp

end DCast₃

namespace Fin

/-- `Fin.cast` as a `DCast` (which should override the default instance).-/
instance instDCast : DCast Nat Fin where
  dcast h := Fin.cast h
  dcast_id := by simp only [Fin.cast_refl, implies_true]

end Fin
-- Tengoku: root names of this library moved to Tengoku.Compply so they do not collide with other libraries (generated)
