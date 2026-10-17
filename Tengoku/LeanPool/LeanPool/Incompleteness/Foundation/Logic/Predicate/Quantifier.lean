/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
public import Tengoku

/-! # Quantifier -/

@[expose] public section

namespace LO

/-- Imported declaration from the Incompleteness formalization. -/
class SigmaSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  sigma : α

/-- Imported declaration from the Incompleteness formalization. -/
class PiSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pi : α

/-- Imported declaration from the Incompleteness formalization. -/
class DeltaSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  delta : α

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "Sg" => SigmaSymbol.sigma

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "Pg" => PiSymbol.pi

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "Dlt" => DeltaSymbol.delta

attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta

/-- Imported declaration from the Incompleteness formalization. -/
inductive Polarity where
  | sigma
  | pi

namespace Polarity

instance : SigmaSymbol Polarity := ⟨sigma⟩

instance : PiSymbol Polarity := ⟨pi⟩

/-- Imported declaration from the Incompleteness formalization. -/
def alt : Polarity → Polarity
  | Sg => Pg
  | Pg => Sg

lemma eq_sigma : sigma = Sg := rfl

lemma eq_pi : pi = Pg := rfl

/--
@isnad1 id=eq.0h0v.s3.bd2652ed0a84 from=translated src=- shape=dce07c30 vocab=55be10ff
-/
@[simp] lemma alt_sigma : alt Sg = Pg := rfl

/--
@isnad1 id=eq.0h0v.s3.5a41b408049f from=translated src=- shape=dce07c30 vocab=55be10ff
-/
@[simp] lemma alt_pi : alt Pg = Sg := rfl

/--
@isnad1 id=eq.0h1v.s3.0d4784247498 from=translated src=- shape=47dcad53 vocab=8b41e959
-/
@[simp] lemma alt_alt (Γ : Polarity) : Γ.alt.alt = Γ := by rcases Γ <;> rfl

end Polarity

/-- Imported declaration from the Incompleteness formalization. -/
inductive SigmaPiDelta where | sigma | pi | delta

namespace SigmaPiDelta

instance : SigmaSymbol SigmaPiDelta := ⟨sigma⟩

instance : PiSymbol SigmaPiDelta := ⟨pi⟩

instance : DeltaSymbol SigmaPiDelta := ⟨delta⟩

/-- Imported declaration from the Incompleteness formalization. -/
def alt : SigmaPiDelta → SigmaPiDelta
  | Sg => Pg
  | Pg => Sg
  | Dlt => Dlt

lemma eq_sigma : sigma = Sg := rfl

lemma eq_pi : pi = Pg := rfl

lemma eq_delta : delta = Dlt := rfl

/--
@isnad1 id=eq.0h0v.s3.0c5580e8977f from=translated src=- shape=dce07c30 vocab=5c721ec8
-/
@[simp] lemma alt_sigma : alt Sg = Pg := rfl

/--
@isnad1 id=eq.0h0v.s3.196db632fcbe from=translated src=- shape=dce07c30 vocab=5c721ec8
-/
@[simp] lemma alt_pi : alt Pg = Sg := rfl

/--
@isnad1 id=eq.0h0v.s3.691c6dfefbbd from=translated src=- shape=dce07c30 vocab=f0b87a45
-/
@[simp] lemma alt_delta : alt Dlt = Dlt := rfl

/--
@isnad1 id=eq.0h1v.s3.53a62a4225ed from=translated src=- shape=47dcad53 vocab=f1209912
-/
@[simp] lemma alt_alt (Γ : SigmaPiDelta) : Γ.alt.alt = Γ := by rcases Γ <;> rfl

end SigmaPiDelta

/-- Imported declaration from the Incompleteness formalization. -/
class UnivQuantifier (α : ℕ → Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  univ : ∀ {n}, α (n + 1) → α n

/-- Imported declaration from the Incompleteness formalization. -/
class ExQuantifier (α : ℕ → Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ex : ∀ {n}, α (n + 1) → α n

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∀' " => UnivQuantifier.univ

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃' " => ExQuantifier.ex

attribute [match_pattern]
  UnivQuantifier.univ
  ExQuantifier.ex

/-- Imported declaration from the Incompleteness formalization. -/
class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  /-- Imported declaration from the Incompleteness formalization. -/
  connectives : (n : ℕ) → LogicalConnective (α n)

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n

instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)] : LCWQ α where
  connectives := inferInstance

section «lp_section_1»

variable {α : ℕ → Type*} [UnivQuantifier α] [ExQuantifier α]

/-- Imported declaration from the Incompleteness formalization. -/
def quant : Polarity → α (n + 1) → α n
  | Sg, φ => ∃' φ
  | Pg, φ => ∀' φ

/--
@isnad1 id=eq.0h3v.s5.19873671eefa from=translated src=- shape=90504260 vocab=539f2fb9
-/
@[simp] lemma quant_sigma (φ : α (n + 1)) : quant Sg φ = ∃' φ := rfl

/--
@isnad1 id=eq.0h3v.s5.67d99cd6f1d8 from=translated src=- shape=90504260 vocab=bc273ebd
-/
@[simp] lemma quant_pi (φ : α (n + 1)) : quant Pg φ = ∀' φ := rfl

end «lp_section_1»

section «lp_section_2»

variable {α : ℕ → Type*} [UnivQuantifier α]

/-- Imported declaration from the Incompleteness formalization. -/
def univClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => univClosure (∀' a)

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∀* " => univClosure

/--
@isnad1 id=eq.0h2v.s5.9867886e3090 from=translated src=- shape=f69b1747 vocab=c5204fe2
-/
@[simp] lemma univClosure_zero (a : α 0) : ∀* a = a := rfl

/--
@isnad1 id=eq.0h3v.s5.e50eecf15b66 from=translated src=- shape=cdb8ba66 vocab=8fec54e0
-/
lemma univClosure_succ {n} (a : α (n + 1)) : ∀* a = ∀* ∀' a := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def univItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => univItr k (∀' a)

/-- Imported declaration from the Incompleteness formalization. -/
notation "∀^[" k "] " φ:64 => univItr k φ

/--
@isnad1 id=eq.0h3v.s4.0f1bb1687c4c from=translated src=- shape=bac807c1 vocab=6c5a8617
-/
@[simp] lemma univItr_zero (a : α n) : ∀^[0] a = a := rfl

/--
@isnad1 id=eq.0h3v.s5.8f9fb1672857 from=translated src=- shape=6ee67882 vocab=307504e8
-/
@[simp] lemma univItr_one (a : α (n + 1)) : ∀^[1] a = ∀' a := rfl

/--
@isnad1 id=eq.0h4v.s6.333a3f4d39b3 from=translated src=- shape=874a1a9e vocab=307504e8
-/
lemma univItr_succ {k} (a : α (n + (k + 1))) : ∀^[k + 1] a = ∀^[k] (∀' a) := rfl

end «lp_section_2»

section «lp_section_3»

variable {α : ℕ → Type*} [ExQuantifier α]

/-- Imported declaration from the Incompleteness formalization. -/
def exClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => exClosure (∃' a)

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃* " => exClosure

/--
@isnad1 id=eq.0h2v.s5.3cfbe833a7b7 from=translated src=- shape=f69b1747 vocab=36332410
-/
@[simp] lemma exClosure_zero (a : α 0) : ∃* a = a := rfl

/--
@isnad1 id=eq.0h3v.s5.0d83d22f77b6 from=translated src=- shape=cdb8ba66 vocab=ba6aa582
-/
lemma exClosure_succ {n} (a : α (n + 1)) : ∃* a = ∃* ∃' a := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def exItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => exItr k (∃' a)

/-- Imported declaration from the Incompleteness formalization. -/
notation "∃^[" k "] " φ:64 => exItr k φ

/--
@isnad1 id=eq.0h3v.s4.1ce3d8a0f672 from=translated src=- shape=bac807c1 vocab=49e53758
-/
@[simp] lemma exItr_zero (a : α n) : ∃^[0] a = a := rfl

/--
@isnad1 id=eq.0h3v.s5.5aaf7c9f8b7e from=translated src=- shape=6ee67882 vocab=4155c5dc
-/
@[simp] lemma exItr_one (a : α (n + 1)) : ∃^[1] a = ∃' a := rfl

/--
@isnad1 id=eq.0h4v.s6.f05d8a94a90c from=translated src=- shape=874a1a9e vocab=4155c5dc
-/
lemma exItr_succ {k} (a : α (n + (k + 1))) : ∃^[k + 1] a = ∃^[k] (∃' a) := rfl

end «lp_section_3»

section «lp_section_4»

variable {α : ℕ → Type*}

/-- Imported declaration from the Incompleteness formalization. -/
def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n :=
  ∀' (φ ==> ψ)

/-- Imported declaration from the Incompleteness formalization. -/
def bex [ExQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∃' (φ ⋏ ψ)

/-- Imported declaration from the Incompleteness formalization. -/
notation:64 "∀[" φ "] " ψ => ball φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
notation:64 "∃[" φ "] " ψ => bex φ ψ

end «lp_section_4»

end LO
-- Tengoku: 3 notation(s) of this module made scoped so they do not change other libraries (generated)
