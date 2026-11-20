/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Name.MemLang
import Tengoku.Forcing.Forcing.Name.Atomic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The family-relative formula forcing relation

The forcing relation by direct recursion on `memLang.BoundedFormula`, at ADR 0003's audited
signatures. The clauses: `falsum` is never forced; the atomic cases *are* `ForcesEq` and
`ForcesMem` (definitionally — see the unfolding laws); implication is quantified over
strengthenings; universal quantification ranges over a **name family `𝒩`** — never over all
of `PName P`, which would re-run the certified collapse. The definition takes no
`SubnameClosed` hypothesis and no assignment-membership proofs: those belong to the adequacy
layer, not the syntax.

The five unfolding laws are named `↔`-laws, deliberately not `@[simp]`. **Persistence**
(`ForcesFormula.mono`) is structural. **Density-regularity**
(`forcesFormula_iff_isDenseBelow`) is the formula-level blocker-extraction engine the truth
lemma consumes — forcing is equivalent to forcing being dense below — with the atomic cases
supplied by `IsDenseBelow.trans` (the coverage lemma in forcing-order form) and the
quantifier cases by structural induction.

Notation is restricted to **sentences** (`p ⊩[𝒩] φ` for `ForcesSentence`): general bounded
formulas keep their assignments explicit, since notation carrying both a free-variable
assignment and a bound-variable vector would be unreadable.

Scope (M6 discipline): Syntax-only imports on the model-theory side; no `Semantics`, no
visibility, no genericity, no material imports.

## Main definitions

* `Forcing.ForcesFormula`: the family-relative forcing relation on bounded formulas.
* `Forcing.ForcesSentence`, notation `p ⊩[𝒩] φ`: the sentence layer.

## Main results

* `Forcing.forcesFormula_falsum` … `forcesFormula_all`: the named unfolding laws.
* `Forcing.ForcesFormula.mono`: persistence under strengthening.
* `Forcing.forcesFormula_iff_isDenseBelow`: density-regularity.
-/

universe u v

namespace Forcing

open FirstOrder PName

variable {P : Type u} [Preorder P] {β : Type v} {𝒩 : Set (PName P)} {v : β → PName P}
variable {p q : P} {τ σ : PName P}

/-- The family-relative forcing relation, by direct recursion on formulas: atomic cases are
the atomic relations, implication quantifies over strengthenings, and the universal
quantifier ranges over the name family `𝒩`.-/
def ForcesFormula (𝒩 : Set (PName P)) (v : β → PName P) :
    ∀ {n}, P → memLang.BoundedFormula β n → (Fin n → PName P) → Prop
  | _, _, .falsum, _ => False
  | _, p, .equal t₁ t₂, xs =>
      ForcesEq p (evalTerm (Sum.elim v xs) t₁) (evalTerm (Sum.elim v xs) t₂)
  | _, p, .rel .mem ts, xs =>
      ForcesMem p (evalTerm (Sum.elim v xs) (ts 0)) (evalTerm (Sum.elim v xs) (ts 1))
  | _, p, .imp φ ψ, xs => ∀ q ≤ p, ForcesFormula 𝒩 v q φ xs → ForcesFormula 𝒩 v q ψ xs
  | _, p, .all φ, xs => ∀ τ ∈ 𝒩, ForcesFormula 𝒩 v p φ (Fin.snoc xs τ)

/-! ### The named unfolding laws (deliberately not `@[simp]`) -/

/--
@isnad1 id=iff.0h7v.s5.0f8de8579ed0 from=translated src=- shape=b3686be0 vocab=240c2f93
-/
theorem forcesFormula_falsum {n} {xs : Fin n → PName P} :
    ForcesFormula 𝒩 v p (.falsum : memLang.BoundedFormula β n) xs ↔ False :=
  Iff.rfl

/--
@isnad1 id=iff.0h9v.s6.b6d83bf04d11 from=translated src=- shape=d3a701a7 vocab=29768b11
-/
theorem forcesFormula_equal {n} {t₁ t₂ : memLang.Term (β ⊕ Fin n)} {xs : Fin n → PName P} :
    ForcesFormula 𝒩 v p (.equal t₁ t₂) xs ↔
      ForcesEq p (evalTerm (Sum.elim v xs) t₁) (evalTerm (Sum.elim v xs) t₂) :=
  Iff.rfl

/--
@isnad1 id=iff.0h8v.s7.fed4624c1c38 from=translated src=- shape=51266bef vocab=efb82139
-/
theorem forcesFormula_rel {n} {ts : Fin 2 → memLang.Term (β ⊕ Fin n)} {xs : Fin n → PName P} :
    ForcesFormula 𝒩 v p (.rel .mem ts) xs ↔
      ForcesMem p (evalTerm (Sum.elim v xs) (ts 0)) (evalTerm (Sum.elim v xs) (ts 1)) :=
  Iff.rfl

/--
@isnad1 id=iff.0h9v.s6.bcd9ef1724df from=translated src=- shape=06e5857b vocab=01f4c831
-/
theorem forcesFormula_imp {n} {φ ψ : memLang.BoundedFormula β n} {xs : Fin n → PName P} :
    ForcesFormula 𝒩 v p (φ.imp ψ) xs ↔
      ∀ q ≤ p, ForcesFormula 𝒩 v q φ xs → ForcesFormula 𝒩 v q ψ xs :=
  Iff.rfl

/--
@isnad1 id=iff.0h8v.s6.98e71254780e from=translated src=- shape=69a0516b vocab=5bbb456e
-/
theorem forcesFormula_all {n} {φ : memLang.BoundedFormula β (n + 1)} {xs : Fin n → PName P} :
    ForcesFormula 𝒩 v p φ.all xs ↔ ∀ τ ∈ 𝒩, ForcesFormula 𝒩 v p φ (Fin.snoc xs τ) :=
  Iff.rfl

/-! ### Persistence -/

/-- **Persistence** under strengthening, structurally: atomic persistence, transitivity
narrowing for implication, pointwise for the quantifier.
@isnad1 id=forcesfo.2h9v.s5.660548ceda58 from=translated src=- shape=25377293 vocab=16c0af35
-/
theorem ForcesFormula.mono :
    ∀ {n} {p q : P} (φ : memLang.BoundedFormula β n) {xs : Fin n → PName P},
      ForcesFormula 𝒩 v p φ xs → q ≤ p → ForcesFormula 𝒩 v q φ xs
  | _, _, _, .falsum, _, h, _ => h
  | _, _, _, .equal _ _, _, h, hqp => ForcesEq.mono h hqp
  | _, _, _, .rel .mem _, _, h, hqp => ForcesMem.mono h hqp
  | _, _, _, .imp _ _, _, h, hqp => fun r hr hφ ↦ h r (hr.trans hqp) hφ
  | _, _, _, .all φ, _, h, hqp => fun τ hτ ↦ ForcesFormula.mono φ (h τ hτ) hqp

/-! ### The atomic regularity instances -/

/-- Regularity at atomic equality: `IsDenseBelow.trans` through the equality clause.
@isnad1 id=forceseq.1h4v.s5.b38e2753ab00 from=translated src=- shape=b1dc510a vocab=2d90338a
-/
theorem forcesEq_of_isDenseBelow (h : IsDenseBelow {q | ForcesEq q τ σ} p) :
    ForcesEq p τ σ := by
  rw [forcesEq_iff]
  constructor
  · intro i r hrp hrc
    have hD : IsDenseBelow {s | ForcesEq s τ σ ∧ s ≤ τ.conds i} r := fun s hs ↦ by
      obtain ⟨t, htEq, hts⟩ := h (Set.mem_Iic.2 ((Set.mem_Iic.1 hs).trans hrp))
      exact ⟨t, ⟨htEq, ((hts.trans (Set.mem_Iic.1 hs)).trans hrc)⟩, hts⟩
    exact hD.trans fun s hs ↦ (forcesEq_iff.1 hs.1).1 i s le_rfl hs.2
  · intro j r hrp hrc
    have hD : IsDenseBelow {s | ForcesEq s τ σ ∧ s ≤ σ.conds j} r := fun s hs ↦ by
      obtain ⟨t, htEq, hts⟩ := h (Set.mem_Iic.2 ((Set.mem_Iic.1 hs).trans hrp))
      exact ⟨t, ⟨htEq, ((hts.trans (Set.mem_Iic.1 hs)).trans hrc)⟩, hts⟩
    exact hD.trans fun s hs ↦ (forcesEq_iff.1 hs.1).2 j s le_rfl hs.2

/-- Regularity at atomic membership: density-below is itself regular.
@isnad1 id=forcesme.1h4v.s5.57d543b000c9 from=translated src=- shape=b1dc510a vocab=796a6345
-/
theorem forcesMem_of_isDenseBelow (h : IsDenseBelow {q | ForcesMem q τ σ} p) :
    ForcesMem p τ σ :=
  IsDenseBelow.trans h fun _ hq ↦ hq

/-! ### Density-regularity -/

/-- The hard direction of density-regularity: if forcing is dense below `p`, then `p`
forces. Atomic cases by `IsDenseBelow.trans`; implication and quantifier by structural
induction.
@isnad1 id=forcesfo.1h8v.s5.9ab99261cd00 from=translated src=- shape=bfcc29e2 vocab=62a46503
-/
theorem forcesFormula_of_isDenseBelow :
    ∀ {n} (φ : memLang.BoundedFormula β n) {p : P} {xs : Fin n → PName P},
      IsDenseBelow {q | ForcesFormula 𝒩 v q φ xs} p → ForcesFormula 𝒩 v p φ xs
  | _, .falsum, p, xs, h => by
    obtain ⟨y, hy, -⟩ := h (Set.mem_Iic.2 le_rfl)
    exact hy
  | _, .equal t₁ t₂, p, xs, h => forcesEq_of_isDenseBelow h
  | _, .rel .mem ts, p, xs, h => forcesMem_of_isDenseBelow h
  | _, .imp φ ψ, p, xs, h => fun r hrp hφ ↦
      forcesFormula_of_isDenseBelow ψ fun s hs ↦ by
        obtain ⟨t, htF, hts⟩ := h (Set.mem_Iic.2 (((Set.mem_Iic.1 hs).trans hrp)))
        exact ⟨t, htF t le_rfl (ForcesFormula.mono φ hφ (hts.trans (Set.mem_Iic.1 hs))), hts⟩
  | _, .all φ, p, xs, h => fun τ hτ ↦
      forcesFormula_of_isDenseBelow φ fun s hs ↦ by
        obtain ⟨t, htF, hts⟩ := h hs
        exact ⟨t, htF τ hτ, hts⟩

/-- **Density-regularity**: forcing is equivalent to forcing being dense below. The forward
direction is persistence; the reverse is the formula-level blocker-extraction engine the
truth lemma consumes — failure of forcing yields a strengthening below which forcing is
impossible.
@isnad1 id=iff.0h8v.s5.7bfd02889938 from=translated src=- shape=c28a136c vocab=62a46503
-/
theorem forcesFormula_iff_isDenseBelow {n} (φ : memLang.BoundedFormula β n)
    {xs : Fin n → PName P} :
    ForcesFormula 𝒩 v p φ xs ↔ IsDenseBelow {q | ForcesFormula 𝒩 v q φ xs} p :=
  ⟨fun h _ hr ↦ ⟨_, ForcesFormula.mono φ h (Set.mem_Iic.1 hr), le_rfl⟩,
    forcesFormula_of_isDenseBelow φ⟩

/-! ### Sentences and notation -/

/-- Sentence-level forcing: no free variables, no bound-variable vector.-/
def ForcesSentence (𝒩 : Set (PName P)) (p : P) (φ : memLang.Sentence) : Prop :=
  ForcesFormula 𝒩 Empty.elim p φ fun i ↦ i.elim0

@[inherit_doc] scoped notation:50 p " ⊩[" 𝒩 "] " φ:51 => ForcesSentence 𝒩 p φ

/--
@isnad1 id=forcesse.2h5v.s5.9ca2dbfa97bf from=translated src=- shape=5bcb12dd vocab=38440d1e
-/
theorem ForcesSentence.mono {φ : memLang.Sentence} (h : p ⊩[𝒩] φ) (hqp : q ≤ p) :
    q ⊩[𝒩] φ :=
  ForcesFormula.mono φ h hqp

/--
@isnad1 id=iff.0h4v.s5.498e7b43a5cc from=translated src=- shape=2eb98340 vocab=2f9bbb11
-/
theorem forcesSentence_iff_isDenseBelow (φ : memLang.Sentence) :
    p ⊩[𝒩] φ ↔ IsDenseBelow {q | q ⊩[𝒩] φ} p :=
  forcesFormula_iff_isDenseBelow φ

/-!
### Sanity examples

The atomic reductions are definitional; falsum is never forced over any family; and sentence
notation composes with persistence.
-/

end Forcing
