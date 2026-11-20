/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.LinearAlgebra.Matrix.Symmetric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open scoped Matrix

inductive ADEType where

  | A (n : ℕ)

  | D (n : ℕ)

  | E6

  | E7

  | E8
deriving DecidableEq, Repr

namespace ADEType

def IsRegular : ADEType → Prop
  | .A n => 1 ≤ n
  | .D n => 4 ≤ n
  | .E6 | .E7 | .E8 => True

instance (t : ADEType) : Decidable t.IsRegular := by
  cases t <;> simp only [IsRegular] <;> infer_instance

def rank : ADEType → ℕ
  | .A n => n
  | .D n => n
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

def det : ADEType → ℤ
  | .A n => (n : ℤ) + 1
  | .D _ => 4
  | .E6 => 3
  | .E7 => 2
  | .E8 => 1

end ADEType

def gramAEntry (i j : ℕ) : ℤ :=
  if i = j then 2 else if i + 1 = j ∨ j + 1 = i then -1 else 0

def gramDEntry (n i j : ℕ) : ℤ :=
  if i = j then 2
  else if ((i + 1 = j ∨ j + 1 = i) ∧ i + 2 ≤ n ∧ j + 2 ≤ n) ∨
      (i + 3 = n ∧ j + 1 = n) ∨ (j + 3 = n ∧ i + 1 = n) then -1 else 0

def gramEEntry (n i j : ℕ) : ℤ :=
  if i = j then 2
  else if ((i + 1 = j ∨ j + 1 = i) ∧ i + 2 ≤ n ∧ j + 2 ≤ n) ∨
      (i = 2 ∧ j + 1 = n) ∨ (j = 2 ∧ i + 1 = n) then -1 else 0

def gramA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => gramAEntry i.1 j.1

def gramD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => gramDEntry n i.1 j.1

def gramE (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => gramEEntry n i.1 j.1

/--
@isnad1 id=eq.0h2v.s3.ca10df0339be from=translated src=- shape=ab795eaa vocab=a9ae922f
-/
theorem gramAEntry_symm (i j : ℕ) : gramAEntry i j = gramAEntry j i := by
  unfold gramAEntry
  split_ifs <;> omega

/--
@isnad1 id=eq.0h3v.s4.4042276c953d from=translated src=- shape=4ed00171 vocab=e8ba2915
-/
theorem gramDEntry_symm (n i j : ℕ) : gramDEntry n i j = gramDEntry n j i := by
  unfold gramDEntry
  split_ifs <;> omega

/--
@isnad1 id=eq.0h3v.s4.234b022c1d6d from=translated src=- shape=4ed00171 vocab=104ab044
-/
theorem gramEEntry_symm (n i j : ℕ) : gramEEntry n i j = gramEEntry n j i := by
  unfold gramEEntry
  split_ifs <;> omega

namespace ADEType

def gramEntry : ADEType → ℕ → ℕ → ℤ
  | .A _, i, j => gramAEntry i j
  | .D n, i, j => gramDEntry n i j
  | .E6, i, j => gramEEntry 6 i j
  | .E7, i, j => gramEEntry 7 i j
  | .E8, i, j => gramEEntry 8 i j

def gram (t : ADEType) : Matrix (Fin t.rank) (Fin t.rank) ℤ :=
  fun i j => t.gramEntry i.1 j.1

/--
@isnad1 id=eq.0h3v.s4.a2aeda3b43a0 from=translated src=- shape=72544f21 vocab=4bf07ff1
-/
theorem gramEntry_symm (t : ADEType) (i j : ℕ) : t.gramEntry i j = t.gramEntry j i := by
  cases t with
  | A _ => exact gramAEntry_symm i j
  | D n => exact gramDEntry_symm n i j
  | E6 => exact gramEEntry_symm 6 i j
  | E7 => exact gramEEntry_symm 7 i j
  | E8 => exact gramEEntry_symm 8 i j

/--
@isnad1 id=eq.0h2v.s3.e3b2e6e152cc from=translated src=- shape=6f92c63f vocab=4bf07ff1
-/
theorem gramEntry_diag (t : ADEType) (i : ℕ) : t.gramEntry i i = 2 := by
  cases t <;> simp [gramEntry, gramAEntry, gramDEntry, gramEEntry]

def rankSum (ts : List ADEType) : ℕ := (ts.map rank).sum

/--
@isnad1 id=eq.0h0v.s3.3136a470bfd4 from=translated src=- shape=35225b15 vocab=dcc1f74a
-/
@[simp] theorem rankSum_nil : rankSum [] = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.9cdf0f267467 from=translated src=- shape=d428a9ab vocab=db4cbb5a
-/
@[simp] theorem rankSum_cons (t : ADEType) (ts : List ADEType) :
    rankSum (t :: ts) = t.rank + rankSum ts := rfl

end ADEType

def adeEntry : List ADEType → ℕ → ℕ → ℤ
  | [], _, _ => 0
  | t :: ts, i, j =>
      if i < t.rank ∧ j < t.rank then t.gramEntry i j
      else if t.rank ≤ i ∧ t.rank ≤ j then adeEntry ts (i - t.rank) (j - t.rank)
      else 0

def adeGram (ts : List ADEType) : (n : ℕ) × Matrix (Fin n) (Fin n) ℤ :=
  ⟨ADEType.rankSum ts, fun i j => adeEntry ts i.1 j.1⟩

/--
@isnad1 id=eq.0h3v.s4.42baf23934fb from=translated src=- shape=689c8eb2 vocab=7ce7810d
-/
theorem adeEntry_symm : ∀ (ts : List ADEType) (i j : ℕ), adeEntry ts i j = adeEntry ts j i
  | [], _, _ => rfl
  | t :: ts, i, j => by
      by_cases h₁ : i < t.rank ∧ j < t.rank
      · have h₁' : j < t.rank ∧ i < t.rank := ⟨h₁.2, h₁.1⟩
        simp only [adeEntry, ite_eq_left h₁, ite_eq_left h₁']
        exact t.gramEntry_symm i j
      · have h₁' : ¬ (j < t.rank ∧ i < t.rank) := fun h => h₁ ⟨h.2, h.1⟩
        by_cases h₂ : t.rank ≤ i ∧ t.rank ≤ j
        · have h₂' : t.rank ≤ j ∧ t.rank ≤ i := ⟨h₂.2, h₂.1⟩
          simp only [adeEntry, ite_eq_right h₁, ite_eq_right h₁', ite_eq_left h₂, ite_eq_left h₂']
          exact adeEntry_symm ts (i - t.rank) (j - t.rank)
        · have h₂' : ¬ (t.rank ≤ j ∧ t.rank ≤ i) := fun h => h₂ ⟨h.2, h.1⟩
          simp only [adeEntry, ite_eq_right h₁, ite_eq_right h₁', ite_eq_right h₂, ite_eq_right h₂']

/--
@isnad1 id=issymm.0h1v.s4.82d51acac575 from=translated src=- shape=7b697402 vocab=728edfaf
-/
theorem adeGram_isSymm (ts : List ADEType) : (adeGram ts).2.IsSymm := by
  ext i j
  exact adeEntry_symm ts j.1 i.1

/--
@isnad1 id=eq.2h3v.s5.f002f752c2ce from=translated src=- shape=70bfa6d5 vocab=f6df2d0d
-/
theorem adeEntry_singleton (t : ADEType) {i j : ℕ} (hi : i < t.rank) (hj : j < t.rank) :
    adeEntry [t] i j = t.gramEntry i j := by
  have h : i < t.rank ∧ j < t.rank := ⟨hi, hj⟩
  simp only [adeEntry, ite_eq_left h]

end Lattice
end SRG266
