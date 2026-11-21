import Tengoku.EocLeanVerification.EOC.Basic
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace EOC

open Finset

/-! ### Definition 5.1, part 1: word and prefix sums -/

/-- Prefix sum `s j = d 0 + d 1 + ... + d (j-1)` of a valuation word `d`.-/
def s (d : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ range j, d i

/--
@isnad1 id=eq.0h1v.s4.1cae4bfa0819 from=translated src=- shape=b298c1f9 vocab=ed27b840
-/
@[simp] theorem s_zero (d : ℕ → ℕ) : s d 0 = 0 :=
  Finset.sum_range_zero d

/--
@isnad1 id=eq.0h2v.s5.9aa4ed6273a4 from=translated src=- shape=6d1f17e2 vocab=ca6df2ce
-/
theorem s_succ (d : ℕ → ℕ) (j : ℕ) : s d (j + 1) = s d j + d j :=
  Finset.sum_range_succ d j

/-- Total valuation `S_N(D) = s_N`.-/
def S (d : ℕ → ℕ) (N : ℕ) : ℕ := s d N

/-! ### The dynamical orbit and the prescribed-valuation formal iteration -/

/-- The actual accelerated orbit of `m0` under `T`. Depends on `T`, hence
`noncomputable`.-/
noncomputable def orbit (m0 : ℕ) : ℕ → ℕ :=
  fun n => Nat.rec m0 (fun _ ih => T ih) n

/--
@isnad1 id=eq.0h1v.s3.5003dc34307e from=translated src=- shape=1fa26838 vocab=adf1cd18
-/
@[simp] theorem orbit_zero (m0 : ℕ) : orbit m0 0 = m0 := rfl
/--
@isnad1 id=eq.0h2v.s4.8d68b65d27c7 from=translated src=- shape=f2900817 vocab=8a8dd5d3
-/
theorem orbit_succ (m0 j : ℕ) : orbit m0 (j + 1) = T (orbit m0 j) := rfl

/-- The formal iteration using the *prescribed* word `d` in place of the actual
2-adic valuation at each step. This is the paper's "formal iterate `m_j`" made
concrete as a genuine total `ℕ`-valued recursive function via `Nat` floor
division — exact whenever `2 ^ d j` truly divides `3 * iter d m0 j + 1`; junk
otherwise, which is harmless since we only ever invoke it under hypotheses that
force the division to be exact. Fully computable: no dependence on `T`/`a`.-/
def iter (d : ℕ → ℕ) (m0 : ℕ) : ℕ → ℕ :=
  fun n => Nat.rec m0 (fun j ih => (3 * ih + 1) / 2 ^ d j) n

/--
@isnad1 id=eq.0h2v.s4.bc497e7dd854 from=translated src=- shape=68fe2a38 vocab=de28473c
-/
@[simp] theorem iter_zero (d : ℕ → ℕ) (m0 : ℕ) : iter d m0 0 = m0 := rfl
/--
@isnad1 id=eq.0h3v.s6.a845152dbfe1 from=translated src=- shape=9c2ad1f0 vocab=7cb74a27
-/
theorem iter_succ (d : ℕ → ℕ) (m0 j : ℕ) :
    iter d m0 (j + 1) = (3 * iter d m0 j + 1) / 2 ^ d j := rfl

/-- Definition 5.1: an odd `m0` realizes a length-`N` word `d` if the *actual*
accelerated orbit's valuations match `d` at every step `j < N`.-/
def Realizes (d : ℕ → ℕ) (N m0 : ℕ) : Prop :=
  Odd m0 ∧ ∀ j < N, a (orbit m0 j) = d j

/-! ### The bridge: dynamic realization ↔ the formal recursion -/

/-- If the *actual* orbit's valuations match `d` up to `N`, the actual orbit
coincides with the formal iteration `iter d m0` up to `N`.
@isnad1 id=eq.2h4v.s5.cf2183cc5d87 from=translated src=- shape=d0835803 vocab=3934bed6
-/
theorem orbit_eq_iter_of_orbit_valuation
    (d : ℕ → ℕ) (N m0 : ℕ) (h : ∀ j < N, a (orbit m0 j) = d j) :
    ∀ j, j ≤ N → orbit m0 j = iter d m0 j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ i ih =>
    intro hj
    have hiN : i < N := by omega
    have heq : orbit m0 i = iter d m0 i := ih (le_of_lt hiN)
    have hval : a (orbit m0 i) = d i := h i hiN
    have hval' : a (iter d m0 i) = d i := by rw [← heq]; exact hval
    rw [orbit_succ, iter_succ, heq]
    unfold T
    rw [hval']

/-- Conversely, if the *formal* iteration's valuations match `d` up to `N`, the
actual orbit coincides with `iter d m0` up to `N`.
@isnad1 id=eq.2h4v.s5.4fe8f4e4a7f5 from=translated src=- shape=9e46b415 vocab=3934bed6
-/
theorem orbit_eq_iter_of_iter_valuation
    (d : ℕ → ℕ) (N m0 : ℕ) (h : ∀ j < N, a (iter d m0 j) = d j) :
    ∀ j, j ≤ N → orbit m0 j = iter d m0 j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ i ih =>
    intro hj
    have hiN : i < N := by omega
    have heq : orbit m0 i = iter d m0 i := ih (le_of_lt hiN)
    have hval' : a (iter d m0 i) = d i := h i hiN
    rw [orbit_succ, iter_succ, heq]
    unfold T
    rw [hval']

/-- **Bridge theorem.** `Realizes` (defined dynamically, via the actual orbit
and the actual 2-adic valuation `a`) is exactly equivalent to `Odd m0` together
with the *prescribed*-valuation recursion `iter d m0` matching `d` at every
step `j < N`. This is the fact the paper uses implicitly — never as a separate
numbered result — when it moves between Definition 5.1's dynamical "realizes"
and the algebraic recursion driving the proof of Proposition 5.2. It is proved
here with no hypothesis beyond what `Realizes` and `iter` already state.
@isnad1 id=iff.0h3v.s5.cdfc9c5f707f from=translated src=- shape=9f84ec57 vocab=f398ddc9
-/
theorem realizes_iff_iter_valuation (d : ℕ → ℕ) (N m0 : ℕ) :
    Realizes d N m0 ↔ Odd m0 ∧ ∀ j < N, a (iter d m0 j) = d j := by
  constructor
  · rintro ⟨hodd, hval⟩
    refine ⟨hodd, fun j hj => ?_⟩
    have heq := orbit_eq_iter_of_orbit_valuation d N m0 hval j (le_of_lt hj)
    rw [← heq]
    exact hval j hj
  · rintro ⟨hodd, hval⟩
    refine ⟨hodd, fun j hj => ?_⟩
    have heq := orbit_eq_iter_of_iter_valuation d N m0 hval j (le_of_lt hj)
    rw [heq]
    exact hval j hj

end EOC
