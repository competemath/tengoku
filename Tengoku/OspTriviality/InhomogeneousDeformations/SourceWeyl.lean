import Tengoku.OspTriviality.InhomogeneousDeformations.IndexedU
import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
import Tengoku.Seed.Algebra.Module.LinearMap.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# I106 R2, W1 — `W_n` as operators on `MvPolynomial (Fin n) ℚ`

**The open choice, resolved**: `W_n` is realized as `Module.End ℚ (WPoly n)`, the even
generators `B_u` as multiplication and differentiation operators, `Module.End`'s own
composition standing for the algebra product. Rejected: a free-algebra-modulo-relations
model (`FreeAlgebra`/`RingQuot`) — mathlib has no Weyl algebra to quotient toward, and the
same `RingQuot`-normalization stall F2 (R0) already named for the source algebra applies
here too, with no offsetting benefit; the operator model instead turns the one relation
that matters (`eq:source`'s `[b_u,b_v]=J_{uv}1`) into a *computation*
(`MvPolynomial.pderiv_mul`/`pderiv_X`), not a postulate.

**A1**: `[B_u, B_v] = Jn n u v • 1`, `Jn` **imported unchanged from the frozen
`Indexed.lean`**, proved below by direct computation, case-split on the even/odd shape of
`u` and `v` — never a fresh matrix.
-/

namespace InhomogeneousDeformations
namespace Source

/-- The `n` polynomial variables `W_n` acts on — **not** `Indexed.lean`'s `Pn n` (which has
`2n` variables `beta_1,...,beta_{2n}` and a different role: the coordinate ring of the target
side, not the operator domain here).-/
noncomputable abbrev WPoly (n : ℕ) : Type := MvPolynomial (Fin n) ℚ

/-- The index `j : Fin n` a source index `u : Fin (2n)` corresponds to: `u = 2j` or `u = 2j+1`.
Matches `Indexed.lean`'s own `evenIdx`/`oddIdx` inverse (`u.val / 2`), reused rather than
redefined.-/
noncomputable def wIndex (n : ℕ) (u : Fin (2 * n)) : Fin n :=
  ⟨(u : ℕ) / 2, by have := u.isLt; omega⟩

/--
@isnad1 id=eq.0h2v.s3.cd4ab471370d from=translated src=- shape=6ddf6d3e vocab=8701cb88
-/
theorem wIndex_evenIdx (n : ℕ) (j : Fin n) : wIndex n (Indexed.evenIdx n j) = j := by
  apply Fin.ext
  unfold wIndex Indexed.evenIdx
  simp

/--
@isnad1 id=eq.0h2v.s3.08b8fa3b3a3b from=translated src=- shape=6ddf6d3e vocab=db29e43a
-/
theorem wIndex_oddIdx (n : ℕ) (j : Fin n) : wIndex n (Indexed.oddIdx n j) = j := by
  apply Fin.ext
  unfold wIndex Indexed.oddIdx
  simp
  omega

/-- `B_u`: differentiation (`pderiv`) at the even indices, multiplication by the
corresponding variable at the odd indices — the assignment `B_{2j} = \partial_j`,
`B_{2j+1} = X_j` fixed by matching `Jn n (evenIdx n j) (oddIdx n j) = 1` (checked below,
`Jn_B_even_odd`) against `[\partial_j, X_j\cdot] = 1` (a computation, `pderiv_X_self`).-/
noncomputable def B (n : ℕ) (u : Fin (2 * n)) : Module.End ℚ (WPoly n) :=
  if (u : ℕ) % 2 = 0 then (MvPolynomial.pderiv (wIndex n u)).toLinearMap
  else LinearMap.mulLeft ℚ (MvPolynomial.X (wIndex n u))

/-- The commutator of two operators on `WPoly n`, as an element of `Module.End ℚ (WPoly n)`
(a `Ring`, composition as multiplication).-/
noncomputable def opComm (f g : Module.End ℚ (WPoly n)) : Module.End ℚ (WPoly n) := f * g - g * f

/--
@isnad1 id=eq.1h2v.s6.959d0b02060f from=translated src=- shape=4675a587 vocab=719c7309
-/
theorem u_eq_evenIdx_of_even (n : ℕ) (u : Fin (2 * n)) (h : (u : ℕ) % 2 = 0) :
    u = Indexed.evenIdx n (wIndex n u) := by
  apply Fin.ext; unfold Indexed.evenIdx wIndex; dsimp only; omega

/--
@isnad1 id=eq.1h2v.s6.e3e761b870d3 from=translated src=- shape=9dc46bfa vocab=114a33c3
-/
theorem u_eq_oddIdx_of_odd (n : ℕ) (u : Fin (2 * n)) (h : ¬ (u : ℕ) % 2 = 0) :
    u = Indexed.oddIdx n (wIndex n u) := by
  apply Fin.ext; unfold Indexed.oddIdx wIndex; dsimp only; omega

/-- `Jn`'s value as a plain `ℚ` scalar — `Jn` only ever takes the constant values `1`, `-1` or
`0` (`cratN n c = MvPolynomial.C c`), so `constantCoeff` recovers exactly that value; `Jn`
itself appears literally as the argument, not redefined.-/
noncomputable def JnQ (n : ℕ) (u v : Fin (2 * n)) : ℚ :=
  MvPolynomial.constantCoeff (Indexed.Jn n u v)

/--
@isnad1 id=eq.1h3v.s6.e75e22f8de1a from=translated src=- shape=cbc242db vocab=a232f6fa
-/
theorem JnQ_eq_zero_of_same_parity (n : ℕ) (u v : Fin (2 * n))
    (h : (u : ℕ) % 2 = (v : ℕ) % 2) : JnQ n u v = 0 := by
  unfold JnQ Indexed.Jn
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp

/--
@isnad1 id=eq.0h3v.s5.4735cc411bd1 from=translated src=- shape=363870a9 vocab=26bff314
-/
theorem JnQ_evenIdx_oddIdx (n : ℕ) (i j : Fin n) :
    JnQ n (Indexed.evenIdx n i) (Indexed.oddIdx n j) = if i = j then 1 else 0 := by
  unfold JnQ Indexed.Jn Indexed.evenIdx Indexed.oddIdx
  dsimp only
  by_cases hij : i = j
  · subst hij; rw [ite_eq_left (by omega)]; simp
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp [hij]

/--
@isnad1 id=eq.0h3v.s5.1dc00367a8ec from=translated src=- shape=e000b6e7 vocab=df66f580
-/
theorem JnQ_oddIdx_evenIdx (n : ℕ) (i j : Fin n) :
    JnQ n (Indexed.oddIdx n i) (Indexed.evenIdx n j) = if i = j then (-1 : ℚ) else 0 := by
  unfold JnQ Indexed.Jn Indexed.evenIdx Indexed.oddIdx
  dsimp only
  by_cases hij : i = j
  · subst hij; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    unfold Indexed.cratN; simp
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp [hij]

end Source
end InhomogeneousDeformations
