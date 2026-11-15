import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

open UniqueFactorizationMonoid

def conductorLevel (W : WeierstrassCurve ℤ) : ℕ :=
  radical W.Δ.natAbs

/--
@isnad1 id=lt.0h1v.s3.d52a5c0e32ff from=translated src=- shape=942babd5 vocab=c19f9e26
-/
theorem conductorLevel_pos (W : WeierstrassCurve ℤ) : 0 < W.conductorLevel :=
  Nat.radical_pos _

/--
@isnad1 id=squarefr.0h1v.s3.9052253a207e from=translated src=- shape=12d4eb43 vocab=d6ebcacb
-/
theorem squarefree_conductorLevel (W : WeierstrassCurve ℤ) : Squarefree W.conductorLevel :=
  squarefree_radical

/--
@isnad1 id=iff.2h2v.s5.4045fcff7553 from=translated src=- shape=92eb2973 vocab=4c8e7a57
-/
theorem prime_dvd_conductorLevel_iff (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {q : ℕ}
    (hq : q.Prime) : q ∣ W.conductorLevel ↔ (q : ℤ) ∣ W.Δ := by
  rw [conductorLevel, dvd_radical_iff_of_irreducible hq.prime.irreducible
    (Int.natAbs_ne_zero.mpr hΔ)]
  exact Int.natCast_dvd.symm

end WeierstrassCurve

end
