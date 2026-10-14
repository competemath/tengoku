/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/
module

public import Tengoku.LeanPool.LeanPool.CriticalPortraits.Portraits
import Tengoku.LeanPool.LeanPool.CriticalPortraits.Denominator
import Tengoku.LeanPool.LeanPool.CriticalPortraits.Surjectivity
public import Tengoku

/-!
# The headline census theorem: `#{portraits} = C(N, d−1) / d` for all `d`

This module assembles the four proved, sorry-free ingredients into the final count.
With positions in `ZMod N` (`N = d*m`) and the delete-min map `T`:

* **Forward** (`T_levelCanonical`) + **weight** (`T_card`): `T` maps each portrait to a
  level-canonical `(d−1)`-subset, i.e. `Set.MapsTo T {P | Portrait} {U | U.card = d−1 ∧ …}`.
* **Injectivity** (`T_injOn`) and **Surjectivity** (`T_surjOn`) upgrade this to `Set.BijOn`.
* `Set.BijOn.equiv` then gives an equivalence of the two subtypes, so their `Fintype.card`s
  agree; composing with the **denominator** count `card_levelCanonical_mul` yields the result.
-/

@[expose] public section

namespace CriticalPortraits
open Finset

/-- **PRIMARY (multiplicative form).** `d · #{portraits} = C(d*m, d-1)`.

The cleanest statement: the count of portraits times `d` equals the binomial numerator.
Proved by the `T`-bijection onto level-canonical `(d−1)`-subsets composed with
`card_levelCanonical_mul`.
@isnad1 id=eq.2h2v.s6.3f9f1860d9cd from=translated src=- shape=50752c80 vocab=fe41789a
-/
theorem card_portraits_mul {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    d * Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = (d*m).choose (d-1) := by
  -- `T` is a bijection from portraits onto level-canonical `(d−1)`-subsets.
  have hbij : Set.BijOn (T (N := d*m)) {P | Portrait d m P}
      {U | U.card = d - 1 ∧ LevelCanonical d m U} :=
    ⟨fun P hP => ⟨T_card hP, T_levelCanonical hd hm hP⟩,
     T_injOn hd hm, T_surjOn hd hm⟩
  -- The induced equivalence of subtypes equates their cardinalities.
  have hcard : Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = Fintype.card {U : Finset (ZMod (d*m)) // U.card = d - 1 ∧ LevelCanonical d m U} :=
    Fintype.card_congr hbij.equiv
  rw [hcard]
  exact card_levelCanonical_mul d m hd hm

/-- **HEADLINE CENSUS THEOREM.** `#{portraits} = C(d*m, d-1) / d` for all `d` (and all `m`).

The number of degree-`d` portraits at level `m` equals `C(d·m, d−1) / d`. Follows from the
multiplicative form by `Nat.div_eq_of_eq_mul_right` (exact `ℕ`-division, no remainder).
@isnad1 id=eq.2h2v.s6.06b07b8772dc from=translated src=- shape=2963f1e6 vocab=e65b93a9
-/
theorem card_portraits {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = (d*m).choose (d-1) / d :=
  (Nat.div_eq_of_eq_mul_right hd (card_portraits_mul hd hm).symm).symm

/-- **Exactness of the `/ d`.** The denominator divides the numerator: `d ∣ C(d*m, d-1)`. Hence the
`/ d` in `card_portraits` is *exact* `ℕ`-division (the count is a genuine integer), not floor
rounding — the witness is the portrait count itself, read off `card_portraits_mul`.
@isnad1 id=dvd.2h2v.s5.9c758da87403 from=translated src=- shape=9ccdb8ab vocab=a485350c
-/
theorem d_dvd_choose {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    d ∣ (d * m).choose (d - 1) :=
  ⟨_, (card_portraits_mul hd hm).symm⟩

end CriticalPortraits
