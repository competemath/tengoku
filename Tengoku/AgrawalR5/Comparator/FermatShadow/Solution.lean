import Tengoku
import Tengoku.AgrawalR5.AgrawalCore.AgrawalBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Submitted proof of the independent Fermat-shadow challenge. -/

open Polynomial

namespace FermatShadowChallenge

/--
@isnad1 id=dvd.3h1v.s9.1c96fce48ead from=translated src=- shape=e0c37648 vocab=fc2d30d4
-/
theorem agrawal_fermat_shadow {n : ℕ} (hsq : Squarefree n)
    (h5 : ¬ 5 ∣ n)
    (h : ∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g) :
    n ∣ 5 ^ (n - 1) - 1 :=
  AgrawalCore.agrawal_fermat_shadow hsq h5 h

end FermatShadowChallenge
