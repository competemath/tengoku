import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FreyPackage

structure IsConductorLevel (P : FreyPackage) (N : ℕ) : Prop where

  pos : 0 < N

  squarefree : Squarefree N

  support : ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ∣ P.a * P.b * P.c

namespace IsConductorLevel

variable {P : FreyPackage} {N : ℕ}

/--
@isnad1 id=isconduc.3h3v.s4.37aa6caa4ac9 from=translated src=- shape=b7e0322d vocab=ea63e80d
-/
theorem of_dvd (h : P.IsConductorLevel N) {M : ℕ} (hMN : M ∣ N) (hM : 0 < M) :
    P.IsConductorLevel M :=
  ⟨hM, h.squarefree.squarefree_of_dvd hMN, fun q hq hqM => h.support q hq (hqM.trans hMN)⟩

/--
@isnad1 id=dvd.2h2v.s5.54243756206a from=translated src=- shape=b3e3f740 vocab=daec9f51
-/
theorem p_dvd_abc (h : P.IsConductorLevel N) (hpN : P.p ∣ N) :
    (P.p : ℤ) ∣ P.a * P.b * P.c :=
  h.support P.p P.pp hpN

/--
@isnad1 id=not.2h2v.s5.8dbe48399bcb from=translated src=- shape=78212bec vocab=daec9f51
-/
theorem not_p_dvd (h : P.IsConductorLevel N) (hp : ¬ (P.p : ℤ) ∣ P.a * P.b * P.c) :
    ¬ P.p ∣ N :=
  fun hpN => hp (h.p_dvd_abc hpN)

/--
@isnad1 id=not.2h3v.s5.ca8d8ff7be40 from=translated src=- shape=6a451854 vocab=8f50807f
-/
theorem sq_not_dvd (h : P.IsConductorLevel N) {q : ℕ} (hq : q.Prime) : ¬ q ^ 2 ∣ N := by
  intro hsq
  exact Nat.squarefree_iff_prime_squarefree.mp h.squarefree q hq (by rwa [← pow_two])

/--
@isnad1 id=not.1h2v.s4.5eb3dd82cd66 from=translated src=- shape=5cb2c717 vocab=0f118ede
-/
theorem not_four_dvd (h : P.IsConductorLevel N) : ¬ 4 ∣ N := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  exact h4 ▸ h.sq_not_dvd Nat.prime_two

end IsConductorLevel

end FreyPackage
