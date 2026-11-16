import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

namespace Tengoku.FltAnthropic.FreyPackage

structure IsConductorLevel (P : FreyPackage) (N : ℕ) : Prop where

  pos : 0 < N

  squarefree : Squarefree N

  support : ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ∣ P.a * P.b * P.c

namespace IsConductorLevel

variable {P : FreyPackage} {N : ℕ}

/--
@isnad1 id=isconduc.3h3v.s4.067373ad0e72 from=translated src=- shape=b7e0322d vocab=93b9b1e9
-/
theorem of_dvd (h : P.IsConductorLevel N) {M : ℕ} (hMN : M ∣ N) (hM : 0 < M) :
    P.IsConductorLevel M :=
  ⟨hM, h.squarefree.squarefree_of_dvd hMN, fun q hq hqM => h.support q hq (hqM.trans hMN)⟩

/--
@isnad1 id=dvd.2h2v.s5.1a26247658c3 from=translated src=- shape=b3e3f740 vocab=2d7547d0
-/
theorem p_dvd_abc (h : P.IsConductorLevel N) (hpN : P.p ∣ N) :
    (P.p : ℤ) ∣ P.a * P.b * P.c :=
  h.support P.p P.pp hpN

/--
@isnad1 id=not.2h2v.s5.a79a48e488b3 from=translated src=- shape=78212bec vocab=2d7547d0
-/
theorem not_p_dvd (h : P.IsConductorLevel N) (hp : ¬ (P.p : ℤ) ∣ P.a * P.b * P.c) :
    ¬ P.p ∣ N :=
  fun hpN => hp (h.p_dvd_abc hpN)

/--
@isnad1 id=not.2h3v.s5.b54f8fad019b from=translated src=- shape=6a451854 vocab=d6b375dc
-/
theorem sq_not_dvd (h : P.IsConductorLevel N) {q : ℕ} (hq : q.Prime) : ¬ q ^ 2 ∣ N := by
  intro hsq
  exact Nat.squarefree_iff_prime_squarefree.mp h.squarefree q hq (by rwa [← pow_two])

/--
@isnad1 id=not.1h2v.s4.fd0a6e4108fb from=translated src=- shape=5cb2c717 vocab=bdf4f7f0
-/
theorem not_four_dvd (h : P.IsConductorLevel N) : ¬ 4 ∣ N := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  exact h4 ▸ h.sq_not_dvd Nat.prime_two

end IsConductorLevel

end Tengoku.FltAnthropic.FreyPackage
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
