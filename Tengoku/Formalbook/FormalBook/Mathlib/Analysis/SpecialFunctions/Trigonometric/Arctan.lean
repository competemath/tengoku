import Tengoku
namespace Tengoku.Formalbook end Tengoku.Formalbook open Tengoku.Formalbook
open Real

/--
@isnad1 id=eq.0h0v.s4.7f2ee168ba10 from=translated src=- shape=f594d0c5 vocab=54a8e687
-/
@[simp, nolint simpNF]
theorem _root_.Tengoku.Formalbook.arctan_sqrt_three : arctan (√3) = π / 3 := by
  rw [←tan_pi_div_three, arctan_tan]
  all_goals
  · field_simp
    norm_num
-- Tengoku: root names of this library moved to Tengoku.Formalbook so they do not collide with other libraries (generated)
