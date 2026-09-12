-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._001: verified translations of equational_theories/Generated/MagmaEgg/small/_001.lean (1 theorem)
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

theorem Equation2558_implies_Equation31 (G: Type _) [Magma G] (h: Equation2558 G) : Equation31 G
:= fun x y =>
  let v0 := M x (M (M x x) x)
  T (h x v0 y) (C (T (C (R v0) (C (S (h y x x)) (R y))) (S (h (M y y) x x))) (R x))

end EquationalTheories
