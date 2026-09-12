-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._001: verified translations of equational_theories/Generated/MagmaEgg/small/_001.lean (2 theorems)
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

theorem Equation2673_implies_Equation2064 (G: Type _) [Magma G] (h: Equation2673 G) : Equation2064 G
:= fun x y =>
  let v0 := M y y
  let v1 := M x y
  T (T (h x y) (C (C (h v1 y) (R v0)) (R y))) (S (h (M (M v1 y) v0) y))

end EquationalTheories
