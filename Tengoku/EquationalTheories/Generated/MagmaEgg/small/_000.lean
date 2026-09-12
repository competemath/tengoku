-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._000: verified translations of equational_theories/Generated/MagmaEgg/small/_000.lean (2 theorems)
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.EquationalTheories.Deps

set_option linter.all false

namespace EquationalTheories

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

theorem Equation3715_implies_Equation4470 (G: Type _) [Magma G] (h: Equation3715 G) : Equation4470 G
:= fun x y =>
  T (T (h x (M y y)) (C (h x x) (S (h y y)))) (S (h (M x x) y))

theorem Equation692_implies_Equation1358 (G: Type _) [Magma G] (h: Equation692 G) : Equation1358 G
:= fun x y z =>
  let v0 := M (M z x) z
  T (h x y v0) (C (R y) (S (h (M v0 y) x z)))

end EquationalTheories
