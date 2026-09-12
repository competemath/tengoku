-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._001: verified translations of equational_theories/Generated/MagmaEgg/small/_001.lean (8 theorems)
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

theorem Equation2737_implies_Equation1722 (G: Type _) [Magma G] (h: Equation2737 G) : Equation1722 G
:= fun x y =>
  let v0 := M x y
  let v1 := M y y
  T (T (h x y) (C (C (R v1) (h v0 y)) (R y))) (S (h (M v1 (M v0 y)) y))

theorem Equation3124_implies_Equation2 (G: Type _) [Magma G] (h: Equation3124 G) : Equation2 G
:= fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (T (h x v0 y) (C (S (h y x x)) h1)) (C (h y x y) h1)) (S (h y v0 y))

theorem Equation3751_implies_Equation3724 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3724 G
:= fun x y =>
  let v0 := M y x
  have h1 := h x y
  T h1 (C (T (T (T (h y x) (C h1 h1)) (S (h v0 v0))) (S h1)) (R v0))

theorem Equation3751_implies_Equation3749 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3749 G
:= fun x y =>
  have h0 := h x y
  let v1 := M y x
  T h0 (C (R v1) (T (T (T (h y x) (C h0 h0)) (S (h v1 v1))) (S h0)))

theorem Equation3932_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3932 G) : Equation3729 G
:= fun x y z =>
  let v0 := M z z
  T (h x y v0) (C (T (T (h x (M y v0) z) (C (C (R x) (S (h y z z))) (R z))) (S (h x y z))) (R v0))

theorem Equation4229_implies_Equation3537 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3537 G
:= fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (T (h x y z) (C (T (h v0 y z) (h v1 v0 z)) (R x))) (S (h x v1 v0))

end EquationalTheories
