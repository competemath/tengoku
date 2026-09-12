-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._006: verified translations of equational_theories/Generated/MagmaEgg/small/_006.lean (2 theorems)
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

theorem Equation1790_implies_Equation3607 (G: Type _) [Magma G] (h: Equation1790 G) : Equation3607 G
:= fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 v0
  let v4 := M v0 v1
  let v5 := M z v2
  have h6 := h z x y
  have h7 := S h6
  have h8 := h y v2 x
  have h9 := R (M v2 x)
  have h10 := R v5
  have h11 := h x z v2
  T (T (h v0 v5 y) (C (T (T (C h10 (T h8 (C h9 h7))) (S h11)) (h x v0 v1)) (T (T (T (C (R (M y v0)) (T (h v5 v0 y) (C (R (M v0 y)) (T (C (R (M y v5)) (C (T h11 (C h10 (T (C h9 h6) (S h8)))) (R y))) (S (h y y v5)))))) (S (h y y v0))) (h y v1 x)) (C (T (h v2 v2 v0) (C (R v3) (C h7 (R v2)))) (R v4))))) (S (h v5 v4 v3))

theorem Equation1333_implies_Equation2 (G: Type _) [Magma G] (h: Equation1333 G) : Equation2 G
:= fun x y =>
  let v0 := M (M x y) x
  let v1 := M v0 x
  have h2 := R x
  have h3 := h x x y
  let v4 := M x x
  let v5 := M (M v4 v4) x
  have h6 := h v4 x x
  let v7 := M v4 x
  let v8 := M v7 x
  let v9 := M (M v4 v0) x
  have h10 := h x x x
  have h11 := S h10
  let v12 := M (M v4 v7) x
  T (T (h x x v1) (C h2 (T (T (T (T (T (C (C (S h3) h2) h2) (h v7 x v5)) (C h2 (T (T (T (C (C (S h6) (R v7)) h2) (h v12 x v8)) (C h2 (C (T (C h11 (R v12)) (S (h v7 x x))) h2))) h11))) (C h2 (T (T (T h3 (C h2 (C (T (h v0 x x) (C h10 (R v9))) h2))) (S (h v9 x v8))) (C (C h6 (R v0)) h2)))) (S (h v0 x v5))) (C (C h3 (R y)) h2)))) (S (h y x v1))

end EquationalTheories
