-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._007: verified translations of equational_theories/Generated/MagmaEgg/small/_007.lean (1 theorem)
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

theorem Equation711_implies_Equation725 (G: Type _) [Magma G] (h: Equation711 G) : Equation725 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := S (h v1 v1 x)
  let v3 := M v1 (M (M v1 x) x)
  have h4 := R y
  let v5 := M z (M v0 x)
  have h6 := h z v0 v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h z z x
  have h10 := R v0
  have h11 := C h10 (C h10 (T h9 (C h9 h8)))
  have h12 := R x
  have h13 := S h9
  have h14 := C h10 (C (C (T h6 (C h10 (C h10 (T (C h13 h8) h13)))) h12) h12)
  have h15 := S (h x x x)
  let v16 := M x (M (M x x) x)
  have h17 := C h10 (C h10 (T (C h15 (R v16)) h15))
  have h18 := h x v0 v16
  T (T (T (T (T h18 h17) h14) (C h10 (T (T (T (C (C (T h11 h7) h12) (T (T h18 h17) h14)) (S (h (M v0 v1) v0 x))) h11) h7))) (h v1 y v3)) (C h4 (C h4 (T (C h2 (R v3)) h2)))

end EquationalTheories
