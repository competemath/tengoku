-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._010: verified translations of equational_theories/Generated/MagmaEgg/small/_010.lean (1 theorem)
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

theorem Equation522_implies_Equation2925 (G: Type _) [Magma G] (h: Equation522 G) : Equation2925 G
:= fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := h y v1 v0
  have h5 := S h4
  have h6 := R v1
  have h7 := C h6 h5
  have h8 := h v0 v1 v1
  have h9 := h v0 y y
  have h10 := S h9
  have h11 := h y v0 v2
  have h12 := S h11
  have h13 := R (M v2 (M y v2))
  have h14 := S h8
  have h15 := C h6 h4
  have h16 := T h15 h14
  have h17 := h v1 v2 y
  have h18 := R v0
  have h19 := C h18 (T h17 (C h16 h13))
  have h20 := T h19 h12
  have h21 := C h16 h20
  have h22 := T h8 h7
  have h23 := C h18 (T (C h22 h13) (S h17))
  have h24 := T h11 h23
  have h25 := C h6 h24
  have h26 := C h6 (T (T h8 h7) h25)
  have h27 := C h22 (T (T (T h26 h5) h11) h23)
  have h28 := R y
  have h29 := h v1 y v0
  have h30 := h v1 v2 v0
  have h31 := C h6 h20
  have h32 := C h6 (T (T h31 h15) h14)
  have h33 := C h16 (T (T (T h19 h12) h4) h32)
  have h34 := R v2
  have h35 := h y v2 v0
  have h36 := C h22 h24
  have h37 := C h28 (T (T (T (T (T h36 h33) (C h22 (T (T (T h26 h5) h35) (C h34 h33)))) (S h30)) h29) (C h28 (C h28 (T h27 h21))))
  have h38 := R v3
  have h39 := R z
  have h40 := h v0 v0 x
  have h41 := h x v0 z
  have h42 := h z v0 v0
  have h43 := R x
  T (T (h x v3 z) (C h38 (C h38 (T (T (T (C h39 (T (T h40 (C h18 (C h18 (C h43 (T (C h18 h41) (S h42)))))) (C h22 (C h18 h22)))) (C h39 (T (T (T (T (T (C h16 (C h18 h16)) (C h18 (C h18 (C h43 (T h42 (C h18 (S h41))))))) (S h40)) h8) h7) h25))) (C h39 (T (T (T (T h31 h15) h14) h9) (C h28 (T (T (T (T (T (C h28 (C h28 (T h36 h33))) (S h29)) h30) (C h16 (T (T (T (C h34 h27) (S h35)) h4) h32))) h27) h21))))) (C h39 (T (T (T h37 h10) (h v0 v3 y)) (C h38 (T (C h38 (T (T (T (T h37 h10) h8) h7) (h v2 v3 z))) (S (h z v3 v3)))))))))) (S (h v3 v3 z))

end EquationalTheories
