-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._011: verified translations of equational_theories/Generated/MagmaEgg/small/_011.lean (2 theorems)
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

theorem Equation4176_implies_Equation3404 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3404 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := R v0
  have h3 := R x
  have h4 := h v1 v0 v1
  have h5 := R v1
  have h6 := h v0 v1 v1
  have h7 := h v1 y v0
  have h8 := R y
  let v9 := M z v1
  have h10 := h y v0 v9
  have h11 := h v9 (M v0 v9) y
  have h12 := R v9
  have h13 := h z x x
  have h14 := S h13
  have h15 := R z
  have h16 := h x x z
  have h17 := h x z x
  have h18 := S h17
  have h19 := h x v0 x
  let v20 := M x v0
  have h21 := h v20 z x
  have h22 := h v0 v20 z
  have h23 := h z x v0
  have h24 := h z x y
  have h25 := S h24
  let v26 := M x y
  have h27 := h y v26 z
  have h28 := C (T (T (T (T (C (T (C h24 h15) (S h27)) h3) (C (T (T (T h27 (C h25 h15)) (C h23 h15)) (S h22)) h3)) (S h21)) (C (T h19 (C h18 h3)) h15)) (S h16)) h15
  have h29 := h x v0 z
  have h30 := S h19
  have h31 := h x z v1
  have h32 := h v1 v9 x
  have h33 := h x v1 v9
  have h34 := h (M x v1) z v1
  have h35 := h z x v1
  let v36 := M v0 v1
  have h37 := S h29
  have h38 := C (T (T (T h16 (C (T (C h17 h3) h30) h15)) h21) (C (T h22 (C (S h23) h15)) h3)) h15
  have h39 := C (T h38 h37) h3
  let v40 := M v26 z
  have h41 := T h4 (C (T (C (T (T (T h6 (C (S h7) h5)) (C (T (T (C h10 h8) (S h11)) (C h12 (T (C (T h13 (C (T (T (T (T h38 h37) h19) (C (T h18 h31) h3)) (S h32)) h3)) h12) (S h33)))) h5)) (S h34)) h5) (S h35)) h5)
  T (T (T (h x y v1) (h (M (M y v1) x) v1 v0)) (C (T (T (T (C h41 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (h y v1 v0) (C (T (T (C h41 h8) (C (C h24 h5) h8)) (S (h v1 v40 y))) h2)) (S (h v40 y v0))) h25) h13) h39) (C (h x v0 v1) h3)) (S (h v1 v36 x))) (h v1 v36 y)) (C (S (h y v0 v1)) h8)) (C (h y v0 v0) h8)) (S (h v0 (M v0 v0) y))) (C h2 (T (C (T h13 h39) h2) (S (h x x v0))))) h3) (S (h (M x x) z x))) h38) h37)) (h v36 v20 x)) (C (C (T (C (T h29 h28) h3) h14) (T (C (T h35 (C (T (T (T h34 (C (T (T (C h12 (T h33 (C (T (C (T (T (T (T h32 (C (T (S h31) h17) h3)) h30) h29) h28) h3) h14) h12))) h11) (C (S h10) h8)) h5)) (C h7 h5)) (S h6)) h5)) h5) (S h4))) h3)) (S (h (M v1 v0) z x))) h2)) (S (h z v1 v0))

theorem Equation3131_implies_Equation759 (G: Type _) [Magma G] (h: Equation3131 G) : Equation759 G
:= fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h v3 v2 v0
  have h5 := S h4
  have h6 := R v1
  have h7 := h z v0 v0
  have h8 := h v0 v1 v0
  have h9 := T h8 (C (S h7) h6)
  have h10 := T (C h7 h6) (S h8)
  have h11 := R v0
  have h12 := R v3
  have h13 := h v2 y y
  have h14 := C (S h13) h12
  have h15 := h y v3 y
  have h16 := C (T h15 h14) h11
  have h17 := C h16 h10
  have h18 := S h15
  have h19 := C h13 h12
  have h20 := C (T h19 h18) h11
  have h21 := h y v3 v3
  have h22 := S h21
  have h23 := R y
  have h24 := R v2
  have h25 := C h17 h24
  have h26 := C (T h25 h5) h23
  have h27 := h v0 y v2
  have h28 := C (T (T (T (C (C (C (T h27 h26) h12) h12) h12) h22) h15) h14) h11
  have h29 := h v3 v0 v3
  have h30 := C (T (T h29 h28) h20) h9
  have h31 := C (T (T (T (T (T (C h30 h9) h25) h5) h29) h28) h20) h9
  have h32 := S h29
  have h33 := S h27
  have h34 := C h20 h9
  have h35 := C h34 h24
  have h36 := C (T h4 h35) h23
  have h37 := C (T (T (T h19 h18) h21) (C (C (C (T h36 h33) h12) h12) h12)) h11
  have h38 := C (T (T h16 h37) h32) h10
  have h39 := C h38 h10
  have h40 := h v3 y v3
  have h41 := h v0 v3 v0
  have h42 := S h41
  have h43 := C (T h30 (C (T (T (T (T (T h16 h37) h32) h4) h35) h39) h10)) h12
  have h44 := C (C (T (T (T h43 h42) h27) h26) h12) h12
  have h45 := h v0 v3 v3
  have h46 := C (T (T (T h43 h42) h45) h44) h12
  have h47 := C (T h46 h22) h12
  have h48 := C (T h31 h38) h12
  have h49 := C (C (T (T (T h36 h33) h41) h48) h12) h12
  have h50 := C (T (T (T (T (C (T h45 (C (T h46 (C (T h49 h47) h12)) h12)) h23) (S h40)) h4) h35) h39) h10
  have h51 := S h45
  have h52 := C (T (T (T h49 h51) h41) h48) h12
  have h53 := C (T (C (T h21 h52) h12) h44) h12
  have h54 := R x
  T (T (h x v0 v3) (C (T (T (T (T (T (T (T (C (T (T (T (C (C (T (h v0 x v0) (C (T (T (C (C (T (T (T (C (h x y y) h11) (S (h y v0 y))) h15) h14) h11) h11) h34) h38) h54)) h54) h12) (S (h v0 v3 x))) h45) h47) h12) h53) h22) (h y v0 v2)) (C (T (T (T (T (C (T h50 h31) h24) h25) h5) h40) (C (T (C (T h53 h52) h12) h51) h23)) h9)) h50) h31) h17) h9)) h5

end EquationalTheories
