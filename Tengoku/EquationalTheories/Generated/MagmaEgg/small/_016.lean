-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._016: verified translations of equational_theories/Generated/MagmaEgg/small/_016.lean (2 theorems)
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

theorem Equation522_implies_Equation1561 (G: Type _) [Magma G] (h: Equation522 G) : Equation1561 G
:= fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := h y z z
  have h5 := h v2 v2 v3
  have h6 := S h5
  have h7 := h v3 v1 v3
  have h8 := S h7
  have h9 := h v1 v3 v3
  have h10 := h v2 v3 v1
  have h11 := R v3
  have h12 := R v2
  have h13 := C h12 (T (C h11 h10) (S h9))
  have h14 := C h11 (C h11 h13)
  have h15 := h v3 v3 v2
  have h16 := R v1
  have h17 := C h16 (C h16 (T h15 h14))
  have h18 := C h16 (T (T (T h17 h8) h15) h14)
  have h19 := h v2 v1 v1
  have h20 := C h16 (T h19 h18)
  have h21 := C h12 (T h20 h8)
  have h22 := S h19
  have h23 := S h15
  have h24 := C h11 (C h11 (C h12 (T h9 (C h11 (S h10)))))
  have h25 := C h16 (T (T (T h24 h23) h7) (C h16 (C h16 (T h24 h23))))
  have h26 := C h16 (T h25 h22)
  have h27 := h v2 v3 v3
  have h28 := S h27
  have h29 := C h11 (C h11 h21)
  have h30 := h v1 v3 v2
  have h31 := C h16 (T (T (T (C h11 (T h30 h29)) h28) h19) h18)
  have h32 := C h12 (T h31 h26)
  have h33 := S h30
  have h34 := C h12 (T h7 h26)
  have h35 := C h11 (C h11 h34)
  have h36 := C h16 (T (T (T h25 h22) h27) (C h11 (T h35 h33)))
  have h37 := h v3 v2 v1
  have h38 := S h37
  have h39 := C h12 (T h20 h36)
  have h40 := C h12 h39
  have h41 := h v1 v2 v2
  have h42 := C h11 (T (T (T (T (T h35 h33) h41) (C h12 (T (T (T h40 h38) h7) h36))) h32) h21)
  have h43 := T h27 h42
  have h44 := C h12 (C h12 h43)
  have h45 := R z
  have h46 := h v2 z v2
  have h47 := C h45 (T (C h45 (T (T (T h44 h6) h46) (C h45 (C h45 (T h44 h6))))) (S h4))
  have h48 := h v2 v3 v0
  have h49 := S h48
  have h50 := S h46
  have h51 := S h41
  have h52 := C h12 h32
  have h53 := C h11 (T (T (T (T (T h34 h39) (C h12 (T (T (T h31 h8) h37) h52))) h51) h30) h29)
  have h54 := T h53 h28
  have h55 := C h12 (C h12 h54)
  have h56 := C h45 (T h4 (C h45 (T (T (T (C h45 (C h45 (T h5 h55))) h50) h5) h55)))
  have h57 := T h56 h50
  have h58 := R v0
  have h59 := C h58 (C h57 (T (T (T h44 h6) h46) h47))
  have h60 := h v2 v0 v2
  have h61 := h v2 v0 v3
  have h62 := S h61
  have h63 := T h46 h47
  have h64 := C h63 (C h58 h43)
  have h65 := C h11 (T (T (T h64 h62) h60) h59)
  have h66 := C h57 (C h58 h54)
  have h67 := C h11 (T (T (T h44 h6) h61) h66)
  have h68 := C h11 (T (T (T h53 h28) h5) h55)
  have h69 := C h57 (T (T (T h24 h23) h37) h52)
  have h70 := C h58 (T (T (T h31 h8) h15) h14)
  have h71 := C h11 (T (T (T (T (T (T (T (T (C h58 (T h7 h36)) h70) h69) h51) h30) h29) h68) h67) h65)
  have h72 := T (T (T h44 h6) h27) h42
  have h73 := T (T (T h64 h62) h5) h55
  have h74 := S h60
  have h75 := C h58 (C h63 (T (T (T h56 h50) h5) h55))
  have h76 := T (T (T h75 h74) h61) h66
  have h77 := C h11 (T (T (T (T (T (T (T (T (C h11 h76) (C h11 h73)) (C h11 h72)) h35) h33) h41) (C h63 (T (T (T h40 h38) h15) h14))) (C h58 (T (T (T h24 h23) h7) h36))) (C h58 (T h31 h8)))
  have h78 := C h58 (T (T (T (T (T (T (T (T (T (T (C h58 (T (T h13 h7) h36)) h70) h69) h51) h30) h29) h68) h67) h65) (C h11 (T (T (T h75 h74) h48) h77))) (C h11 (T (T (T h71 h49) h46) h47)))
  have h79 := h v3 v0 v2
  have h80 := S (h v0 x v3)
  have h81 := h v0 v1 v1
  have h82 := h x v1 v0
  have h83 := R x
  have h84 := C h83 (T (T (T (T (T (C h16 h82) (S h81)) h56) h50) h48) h77)
  T (T (h x v3 v1) (C h11 (C h11 (T (T (T (C h16 (T (T (T (C h83 (T (T (h v1 x x) (C h83 (T (T (T (C h83 h84) h80) h81) (C h16 (S h82))))) h84)) h80) (h v0 v1 v3)) (C h16 (T (T (T (T (T (T (T (C h16 (T (T (T h71 h49) h60) h59)) (C h16 h76)) (C h16 h73)) (C h16 h72)) (C h16 (T (T (T h53 h28) h19) (C h16 (T h17 h36))))) (S (h v3 v1 v1))) h79) h78)))) (S (h v3 v1 v0))) h79) h78)))) (S (h v3 v3 v0))

theorem Equation522_implies_Equation1943 (G: Type _) [Magma G] (h: Equation522 G) : Equation1943 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M x z
  have h3 := h v0 v1 v1
  have h4 := h y v1 v0
  have h5 := R v1
  have h6 := R y
  have h7 := C h6 (T (C h5 h4) (S h3))
  have h8 := R v2
  have h9 := C h6 (T h3 (C h5 (S h4)))
  have h10 := h v1 v1 y
  have h11 := S h10
  have h12 := C h5 (C h5 h9)
  have h13 := C h5 (C h5 h7)
  have h14 := h v1 v0 v1
  have h15 := S h14
  have h16 := R v0
  have h17 := C h16 (T (T (T (C h16 (C h16 (T h10 h13))) h15) h10) h13)
  have h18 := h y v0 v0
  have h19 := h y v1 v1
  have h20 := S h19
  have h21 := C h16 (T h18 h17)
  have h22 := C h6 (T h21 h15)
  have h23 := C h5 (C h5 h22)
  have h24 := h v0 v1 y
  have h25 := C h16 (T (T (T (C h5 (T h24 h23)) h20) h18) h17)
  have h26 := S h24
  have h27 := S h18
  have h28 := C h16 (T (T (T h12 h11) h14) (C h16 (C h16 (T h12 h11))))
  have h29 := C h16 (T h28 h27)
  have h30 := C h6 (T h14 h29)
  have h31 := C h5 (C h5 h30)
  have h32 := C h16 (T (T (T h28 h27) h19) (C h5 (T h31 h26)))
  have h33 := h v1 z v0
  have h34 := R z
  let v35 := M v1 v2
  have h36 := h z v35 y
  have h37 := S h36
  have h38 := h v0 y y
  have h39 := S h38
  have h40 := C h6 (T h25 h29)
  have h41 := h v1 y v0
  have h42 := C h6 (T (T (T h25 h15) h41) (C h6 h40))
  have h43 := C h6 (T h21 h32)
  have h44 := C h5 (T (T (T (T (T h30 h43) h42) h39) h24) h23)
  have h45 := T h44 h20
  have h46 := S h41
  have h47 := C h6 (T (T (T (C h6 h43) h46) h14) h32)
  have h48 := C h5 (T (T (T (T (T h31 h26) h38) h47) h40) h22)
  have h49 := h y y v1
  have h50 := S h49
  have h51 := T h19 h48
  have h52 := C h6 (C h6 h51)
  have h53 := C h6 (C h6 h45)
  have h54 := h y z z
  have h55 := h v0 v0 y
  have h56 := S h55
  have h57 := C h16 (C h16 (T (T h38 h47) h40))
  have h58 := h v0 z v0
  have h59 := R v35
  have h60 := C h59 (C h59 (T (T (T h25 h15) h41) (C h6 (T (T (T (T (T h42 h39) h58) (C h34 (T (T (T (C h34 (T (T (T h57 h56) h58) (C h34 (C h34 (T h57 h56))))) (S h54)) h49) h53))) (C h34 (T (T (T h52 h50) h19) h48))) (C h34 h45)))))
  have h61 := h v1 v35 v0
  have h62 := T (T h61 h60) h37
  have h63 := S h61
  have h64 := S h58
  have h65 := C h16 (C h16 (T (T h43 h42) h39))
  have h66 := C h59 (C h59 (T (T (T (C h6 (T (T (T (T (T (C h34 h51) (C h34 (T (T (T h44 h20) h49) h53))) (C h34 (T (T (T h52 h50) h54) (C h34 (T (T (T (C h34 (C h34 (T h55 h65))) h64) h55) h65))))) h64) h38) h47)) h46) h14) h32))
  have h67 := T (T h36 h66) h63
  have h68 := h v1 z y
  have h69 := S h68
  have h70 := C h34 (C h62 (T (T (T h36 h66) h63) h9))
  have h71 := C h34 (C h67 (T (T (T h7 h61) h60) h37))
  have h72 := h v1 x z
  have h73 := S h72
  have h74 := h z v2 v2
  have h75 := S h74
  have h76 := h x v2 z
  have h77 := C h8 h76
  have h78 := R x
  have h79 := C h78 (T (T (T (T (T (T h77 h75) h36) h66) h63) h68) h71)
  have h80 := C h8 (S h76)
  have h81 := h v2 x x
  have h82 := C h78 (T (T h81 (C h78 (T (T (T (T (T (T (C h78 h79) h73) h61) h60) h37) h74) h80))) h79)
  have h83 := h x v1 v2
  have h84 := C h78 (T (T (T (T (T (T h70 h69) h61) h60) h37) h74) h80)
  T h83 (C h5 (T (C h5 (T (T (T (C h8 (T (T (T h82 h73) (h v1 v2 z)) (C h8 (C h8 (T (T (T h70 h69) h72) (C h78 (T (T h84 (C h78 (T (T (T (T (T (T h77 h75) h36) h66) h63) h72) (C h78 h84)))) (S h81)))))))) (S (h x v2 v2))) h83) (C h5 (C h5 (T (T (T (T (T (C h8 (T (T (T h82 h73) h68) h71)) (C h8 (T (T (T h70 h69) h33) (C h67 (C h34 (T h25 h15)))))) (C h8 (T (T (T (C h62 (C h34 (T h14 h32))) (S h33)) h14) h32))) (C h8 (T (T (T h25 h15) h10) h13))) (C h8 (T (T h12 h11) h9))) (C h8 h7)))))) (S (h v2 v1 v1))))

end EquationalTheories
