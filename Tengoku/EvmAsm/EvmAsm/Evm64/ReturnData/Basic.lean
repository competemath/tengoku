/-
  EvmAsm.Evm64.ReturnData.Basic

  Pure returndata helpers for RETURNDATACOPY executable-spec bridges
  (GH #107 / GH #114).
-/

-- (No `import EvmAsm.Evm64.Basic`: this module only uses `BitVec 8`,
-- not anything from `Evm64.Basic`; dropped per shake hygiene, slice of #1045.)

module

@[expose] public section
namespace EvmAsm.Evm64
namespace ReturnData

/-- Read one returndata byte, returning zero past the end of the buffer.-/
def byte (data : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < data.length then data[idx] else 0

/-- Bytes written by RETURNDATACOPY:
    `size` bytes from `data` starting at `dataOffset`, with out-of-bounds
    reads producing zero. Distinctive token: ReturnData.copyBytes #107 #114.-/
def copyBytes
    (data : List (BitVec 8)) (dataOffset size : Nat) : List (BitVec 8) :=
  (List.range size).map (fun i => byte data (dataOffset + i))

/--
@isnad1 id=eq.1h2v.s6.495eb5051593 from=translated src=- shape=537e03bc vocab=12b2b603
-/
theorem byte_of_lt {data : List (BitVec 8)} {idx : Nat}
    (h : idx < data.length) :
    byte data idx = data[idx] := by
  simp [byte, h]

/--
@isnad1 id=eq.1h2v.s5.8160d3d6daaa from=translated src=- shape=e6661f4e vocab=68738510
-/
theorem byte_of_ge {data : List (BitVec 8)} {idx : Nat}
    (h : data.length ≤ idx) :
    byte data idx = 0 := by
  simp [byte, show ¬idx < data.length from by omega]

/--
@isnad1 id=eq.0h1v.s5.d4bb7ba108af from=translated src=- shape=bb7fe741 vocab=8825dc3a
-/
@[simp] theorem byte_nil (idx : Nat) :
    byte [] idx = 0 := by
  exact byte_of_ge (data := []) (idx := idx) (by simp)

/--
@isnad1 id=eq.0h3v.s4.8e9b7672ed4a from=translated src=- shape=f4dcf33e vocab=c037c49b
-/
@[simp] theorem copyBytes_length
    (data : List (BitVec 8)) (dataOffset size : Nat) :
    (copyBytes data dataOffset size).length = size := by
  simp [copyBytes]

/--
@isnad1 id=eq.0h2v.s5.85b4991f6a0d from=translated src=- shape=7d8017ca vocab=60c7d1a8
-/
@[simp] theorem copyBytes_zero
    (data : List (BitVec 8)) (dataOffset : Nat) :
    copyBytes data dataOffset 0 = [] := by
  simp [copyBytes]

/--
@isnad1 id=eq.1h4v.s6.474bc00d53f2 from=translated src=- shape=32b007db vocab=297c0b16
-/
theorem copyBytes_get
    {data : List (BitVec 8)} {dataOffset size i : Nat}
    (h : i < size) :
    (copyBytes data dataOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = byte data (dataOffset + i) := by
  simp [copyBytes]

/--
@isnad1 id=eq.2h4v.s7.7e771fc33629 from=translated src=- shape=0b567736 vocab=7cf61355
-/
theorem copyBytes_get_of_in_bounds
    {data : List (BitVec 8)} {dataOffset size i : Nat}
    (h : i < size)
    (hsrc : dataOffset + i < data.length) :
    (copyBytes data dataOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = data[dataOffset + i] := by
  rw [copyBytes_get h, byte_of_lt hsrc]

/--
@isnad1 id=eq.2h4v.s6.64ccde577a28 from=translated src=- shape=ed77eae0 vocab=ccaaded3
-/
theorem copyBytes_get_of_out_of_bounds
    {data : List (BitVec 8)} {dataOffset size i : Nat}
    (h : i < size)
    (hsrc : data.length ≤ dataOffset + i) :
    (copyBytes data dataOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = 0 := by
  rw [copyBytes_get h, byte_of_ge hsrc]

/--
@isnad1 id=eq.0h2v.s5.5e100c738431 from=translated src=- shape=a3ffc0a1 vocab=5cac09c4
-/
@[simp] theorem copyBytes_nil (dataOffset size : Nat) :
    copyBytes [] dataOffset size = List.replicate size 0 := by
  simp [copyBytes, List.map_const']

end ReturnData
end EvmAsm.Evm64
