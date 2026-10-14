/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 7).
@isnad1 id=eq.0h0v.s5.f904751232e3 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_07 :
    branchClaimRootValidB 3 7 (.patternThree 2) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 25).
@isnad1 id=eq.0h0v.s5.015abe0321a7 from=translated src=- shape=e9e0773c vocab=3ff1596c
-/
theorem coverageBranchRoot_5_25 :
    branchClaimRootValidB 5 25 (.search branchClaims5Row25) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 25), starting at 0.
@isnad1 id=eq.0h0v.s3.cbed5e6b0c5e from=translated src=- shape=6f582f20 vocab=0ab4b116
-/
theorem coverageBranchNodes_5_25_00000 :
    nodeClaimChunkValidB branchClaims5Row25 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 25), starting at 64.
@isnad1 id=eq.0h0v.s3.1d00b0b79383 from=translated src=- shape=6f582f20 vocab=0ab4b116
-/
theorem coverageBranchNodes_5_25_00064 :
    nodeClaimChunkValidB branchClaims5Row25 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 25), starting at 128.
@isnad1 id=eq.0h0v.s3.4b69b2c7d4ec from=translated src=- shape=6f582f20 vocab=0ab4b116
-/
theorem coverageBranchNodes_5_25_00128 :
    nodeClaimChunkValidB branchClaims5Row25 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 25), starting at 192.
@isnad1 id=eq.0h0v.s3.958c0fcfdd20 from=translated src=- shape=6f582f20 vocab=0ab4b116
-/
theorem coverageBranchNodes_5_25_00192 :
    nodeClaimChunkValidB branchClaims5Row25 192 31 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
