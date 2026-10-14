/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 9).
@isnad1 id=eq.0h0v.s5.989b2cf4db42 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_09 :
    branchClaimRootValidB 0 9 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 27).
@isnad1 id=eq.0h0v.s5.7495ac125f7b from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_27 :
    branchClaimRootValidB 4 27 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 31).
@isnad1 id=eq.0h0v.s5.ca46d7cabc4b from=translated src=- shape=e9e0773c vocab=f8ab0a71
-/
theorem coverageBranchRoot_1_31 :
    branchClaimRootValidB 1 31 (.search branchClaims1Row31) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 192.
@isnad1 id=eq.0h0v.s3.8cdc85cdc4e9 from=translated src=- shape=6f582f20 vocab=606d8a49
-/
theorem coverageBranchNodes_1_30_00192 :
    nodeClaimChunkValidB branchClaims1Row30 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 256.
@isnad1 id=eq.0h0v.s3.e0619577cbe6 from=translated src=- shape=6f582f20 vocab=606d8a49
-/
theorem coverageBranchNodes_1_30_00256 :
    nodeClaimChunkValidB branchClaims1Row30 256 19 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 31), starting at 0.
@isnad1 id=eq.0h0v.s3.ae739eaaefe6 from=translated src=- shape=6f582f20 vocab=83b05302
-/
theorem coverageBranchNodes_1_31_00000 :
    nodeClaimChunkValidB branchClaims1Row31 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 31), starting at 64.
@isnad1 id=eq.0h0v.s3.a2de43ffe16d from=translated src=- shape=6f582f20 vocab=83b05302
-/
theorem coverageBranchNodes_1_31_00064 :
    nodeClaimChunkValidB branchClaims1Row31 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
