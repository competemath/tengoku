/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 29).
@isnad1 id=eq.0h0v.s5.3d5f7aca3e96 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_29 :
    branchClaimRootValidB 3 29 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 1).
@isnad1 id=eq.0h0v.s5.c6558528de80 from=translated src=- shape=e9e0773c vocab=6606ecc6
-/
theorem coverageBranchRoot_6_01 :
    branchClaimRootValidB 6 1 (.search branchClaims6Row1) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 320.
@isnad1 id=eq.0h0v.s3.3181c41e48ac from=translated src=- shape=6f582f20 vocab=fbc3c659
-/
theorem coverageBranchNodes_5_34_00320 :
    nodeClaimChunkValidB branchClaims5Row34 320 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 384.
@isnad1 id=eq.0h0v.s3.d4fdfbcbbf4c from=translated src=- shape=6f582f20 vocab=fbc3c659
-/
theorem coverageBranchNodes_5_34_00384 :
    nodeClaimChunkValidB branchClaims5Row34 384 6 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 1), starting at 0.
@isnad1 id=eq.0h0v.s3.525c7b6ae115 from=translated src=- shape=6f582f20 vocab=13534537
-/
theorem coverageBranchNodes_6_01_00000 :
    nodeClaimChunkValidB branchClaims6Row1 0 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 1), starting at 32.
@isnad1 id=eq.0h0v.s3.0ca7654fd2dd from=translated src=- shape=6f582f20 vocab=13534537
-/
theorem coverageBranchNodes_6_01_00032 :
    nodeClaimChunkValidB branchClaims6Row1 32 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
