/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 20).
@isnad1 id=eq.0h0v.s5.23bcc3f10bfb from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_20 :
    branchClaimRootValidB 3 20 (.patternThree 1) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 128.
@isnad1 id=eq.0h0v.s3.09799f9b04b7 from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00128 :
    nodeClaimChunkValidB branchClaims5Row32 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 192.
@isnad1 id=eq.0h0v.s3.ae1a9cb83581 from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00192 :
    nodeClaimChunkValidB branchClaims5Row32 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 256.
@isnad1 id=eq.0h0v.s3.f3f330ca1e83 from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00256 :
    nodeClaimChunkValidB branchClaims5Row32 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 320.
@isnad1 id=eq.0h0v.s3.602fadb20689 from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00320 :
    nodeClaimChunkValidB branchClaims5Row32 320 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
