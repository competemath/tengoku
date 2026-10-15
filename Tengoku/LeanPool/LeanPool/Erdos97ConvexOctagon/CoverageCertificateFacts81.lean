/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 5).
@isnad1 id=eq.0h0v.s5.4f41d1e22c80 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_05 :
    branchClaimRootValidB 4 5 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 16).
@isnad1 id=eq.0h0v.s5.d3f11509bfa8 from=translated src=- shape=e9e0773c vocab=10d93bdb
-/
theorem coverageBranchRoot_6_16 :
    branchClaimRootValidB 6 16 (.search branchClaims6Row16) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 15), starting at 64.
@isnad1 id=eq.0h0v.s3.e8bea19c6558 from=translated src=- shape=6f582f20 vocab=ef6c3d63
-/
theorem coverageBranchNodes_6_15_00064 :
    nodeClaimChunkValidB branchClaims6Row15 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 15), starting at 128.
@isnad1 id=eq.0h0v.s3.d212726abdd2 from=translated src=- shape=6f582f20 vocab=ef6c3d63
-/
theorem coverageBranchNodes_6_15_00128 :
    nodeClaimChunkValidB branchClaims6Row15 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 15), starting at 192.
@isnad1 id=eq.0h0v.s3.d4240b9c0dd9 from=translated src=- shape=6f582f20 vocab=ef6c3d63
-/
theorem coverageBranchNodes_6_15_00192 :
    nodeClaimChunkValidB branchClaims6Row15 192 9 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 16), starting at 0.
@isnad1 id=eq.0h0v.s3.f27e4ee8d1c9 from=translated src=- shape=6f582f20 vocab=2feb8b88
-/
theorem coverageBranchNodes_6_16_00000 :
    nodeClaimChunkValidB branchClaims6Row16 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
