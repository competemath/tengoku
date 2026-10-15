/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 2).
@isnad1 id=eq.0h0v.s5.5e177365bc71 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_02 :
    branchClaimRootValidB 1 2 (.patternThree 178) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 25), starting at 64.
@isnad1 id=eq.0h0v.s3.f83bcca3a6c6 from=translated src=- shape=6f582f20 vocab=8f57ad29
-/
theorem coverageBranchNodes_3_25_00064 :
    nodeClaimChunkValidB branchClaims3Row25 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 25), starting at 128.
@isnad1 id=eq.0h0v.s3.9b985d74afc4 from=translated src=- shape=6f582f20 vocab=8f57ad29
-/
theorem coverageBranchNodes_3_25_00128 :
    nodeClaimChunkValidB branchClaims3Row25 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 25), starting at 192.
@isnad1 id=eq.0h0v.s3.e3035de1faa2 from=translated src=- shape=6f582f20 vocab=8f57ad29
-/
theorem coverageBranchNodes_3_25_00192 :
    nodeClaimChunkValidB branchClaims3Row25 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 25), starting at 256.
@isnad1 id=eq.0h0v.s3.2c09e756730b from=translated src=- shape=6f582f20 vocab=8f57ad29
-/
theorem coverageBranchNodes_3_25_00256 :
    nodeClaimChunkValidB branchClaims3Row25 256 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
