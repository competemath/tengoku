/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 15).
@isnad1 id=eq.0h0v.s5.fdb4d6bba540 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_15 :
    branchClaimRootValidB 0 15 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 33).
@isnad1 id=eq.0h0v.s5.c4bdf4590e0e from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_33 :
    branchClaimRootValidB 4 33 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 5).
@isnad1 id=eq.0h0v.s5.8e18b856cabf from=translated src=- shape=e9e0773c vocab=75b2a716
-/
theorem coverageBranchRoot_2_05 :
    branchClaimRootValidB 2 5 (.search branchClaims2Row5) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 6).
@isnad1 id=eq.0h0v.s5.94f9c9eb076f from=translated src=- shape=e9e0773c vocab=90ca6a13
-/
theorem coverageBranchRoot_2_06 :
    branchClaimRootValidB 2 6 (.search branchClaims2Row6) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 4), starting at 64.
@isnad1 id=eq.0h0v.s3.1391f565b205 from=translated src=- shape=6f582f20 vocab=354d6409
-/
theorem coverageBranchNodes_2_04_00064 :
    nodeClaimChunkValidB branchClaims2Row4 64 50 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 5), starting at 0.
@isnad1 id=eq.0h0v.s3.5a6ebd2629ce from=translated src=- shape=6f582f20 vocab=d6ff5178
-/
theorem coverageBranchNodes_2_05_00000 :
    nodeClaimChunkValidB branchClaims2Row5 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 5), starting at 64.
@isnad1 id=eq.0h0v.s3.9756dcbcdad8 from=translated src=- shape=6f582f20 vocab=d6ff5178
-/
theorem coverageBranchNodes_2_05_00064 :
    nodeClaimChunkValidB branchClaims2Row5 64 61 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 6), starting at 0.
@isnad1 id=eq.0h0v.s3.358beb19f07b from=translated src=- shape=6f582f20 vocab=02e96baa
-/
theorem coverageBranchNodes_2_06_00000 :
    nodeClaimChunkValidB branchClaims2Row6 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
