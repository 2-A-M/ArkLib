/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb01Step
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Step
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Step
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb34Step

/-!
# CO25 Lemma 5.1 — round-2 frontier: the eager key lemma from the finest lane residuals

Round 1 (`KeyLemmaAssembly.keyLemmaEager_of_hybSteps`) reduced `KeyLemmaEagerResidual` to
the four hybrid-step residuals (Claims 5.21–5.24), with the Lemma 5.1 witness budgets
(M1c/M1d) discharged by `SimulatorBudgets`. Round 2 ran one lane per step; **no step closed
outright**, but every step now carries a *proven* split skeleton onto strictly finer named
residuals:

- **Claim 5.21** (`Hyb01Step.hyb01Step_of_offEventCoupling_of_freshSplit`):
  `Hyb01OffEventCouplingResidual` (off-`E` BackTrack coupling) + `DDSFreshSwitchResidual εsw`
  (eager-lazy carrier switch) + `FreshTraceEventResidual εev` (fresh-world event
  decomposition) + `εsw + εev ≤ lemma5_8Bound` ⟹ `Hyb01StepResidual`.
- **Claim 5.22** (`Hyb12Step.hyb12Step_of_resampleSplit`):
  `Hyb12ResampleAlignResidual` (fiber-resample alignment, `= 0`) +
  `Hyb12BiasAccountingResidual` (decoding-bias accounting through `Hyb12Mid`)
  ⟹ `Hyb12StepResidual`.
- **Claim 5.23** (`Hyb23Step.hyb23Step_of_saltedSplit`):
  `Hyb23DecodedQueryResidual` (the paper's query re-format, `= 0`) +
  `Hyb23MemoTransparencyResidual` (`tr_i` memo transparency) +
  `Hyb23SaltErasureResidual` (salt erasure onto the unsalted FS oracle)
  ⟹ `Hyb23StepResidual`.
- **Claim 5.24** (`Hyb34Step.hyb34Step_of_divergence_collapse`):
  `Hyb34DivergenceResidual` (`Δ(Hyb₃, Hyb3Strict) ≤ claim5_24Bound/2`) +
  `Hyb34CollapseResidual` (`Δ(Hyb3Strict, Hyb₄) ≤ claim5_24Bound/2`)
  ⟹ `Hyb34StepResidual`.

This module composes the four skeletons with the round-1 assembly into the tightest honest
top-level theorems:

- `keyLemmaEager_of_finestResiduals` — **the round-2 frontier**: the nine finest open
  residuals (with the `(εsw, εev)` Lemma 5.8 budget split) imply the full eager key lemma.
- `keyLemmaEager_of_birthdayLanes` — the Claim 5.21 lane consumed at the coarser round-1
  granularity (`BirthdayBound.Lemma5_8EagerBirthdayResidual` unsplit), for a worker who
  closes Lemma 5.8 directly.

## Honest caveats (carried from the lane headers — read before attacking a residual)

- `Hyb23SaltErasureResidual` appears **genuinely false for `δ > 0`** (salt-grinding
  distinguisher: `eSpec` keys on the salt, the erased surface does not) — CO25 never erases
  the salt; its Hyb₃/Hyb₄/Lemma 5.1 stay on `fsChallengeOracle (StmtIn × Salt)`. This is a
  structural decision point for the eager ladder (restrict to `δ = 0`, or re-key
  `KeyLemmaEagerResidual` on salted statements), not a proof obligation to brute-force.
- `Hyb23MemoTransparencyResidual`'s exact-`0` form is likewise doubtful (repeat-key raw
  squeeze re-exposure is a positive-probability birthday event); CO25 introduces the memo
  only inside D2SAlgo/Hyb₄.
- The symmetric Claim 5.24 split is satisfiable only for `1 ≤ L`
  (`Hyb34Step.claim5_24Bound_nonneg`): at `L = 0` the CO25 Eq. 55 bound is negative.
- Off the critical path, the M2 residuals (`Lemma5_12/5_14/5_16HonestResidual`) feed the
  `E`-mass analyses of both `FreshTraceEventResidual` and `Hyb34DivergenceResidual` via
  `BirthdayBound.probEvent_honestBad_le_probEvent_E`. **Round-3 update**: the raw-trace
  5.12 surface is machine-checked false
  (`BacktrackLemmas.lemma5_12HonestResidual_not_universal`); consume the dedup'd-trace
  channel instead, which is M2-free
  (`KeyLemmaFrontierRound3.probEvent_honestBadDedup_le_probEvent_E`, hypothesis-free fold
  of the proven `lemma5_1{2,4,6}Honest_of_noRedundant` cores).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.KeyLemmaFrontier

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

-- The two theorems share one DSFS-wide variable block; each hypothesis uses only a slice
-- of it (repo precedent: the sibling lane modules).
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- **The round-2 frontier** (CO25 Lemma 5.1, eager surface): the finest open residuals of
the four lanes imply the full eager key lemma. Composes, lane by lane,
`Hyb01Step.hyb01Step_of_offEventCoupling_of_freshSplit`,
`Hyb12Step.hyb12Step_of_resampleSplit`, `Hyb23Step.hyb23Step_of_saltedSplit` and
`Hyb34Step.keyLemmaEager_of_steps_divergenceCollapse` (which already routes through
`KeyLemmaAssembly.keyLemmaEager_of_hybSteps`, witness budgets discharged). Every reduction
consumed here is proven and axiom-clean; the nine hypotheses are exactly the remaining
open mathematics. -/
theorem keyLemmaEager_of_finestResiduals
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp)
    -- Claim 5.21 lane (Lemma 5.8 fresh-split granularity)
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
    -- Claim 5.22 lane
    (h12A : Hyb12Step.Hyb12ResampleAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h12B : Hyb12Step.Hyb12BiasAccountingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    -- Claim 5.23 lane
    (h23A : Hyb23Step.Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23B : Hyb23Step.Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23C : Hyb23Step.Hyb23SaltErasureResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    -- Claim 5.24 lane
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  Hyb34Step.keyLemmaEager_of_steps_divergenceCollapse T_H T_P δ Salt oImpl
    (Hyb01Step.hyb01Step_of_offEventCoupling_of_freshSplit T_H T_P δ oImpl h01C
      εsw εev h01sw h01ev h01sum)
    (Hyb12Step.hyb12Step_of_resampleSplit T_H T_P δ oImpl h12A h12B)
    (Hyb23Step.hyb23Step_of_saltedSplit T_H T_P δ Salt oImpl h23A h23B h23C)
    h34A h34B

/-- The round-2 frontier with the Claim 5.21 lane at the coarser round-1 granularity:
`BirthdayBound.Lemma5_8EagerBirthdayResidual` consumed unsplit (via
`Hyb01Step.hyb01Step_of_offEventCoupling_of_birthday`) instead of the `(εsw, εev)`
fresh-split. Useful for a worker who closes CO25 Lemma 5.8 in one piece. -/
theorem keyLemmaEager_of_birthdayLanes
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp)
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h58 : BirthdayBound.Lemma5_8EagerBirthdayResidual StmtIn U)
    (h12A : Hyb12Step.Hyb12ResampleAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h12B : Hyb12Step.Hyb12BiasAccountingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h23A : Hyb23Step.Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23B : Hyb23Step.Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23C : Hyb23Step.Hyb23SaltErasureResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  Hyb34Step.keyLemmaEager_of_steps_divergenceCollapse T_H T_P δ Salt oImpl
    (Hyb01Step.hyb01Step_of_offEventCoupling_of_birthday T_H T_P δ oImpl h01C h58)
    (Hyb12Step.hyb12Step_of_resampleSplit T_H T_P δ oImpl h12A h12B)
    (Hyb23Step.hyb23Step_of_saltedSplit T_H T_P δ Salt oImpl h23A h23B h23C)
    h34A h34B

end DuplexSpongeFS.KeyLemmaFrontier

#print axioms DuplexSpongeFS.KeyLemmaFrontier.keyLemmaEager_of_finestResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontier.keyLemmaEager_of_birthdayLanes

end
