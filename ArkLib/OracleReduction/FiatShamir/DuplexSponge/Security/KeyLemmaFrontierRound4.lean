/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Delta0Lift
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Decoded
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Budgets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12EagerLazy

/-!
# CO25 Lemma 5.1 — round-4 assembly: the ten-residual `δ = 0` frontier

Round 4 ran four lanes; **three round-3 residuals closed outright** and **four were
replaced by strictly finer cores with proven reductions**:

Closed outright (all 0-sorry, axiom-clean):

- **B1** `Hyb12Accounting.Hyb2FreshAlignResidual` — `Hyb12EagerLazy.hyb2FreshAlign_holds`
  (generic lazy-memo-table = eager-uniform-table CPS master theorem; any `δ`).
- **B3** `Hyb12Accounting.Hyb12ProverPipelineBudgetResidual` —
  `Hyb12Budgets.hyb12ProverPipelineBudget` (`θ★ = tₚ`, M1c replay at the `Hyb₂`
  instantiation + logging budget transparency; any `δ`).
- **Step C** `Hyb23Delta0.Hyb23SaltErasureLiftDelta0Residual` —
  `Hyb23Delta0Lift.hyb23SaltErasureLiftDelta0` (deterministic log-coupling bisimulation),
  making `Hyb23SaltErasureResidual` **unconditional at `δ = 0`**
  (`Hyb23Delta0Lift.hyb23SaltErasure_delta0`).

Refined (proven reduction onto a strictly finer core):

- **A** `Hyb12Align.Hyb12LazyEagerResampleResidual` ← all-lazy redraw coupling
  `Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual`
  (`hyb12LazyEagerResample_of_redrawCoupling`; both eager tables eliminated).
- **B2** `Hyb12Accounting.Hyb12MidFreshAlignResidual` ← cross-spec lazy re-keying
  `Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual` (`hyb12MidFreshAlign_of_crossSpecAlign`).
- **B4** `Hyb12Accounting.Hyb12VerifierPipelineBudgetResidual` ← once-per-round at the bare
  `d2fRaw` layer `Hyb12Budgets.Hyb12VerifierOncePerRoundResidual`
  (`hyb12VerifierPipelineBudget_of_oncePerRound`; the round-indexed F4 toolkit reduces it
  further to a backtrack no-refire invariant).
- **Step A** `Hyb23Step.Hyb23DecodedQueryResidual`@`δ=0` ← fixed-table cross-spec lift
  `Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual`
  (`hyb23DecodedQuery_delta0_of_crossLift`; the reachability invariant, `φ⁻¹`-injectivity
  on its success domain, and the uniform `eSpec`/salted-table re-indexing are discharged).

This module wires all of it into the tightest honest top-level theorems:

- `hyb12Step_of_coreResiduals` (any `δ`) — CO25 Claim 5.22 from its **four** remaining
  cores (redraw coupling, repeat derivation, cross-spec re-keying, once-per-round).
- `hyb23Step_delta0_of_coreResiduals` / `hyb23StepEps_delta0_of_coreResiduals` — CO25
  Claim 5.23 at `δ = 0` from its **two** remaining cores (cross-spec lift, memo
  transparency — exact and ε-budget forms).
- `keyLemmaEagerDelta0_of_coreResiduals` — **the round-4 exact frontier at `δ = 0`**:
  ten finest open residuals imply the full eager key lemma (round 3 had thirteen).
- `keyLemmaEagerDelta0_of_coreResidualsEps23` — **the honest headline**: the memo
  transparency leg consumed in ε-budget form (`ε ≤ 7/(2|Σ|^c)`, absorbed by the proven
  F1b slack at the **unchanged** `ηStarPaper` bound).

## The exact remaining map (round-4 census; hypothesis names as below)

- Claim 5.21: `h01C` = `Hyb01Step.Hyb01OffEventCouplingResidual` (off-`E` BackTrack
  coupling); the Lemma 5.8 fresh split `h01sw`/`h01ev`
  (`DDSFreshSwitchResidual εsw` / `FreshTraceEventResidual εev`, `εsw + εev ≤
  lemma5_8Bound`). Unchanged from round 2.
- Claim 5.22: `hRedraw` = `Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual`; `hRepeat` =
  `Hyb12Align.Hyb12RepeatDerivationResidual` (**doubtful** for non-injective decoders);
  `hCross` = `Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual`; `hOnce` =
  `Hyb12Budgets.Hyb12VerifierOncePerRoundResidual` (**honest doubt flag**: whether the
  backtrack no-refire invariant holds on *every* support path — `IsQueryBoundP` counts
  sampled-capacity collision paths too — mirrors the Lemma 5.12 raw-trace subtlety).
- Claim 5.23 at `δ = 0`: `h23X` = `Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual`
  (deterministic fixed-table bisimulation, the same plumbing class as the proven step C
  lift); `h23B` = `Hyb23Step.Hyb23MemoTransparencyResidual` (exact-`0` **doubtful** at
  every `δ` — use the ε-budget form `Hyb23Delta0.Hyb23MemoTransparencyEpsResidual`).
- Claim 5.24: `h34A`/`h34B` = `Hyb34Step.Hyb34DivergenceResidual` /
  `Hyb34CollapseResidual` (satisfiable only for `1 ≤ L`). Unchanged from round 2.

NOT claimed: the Claim 5.23 chain at `δ = 0` is **not** fully closed — step C is proven,
but steps A (cross-spec lift core) and B (memo transparency) remain open; `Hyb23StepEps`
at `δ = 0` is a *two-hypothesis* theorem (`hyb23StepEps_delta0_of_coreResiduals`), not a
proven fact.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.KeyLemmaFrontierRound4

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

-- The frontier theorems share one DSFS-wide variable block; each hypothesis uses only a
-- slice of it (repo precedent: `KeyLemmaFrontierRound3` and the lane modules).
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

/-! ## Claim 5.22 from its four remaining cores (any `δ`) -/

/-- **CO25 Claim 5.22 at the round-4 core granularity** (any `δ`): with B1 closed outright
(`Hyb12EagerLazy.hyb2FreshAlign_holds`) and B3 closed outright
(`Hyb12Budgets.hyb12ProverPipelineBudget`, `θ★ = tₚ`), the full `Hyb12StepResidual`
follows from the **four** remaining cores: the all-lazy fiber-redraw coupling (A), the
repeat-derivation memo transparency, the cross-spec lazy re-keying (B2), and the
once-per-round verifier budget (B4, logging-stripped). Honest flags: `hRepeat` is doubtful
for non-injective decoders; `hOnce` carries the support-path doubt flag (see the
`Hyb12Budgets` header). All reductions consumed here are proven and axiom-clean. -/
theorem hyb12Step_of_coreResiduals [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hOnce : Hyb12Budgets.Hyb12VerifierOncePerRoundResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  Hyb12EagerLazy.hyb12Step_of_lazyResiduals T_H T_P δ oImpl hRedraw hRepeat hCross
    (Hyb12Budgets.hyb12ProverPipelineBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P))
    (Hyb12Budgets.hyb12VerifierPipelineBudget_of_oncePerRound hOnce)

/-! ## Claim 5.23 at `δ = 0` from its two remaining cores -/

/-- **CO25 Claim 5.23 at `δ = 0` from its two remaining cores, exact form**: the
fixed-table cross-spec lift (step A's core — the probabilistic content and the
reachability invariant are already discharged by
`Hyb23Decoded.hyb23DecodedQuery_delta0_of_crossLift`) and exact memo transparency
(step B) give the full `Hyb23StepResidual`; salt erasure (step C) is proven
(`Hyb23Delta0Lift.hyb23SaltErasureLiftDelta0`). Honest flag: `h23B`'s exact-`0` form is
doubtful at every `δ` — use `hyb23StepEps_delta0_of_coreResiduals` for the honest
ε-budget routing. -/
theorem hyb23Step_delta0_of_coreResiduals [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23Step.Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl :=
  Hyb23Delta0Lift.hyb23Step_delta0_of_AB T_H T_P Salt oImpl
    (Hyb23Decoded.hyb23DecodedQuery_delta0_of_crossLift T_H T_P Salt oImpl h23X) h23B

/-- **CO25 Claim 5.23 at `δ = 0` from its two remaining cores, ε-budget form**: the
fixed-table cross-spec lift plus memo transparency with budget `ε` give
`Δ(Hyb₂, Hyb₃) ≤ ε`. This is the honest form of the step — the exact-`0` memo leg is
doubtful at every `δ` (the repeat-key raw-`ρ̂ᵢ` re-exposure event is salt-free). -/
theorem hyb23StepEps_delta0_of_coreResiduals [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) {ε : ℝ}
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23Delta0.Hyb23MemoTransparencyEpsResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      T_H T_P 0 Salt oImpl ε) :
    Hyb23Delta0.Hyb23StepEpsResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε :=
  Hyb23Delta0Lift.hyb23StepEps_delta0_of_AB T_H T_P Salt oImpl
    (Hyb23Decoded.hyb23DecodedQuery_delta0_of_crossLift T_H T_P Salt oImpl h23X) h23B

/-! ## The round-4 `δ = 0` frontier -/

/-- **The round-4 `δ = 0` frontier, exact form** (CO25 Lemma 5.1, eager surface, unsalted
DSFS transform): **ten** finest open residuals imply the full eager key lemma at `δ = 0`.
Relative to the round-3 frontier
(`KeyLemmaFrontierRound3.keyLemmaEagerDelta0_of_finestResiduals`, thirteen residuals):

- **closed outright**: B1 (`hyb2FreshAlign_holds`), B3 (`hyb12ProverPipelineBudget`),
  step C's fixed-table lift (`hyb23SaltErasureLiftDelta0`);
- **refined**: A → all-lazy redraw coupling, B2 → cross-spec lazy re-keying, B4 →
  once-per-round at the bare layer, step A → the fixed-table cross-spec lift.

Honest flags: `hRepeat` is doubtful for non-injective decoders; `hOnce` carries the
support-path doubt flag (`Hyb12Budgets` header); `h23B`'s exact-`0` form is doubtful at
every `δ` (use `keyLemmaEagerDelta0_of_coreResidualsEps23`); the Claim 5.24 split needs
`1 ≤ L`. Every reduction consumed here is proven and axiom-clean. -/
theorem keyLemmaEagerDelta0_of_coreResiduals
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp)
    -- Claim 5.21 lane (Lemma 5.8 fresh-split granularity)
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
    -- Claim 5.22 lane (round-4 core granularity)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hOnce : Hyb12Budgets.Hyb12VerifierOncePerRoundResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0)
    -- Claim 5.23 lane at `δ = 0` (round-4 core granularity)
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23Step.Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    -- Claim 5.24 lane
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  Hyb23Delta0Lift.keyLemmaEagerDelta0_of_finestResiduals' T_H T_P Salt oImpl
    h01C εsw εev h01sw h01ev h01sum
    (Hyb12EagerLazy.hyb12LazyEagerResample_of_redrawCoupling T_H T_P 0 oImpl hRedraw)
    hRepeat
    (Hyb12EagerLazy.hyb2FreshAlign_holds T_H T_P 0 oImpl)
    (Hyb12EagerLazy.hyb12MidFreshAlign_of_crossSpecAlign T_H T_P 0 oImpl hCross)
    (Hyb12Budgets.hyb12ProverPipelineBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := 0) (T_H := T_H) (T_P := T_P))
    (Hyb12Budgets.hyb12VerifierPipelineBudget_of_oncePerRound hOnce)
    (Hyb23Decoded.hyb23DecodedQuery_delta0_of_crossLift T_H T_P Salt oImpl h23X)
    h23B h34A h34B

/-- **The round-4 `δ = 0` frontier, ε-budget form (the honest headline)**: same as
`keyLemmaEagerDelta0_of_coreResiduals`, but the memo-transparency leg — whose exact-`0`
form is doubtful at every `δ` (the repeat-key raw-`ρ̂ᵢ` re-exposure event is a
permutation-state collision, salt-free) — is consumed with an ε-budget
`ε ≤ 7/(2|Σ|^c)`, absorbed by the proven F1b slack
(`Hyb23Delta0.claimSum_add_le_ηStarPaper`) at the **unchanged** `ηStarPaper` bound.
Caveat (from the `Hyb23Delta0` header): the slack is linear in `t` while the re-exposure
event is birthday-quadratic — for large budgets the honest route is re-stating Claims
5.21/5.24 across the memo switch, not this additive ε. -/
theorem keyLemmaEagerDelta0_of_coreResidualsEps23
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp)
    {ε : ℝ} (hε : ε ≤ 7 / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C))
    -- Claim 5.21 lane (Lemma 5.8 fresh-split granularity)
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
    -- Claim 5.22 lane (round-4 core granularity)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hOnce : Hyb12Budgets.Hyb12VerifierOncePerRoundResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0)
    -- Claim 5.23 lane at `δ = 0`, memo transparency with ε-budget
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23Delta0.Hyb23MemoTransparencyEpsResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      T_H T_P 0 Salt oImpl ε)
    -- Claim 5.24 lane
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  Hyb23Delta0Lift.keyLemmaEagerDelta0_of_finestResidualsEps23' T_H T_P Salt oImpl hε
    h01C εsw εev h01sw h01ev h01sum
    (Hyb12EagerLazy.hyb12LazyEagerResample_of_redrawCoupling T_H T_P 0 oImpl hRedraw)
    hRepeat
    (Hyb12EagerLazy.hyb2FreshAlign_holds T_H T_P 0 oImpl)
    (Hyb12EagerLazy.hyb12MidFreshAlign_of_crossSpecAlign T_H T_P 0 oImpl hCross)
    (Hyb12Budgets.hyb12ProverPipelineBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := 0) (T_H := T_H) (T_P := T_P))
    (Hyb12Budgets.hyb12VerifierPipelineBudget_of_oncePerRound hOnce)
    (Hyb23Decoded.hyb23DecodedQuery_delta0_of_crossLift T_H T_P Salt oImpl h23X)
    h23B h34A h34B

end DuplexSpongeFS.KeyLemmaFrontierRound4

#print axioms DuplexSpongeFS.KeyLemmaFrontierRound4.hyb12Step_of_coreResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound4.hyb23Step_delta0_of_coreResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound4.hyb23StepEps_delta0_of_coreResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound4.keyLemmaEagerDelta0_of_coreResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound4.keyLemmaEagerDelta0_of_coreResidualsEps23

end
