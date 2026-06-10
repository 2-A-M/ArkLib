/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFrontierRound4
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb34Legs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.DoubtRepairs

/-!
# CO25 Lemma 5.1 — round-5 assembly: the repaired twelve-residual `δ = 0` frontier

Round 5 ran four lanes. Two delivered (`Hyb34Legs`, `DoubtRepairs`); two produced **no
closures** (the Claim 5.23 cross-lift lane and the Claim 5.22 coupling lane — their cores
`h23X`, `hRedraw`, `hCross` are carried **unchanged** from round 4). This module wires
what landed into the tightest honest top-level theorems.

## What changed relative to round 4

**Claim 5.24 (both Eq. 55 legs refined, no TV-shaped obligation left)** — `Hyb34Legs`:
`Hyb3Strict` is an *abort-truncation* of both neighbours, and the abort-truncation TV
identity (`spmf_tvDist_eq_abortGap`: off-sink domination ⇒ TV distance **equals** the
sink gap, exactly) replaces each leg's TV coupling by (i) a pointwise sub-run domination
and (ii) a scalar abort-gap mass. The εA structural side is further threaded
(`hyb34StrictSubRun_of_stageDomination`) down to a *fixed-table, fixed-memo
verifier-stage* domination — the exact granularity of the proven per-query seeds
(`probOutput_some_hitOnly_run_le_eager`) and of the step-C d2fRaw induction recipe.
`h34A`/`h34B` are **replaced** by the four cores `hStage`/`hgapA`/`hsubB`/`hgapB`.

**The three doubt-flagged residuals (honest repairs, not closures)** — `DoubtRepairs`:

- `Hyb12RepeatDerivationResidual` (exact-`0`): its kernel is **machine-checked FALSE**
  (`repeatDerivationKernelTransparency_not_universal`; TV provably positive at
  `ψ = const : Bool → Unit`, `repeatDerivationKernel_tvDist_pos`; injective-`ψ` rescue
  proven, `repeatDerivationKernel_transparent_of_injective`). The frontier consumes the
  leg in repaired ε₁₂-budget form (`Hyb12RepeatDerivationEpsFunResidual`). The exact form
  is kept only in the legacy theorem below, explicitly vacuity-flagged.
- `Hyb12VerifierOncePerRoundResidual` (B4): reduced **with proof**
  (`hyb12VerifierOncePerRound_of_noRefire`) to the canonical Dead-certificate core
  `Hyb12OncePerRoundNoRefireResidual` — fire-kills + dead-stays-dead on every support
  path; no `IsQueryBoundP` induction remains. The raw-form falsity suspicion (Lemma 5.12
  mirror) is documented, neither direction machine-checked.
- `Hyb23MemoTransparencyEpsResidual`: ε₂₃ estimated birthday-shaped via the §5.6
  capacity-collision channel (`probEvent_capacityDup_le_lemma5_8Bound`); machine-checked
  absorption verdicts — fits the budget-uniform slack `7/(2|Σ|^c)` only at `T ≤ 1`
  (`lemma5_8Bound_one_le_uniformSlack` / `uniformSlack_lt_lemma5_8Bound`), and the
  birthday shape overflows even the full claimSum slack for every non-trivial budget
  (`claimSlack_lt_lemma5_8Bound`, `birthdayRepair_not_absorbable`). The frontier consumes
  the leg in ε₂₃-budget-function form (`Hyb23MemoTransparencyEpsFunResidual`).

## The round-5 theorems

- `hyb12Step_of_noRefireCores` / `hyb12StepEpsFun_of_noRefireCores` — CO25 Claim 5.22
  (exact / ε-budget) with B4 at Dead-certificate granularity.
- `hyb34Step_of_stageLegs` — CO25 Claim 5.24 from its four round-5 cores (any `δ`).
- `keyLemmaEagerDelta0_of_coreResidualsEpsFun1223` — **the round-5 honest headline**:
  twelve finest open residuals (counting the Lemma 5.8 fresh-switch/event pair as one, as
  in rounds 3–4; thirteen hypothesis slots) + the sharp absorption side condition `hεsum`
  imply the full eager key lemma at `δ = 0` at the **unchanged** `ηStarPaper` bound.
- `keyLemmaEagerDelta0_of_coreResidualsEps1223` — constant-budget corollary
  (`ε₁₂ + ε₂₃ ≤ 7/(2|Σ|^c)`).
- `keyLemmaEagerDelta0_of_coreResiduals` — the exact-form **legacy** frontier (round-4
  shape at round-5 granularity). ⚠ Its `hRepeat` hypothesis is the exact-`0` form whose
  kernel is machine-checked false for non-injective decoders: unless the in-tree decoders
  are injective on the reachable fibers (or the repeat path is unreachable), this
  hypothesis is expected unsatisfiable — kept only as the embedding target
  (`hyb12RepeatDerivationEpsFun_of_exact`) and for census continuity.

## The exact remaining map (round-5 census; hypothesis names as in the headline)

- Claim 5.21 (unchanged since round 2): `h01C` =
  `Hyb01Step.Hyb01OffEventCouplingResidual`; the Lemma 5.8 fresh split `h01sw`/`h01ev`
  (`DDSFreshSwitchResidual εsw` / `FreshTraceEventResidual εev`,
  `εsw + εev ≤ lemma5_8Bound`).
- Claim 5.22: `hRedraw` = `Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual` (**unchanged —
  null lane this round**); `hRepeat` = `DoubtRepairs.Hyb12RepeatDerivationEpsFunResidual
  ε₁₂` (**repaired**; exact-`0` kernel machine-checked false; birthday instantiation not
  absorbable — beyond the slack the honest route is re-stating the 5.21/5.24 budgets);
  `hCross` = `Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual` (**unchanged — null lane**);
  `hNoRefire` = `DoubtRepairs.Hyb12OncePerRoundNoRefireResidual` (**refined**: the
  backtrack no-refire state analysis is all that is left of B4; support-path doubt flag
  carried, raw-form falsity not machine-checked).
- Claim 5.23 at `δ = 0`: `h23X` = `Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual`
  (**unchanged — null lane**; still the same plumbing class as the proven step-C lift);
  `h23B` = `DoubtRepairs.Hyb23MemoTransparencyEpsFunResidual ε₂₃` (**repaired**; honest
  estimate birthday-shaped, fits the uniform slack only at `T ≤ 1`).
- Claim 5.24 (**refined this round**): `hStage` =
  `Hyb34Legs.Hyb34VerifierStageDominationResidual` (εA structural, fixed-table
  verifier-stage domination — step-C bisimulation class in inequality form); `hgapA` =
  `Hyb34Legs.Hyb34StrictAbortGapResidual` (εA mass — the genuine `E_𝒱` content, §5.6
  discharge path); `hsubB` = `Hyb34Legs.Hyb34CollapseSubRunResidual` (εB structural,
  cross-skeleton threading of the proven `coherent_serve` keystone); `hgapB` =
  `Hyb34Legs.Hyb34CollapseAbortGapResidual` (εB mass). Satisfiability caveat `1 ≤ L`
  unchanged; `Hyb34StrictSubRunResidual` is implied by `hStage` (proven threading) and is
  no longer counted.
- Side condition (not a residual): `hεsum` — the **exact** F1b claimSum absorption
  boundary `(14t + 7)/(2|Σ|^c)`; sharp in both directions (inside it nothing changes,
  birthday shapes provably overflow it).

## NOT claimed (honest negative census)

- **`hyb23StepEps_delta0_proved` is NOT stated**: Claim 5.23 at `δ = 0` is *not* fully
  closed. Step C is proven (`hyb23SaltErasureLiftDelta0`) and step A's probabilistic
  content is discharged, but step A's fixed-table cross-spec lift core (`h23X`) remains
  open (the round-5 cross-lift lane produced nothing), and the memo leg (`h23B`) is an
  ε-budget, not `0`. The tightest 5.23 surfaces remain the *conditional*
  `hyb23StepEpsFun_delta0_of_coreResiduals` (two hypotheses) and
  `KeyLemmaFrontierRound4.hyb23StepEps_delta0_of_coreResiduals`.
- The exact-`0` repeat-derivation and memo-transparency legs are **not** disproven at the
  full-game level (kernel falsity is machine-checked; full-game falsity additionally needs
  the documented reachability constructions).
- All round-5 new content is reduction/repair plumbing: **no previously-open residual was
  closed outright this round** (round 4's closures B1/B3/step-C stand).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.KeyLemmaFrontierRound5

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

-- The frontier theorems share one DSFS-wide variable block; each hypothesis uses only a
-- slice of it (repo precedent: `KeyLemmaFrontierRound3`/`Round4` and the lane modules).
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

/-! ## Claim 5.22 at round-5 granularity (B4 at the Dead-certificate core) -/

/-- **CO25 Claim 5.22, exact legacy form, B4 at Dead-certificate granularity** (any `δ`):
the round-4 core assembly with the once-per-round leg consumed through the proven
Dead-certificate reduction (`DoubtRepairs.hyb12VerifierOncePerRound_of_noRefire`). ⚠ The
`hRepeat` hypothesis is the exact-`0` form whose kernel is machine-checked false for
non-injective decoders (`repeatDerivationKernelTransparency_not_universal`) — prefer
`hyb12StepEpsFun_of_noRefireCores`. -/
theorem hyb12Step_of_noRefireCores [SampleableType U]
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
    (hNoRefire : DoubtRepairs.Hyb12OncePerRoundNoRefireResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  KeyLemmaFrontierRound4.hyb12Step_of_coreResiduals T_H T_P δ oImpl hRedraw hRepeat hCross
    (DoubtRepairs.hyb12VerifierOncePerRound_of_noRefire T_H T_P δ hNoRefire)

/-- **CO25 Claim 5.22, repaired ε-budget form, B4 at Dead-certificate granularity**
(any `δ`): `Δ(Hyb₁, Hyb₂) ≤ claim5_22Bound + ε₁₂(T)` from the all-lazy redraw coupling,
the **repaired** ε₁₂-budgeted repeat-derivation leg, the cross-spec lazy re-keying, and
the no-refire certificate. This is the honest round-5 form of the Claim 5.22 lane. -/
theorem hyb12StepEpsFun_of_noRefireCores [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) {ε₁₂ : ℕ → ℝ}
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hRepeat : DoubtRepairs.Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl
      ε₁₂)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hNoRefire : DoubtRepairs.Hyb12OncePerRoundNoRefireResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P δ) :
    DoubtRepairs.Hyb12StepEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl ε₁₂ :=
  DoubtRepairs.hyb12StepEpsFun_of_coreResiduals T_H T_P δ oImpl hRedraw hRepeat hCross
    (DoubtRepairs.hyb12VerifierOncePerRound_of_noRefire T_H T_P δ hNoRefire)

/-! ## Claim 5.24 from its four round-5 cores -/

/-- **CO25 Claim 5.24 from the four round-5 cores** (any `δ`): the εA leg from the
fixed-table verifier-stage domination (threaded to the whole game by the proven
`hyb34StrictSubRun_of_stageDomination`) plus its abort-gap mass, and the εB leg from the
strict-vs-`Hyb₄` sub-run domination plus its abort-gap mass — via the abort-truncation TV
identity, with zero slack. No TV-shaped obligation remains in the Claim 5.24 lane. -/
theorem hyb34Step_of_stageLegs [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hStage : Hyb34Legs.Hyb34VerifierStageDominationResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt
      oImpl)
    (hgapA : Hyb34Legs.Hyb34StrictAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hsubB : Hyb34Legs.Hyb34CollapseSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hgapB : Hyb34Legs.Hyb34CollapseAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl :=
  Hyb34Legs.hyb34Step_of_legs T_H T_P δ Salt oImpl
    (Hyb34Legs.hyb34StrictSubRun_of_stageDomination T_H T_P δ Salt oImpl hStage)
    hgapA hsubB hgapB

/-! ## The round-5 `δ = 0` frontier -/

/-- **The round-5 `δ = 0` frontier, exact legacy form**: the round-4 exact frontier at
round-5 granularity — B4 at the Dead-certificate core, Claim 5.24 at the four leg cores.

⚠ **Vacuity flag (stronger than round 4's doubt flag)**: `hRepeat` is the exact-`0`
repeat-derivation form whose *kernel* is now machine-checked FALSE for non-injective
decoders (`DoubtRepairs.repeatDerivationKernelTransparency_not_universal`); `h23B`'s
exact-`0` form remains doubtful at every `δ`. This theorem is kept for census continuity
and for the injective-decoder/unreachable-repeat regimes; the honest headline is
`keyLemmaEagerDelta0_of_coreResidualsEpsFun1223`. -/
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
    -- Claim 5.22 lane (round-5 granularity, hRepeat exact ⚠)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hNoRefire : DoubtRepairs.Hyb12OncePerRoundNoRefireResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P 0)
    -- Claim 5.23 lane at `δ = 0` (round-4 cores, h23B exact ⚠)
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23Step.Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    -- Claim 5.24 lane (round-5 leg cores)
    (hStage : Hyb34Legs.Hyb34VerifierStageDominationResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt
      oImpl)
    (hgapA : Hyb34Legs.Hyb34StrictAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hsubB : Hyb34Legs.Hyb34CollapseSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hgapB : Hyb34Legs.Hyb34CollapseAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  KeyLemmaFrontierRound4.keyLemmaEagerDelta0_of_coreResiduals T_H T_P Salt oImpl
    h01C εsw εev h01sw h01ev h01sum hRedraw hRepeat hCross
    (DoubtRepairs.hyb12VerifierOncePerRound_of_noRefire T_H T_P 0 hNoRefire)
    h23X h23B
    (Hyb34Legs.hyb34Divergence_of_subRun_gap T_H T_P 0 Salt oImpl
      (Hyb34Legs.hyb34StrictSubRun_of_stageDomination T_H T_P 0 Salt oImpl hStage) hgapA)
    (Hyb34Legs.hyb34Collapse_of_subRun_gap T_H T_P 0 Salt oImpl hsubB hgapB)

/-- **The round-5 `δ = 0` frontier, repaired ε-budget form (THE honest headline)**:
twelve finest open residuals (counting the Lemma 5.8 fresh-switch/event pair as one, as in
rounds 3–4) plus the sharp absorption side condition imply the full eager key lemma at
`δ = 0`, at the **unchanged** `ηStarPaper` bound:

- Claim 5.21: `h01C` + the fresh split (`h01sw`/`h01ev`, `h01sum`);
- Claim 5.22: `hRedraw`, **repaired** `hRepeat` (ε₁₂-budgeted; the exact-`0` kernel is
  machine-checked false), `hCross`, **refined** `hNoRefire` (B4's Dead certificate);
- Claim 5.23 at `δ = 0`: `h23X` (cross-spec lift, unchanged), **repaired** `h23B`
  (ε₂₃-budgeted);
- Claim 5.24: **refined** `hStage`/`hgapA`/`hsubB`/`hgapB` (the abort-truncation legs);
- `hεsum`: `ε₁₂(T) + ε₂₃(T)` within the exact F1b claimSum slack `(14t + 7)/(2|Σ|^c)` —
  the sharp absorption boundary (birthday-shaped budgets provably overflow it,
  `DoubtRepairs.birthdayRepair_not_absorbable`; beyond it the honest route is the
  documented re-statement of the Claim 5.21/5.24 budgets).

Caveats: the Claim 5.24 split needs `1 ≤ L`; `hNoRefire` carries the support-path doubt
flag. Every reduction consumed here is proven and axiom-clean. -/
theorem keyLemmaEagerDelta0_of_coreResidualsEpsFun1223
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
    (oImpl : QueryImpl oSpec ProbComp) {ε₁₂ ε₂₃ : ℕ → ℝ}
    (hεsum : ∀ tₕ tₚ tₚᵢ L : ℕ,
      ε₁₂ (tₕ + 1 + tₚ + L + tₚᵢ) + ε₂₃ (tₕ + 1 + tₚ + L + tₚᵢ)
        ≤ (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7)
            / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C))
    -- Claim 5.21 lane (Lemma 5.8 fresh-split granularity)
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
    -- Claim 5.22 lane (round-5 granularity, repeat derivation REPAIRED)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : DoubtRepairs.Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl
      ε₁₂)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hNoRefire : DoubtRepairs.Hyb12OncePerRoundNoRefireResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P 0)
    -- Claim 5.23 lane at `δ = 0` (memo transparency REPAIRED)
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : DoubtRepairs.Hyb23MemoTransparencyEpsFunResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      T_H T_P 0 Salt oImpl ε₂₃)
    -- Claim 5.24 lane (round-5 leg cores)
    (hStage : Hyb34Legs.Hyb34VerifierStageDominationResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt
      oImpl)
    (hgapA : Hyb34Legs.Hyb34StrictAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hsubB : Hyb34Legs.Hyb34CollapseSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hgapB : Hyb34Legs.Hyb34CollapseAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  DoubtRepairs.keyLemmaEagerDelta0_of_coreResidualsEpsFun1223 T_H T_P Salt oImpl hεsum
    h01C εsw εev h01sw h01ev h01sum hRedraw hRepeat hCross
    (DoubtRepairs.hyb12VerifierOncePerRound_of_noRefire T_H T_P 0 hNoRefire)
    h23X h23B
    (Hyb34Legs.hyb34Divergence_of_subRun_gap T_H T_P 0 Salt oImpl
      (Hyb34Legs.hyb34StrictSubRun_of_stageDomination T_H T_P 0 Salt oImpl hStage) hgapA)
    (Hyb34Legs.hyb34Collapse_of_subRun_gap T_H T_P 0 Salt oImpl hsubB hgapB)

/-- **Constant-budget corollary of the round-5 headline**: both repaired legs at constant
budgets with `ε₁₂ + ε₂₃ ≤ 7/(2|Σ|^c)` (the budget-uniform part of the proven F1b slack).
Machine-checked caveat: the birthday-shaped estimates exceed every constant fitting here
beyond trivial budgets (`DoubtRepairs.uniformSlack_lt_lemma5_8Bound`). -/
theorem keyLemmaEagerDelta0_of_coreResidualsEps1223
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
    (oImpl : QueryImpl oSpec ProbComp) {ε₁₂ ε₂₃ : ℝ}
    (hε : ε₁₂ + ε₂₃ ≤ 7 / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C))
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : DoubtRepairs.Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl
      (fun _ => ε₁₂))
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hNoRefire : DoubtRepairs.Hyb12OncePerRoundNoRefireResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P 0)
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : DoubtRepairs.Hyb23MemoTransparencyEpsFunResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      T_H T_P 0 Salt oImpl (fun _ => ε₂₃))
    (hStage : Hyb34Legs.Hyb34VerifierStageDominationResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt
      oImpl)
    (hgapA : Hyb34Legs.Hyb34StrictAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hsubB : Hyb34Legs.Hyb34CollapseSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hgapB : Hyb34Legs.Hyb34CollapseAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  DoubtRepairs.keyLemmaEagerDelta0_of_coreResidualsEps1223 T_H T_P Salt oImpl hε
    h01C εsw εev h01sw h01ev h01sum hRedraw hRepeat hCross
    (DoubtRepairs.hyb12VerifierOncePerRound_of_noRefire T_H T_P 0 hNoRefire)
    h23X h23B
    (Hyb34Legs.hyb34Divergence_of_subRun_gap T_H T_P 0 Salt oImpl
      (Hyb34Legs.hyb34StrictSubRun_of_stageDomination T_H T_P 0 Salt oImpl hStage) hgapA)
    (Hyb34Legs.hyb34Collapse_of_subRun_gap T_H T_P 0 Salt oImpl hsubB hgapB)

end DuplexSpongeFS.KeyLemmaFrontierRound5

#print axioms DuplexSpongeFS.KeyLemmaFrontierRound5.hyb12Step_of_noRefireCores
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound5.hyb12StepEpsFun_of_noRefireCores
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound5.hyb34Step_of_stageLegs
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound5.keyLemmaEagerDelta0_of_coreResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound5.keyLemmaEagerDelta0_of_coreResidualsEpsFun1223
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound5.keyLemmaEagerDelta0_of_coreResidualsEps1223

end
