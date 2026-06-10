/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.VerifierReplay
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets

/-!
# CO25 Lemma 5.1 (DSFS Key Lemma) — eager-surface campaign assembly

This module reconciles the parallel campaign lanes into the tightest honest top-level
theorems for the eager key lemma:

- `KeyLemmaHybrids.keyLemmaEager_of_steps` reduced `KeyLemmaEagerResidual` to the four
  per-step TV residuals (Claims 5.21–5.24) **plus** the witness budget residuals M1c/M1d;
- `SimulatorBudgets` has since **proven** M1c/M1d outright
  (`simulatedProverChallengeBudget` / `simulatedProverSharedBudget`);
- `VerifierReplay.hyb34Step_of_strictSplit` reduced the Claim 5.24 step to any Eq. 55
  coupling split `(εA, εB)` through the strict-replay hybrid `Hyb3Strict`.

Wiring these together yields:

- `keyLemmaEager_of_hybSteps` — **the current frontier**: the four hybrid-step residuals
  alone imply the full eager key lemma; every witness-budget obligation of CO25 Lemma 5.1
  (conjuncts (a) and (b)) is discharged.
- `keyLemmaEager_of_steps_strictSplit` — the Claim 5.24 hypothesis replaced by its proven
  Eq. 55 decomposition: Claims 5.21–5.23 plus any strict-split coupling pair summing to
  `claim5_24Bound` imply the eager key lemma.

## Residual census after campaign round 4 (the honest remaining-work map)

Round 2 split each step residual onto finer named residuals with proven skeletons
(frontier: `KeyLemmaFrontier.keyLemmaEager_of_finestResiduals`, any `δ`). Round 3 ran four
deeper lanes (`Hyb12Align`, `Hyb12Accounting`, `Hyb23Delta0`, `BacktrackLemmas`) plus the
assembly `KeyLemmaFrontierRound3` (thirteen-residual `δ = 0` frontier). Round 4 ran four
more (`Hyb12EagerLazy`, `Hyb12Budgets`, `Hyb23Decoded`, `Hyb23Delta0Lift`): **three
round-3 residuals closed outright** (B1 eager↔lazy alignment, B3 prover `θ★` budget, the
step C fixed-table salt-erasure lift — so `Hyb23SaltErasureResidual` is **unconditional at
`δ = 0`**, `Hyb23Delta0Lift.hyb23SaltErasure_delta0`) and **four were replaced by strictly
finer cores with proven reductions** (A, B2, B4, step A). **The tightest top-level
theorems are now the ten-residual `δ = 0` frontiers**
`KeyLemmaFrontierRound4.keyLemmaEagerDelta0_of_coreResiduals` (exact) and
`keyLemmaEagerDelta0_of_coreResidualsEps23` (memo leg with ε-budget — the honest
headline); the items below are exactly their hypotheses. `δ = 0` is the primary surface
(the unsalted DSFS transform; CO25's salt exists for ZK): for `δ > 0` the salt-erasure leg
of Claim 5.23 is genuinely false and the eager surface must first be re-keyed on salted
statements.

Open residuals **on the eager key-lemma critical path** (at `δ = 0`):

1. CO25 Claim 5.21 (`Hyb01Step`): `Hyb01OffEventCouplingResidual` (the off-`E` BackTrack
   coupling, §5.6/5.9–5.10) plus the Lemma 5.8 split `DDSFreshSwitchResidual εsw` (eager-
   lazy carrier switch) / `FreshTraceEventResidual εev` (fresh-world event decomposition)
   — or the unsplit `BirthdayBound.Lemma5_8EagerBirthdayResidual`
   (`KeyLemmaFrontier.keyLemmaEager_of_birthdayLanes`). Unchanged from round 2; round 3
   made the §5.6 honest-bad `E`-mass channel **M2-free on the dedup'd surface**
   (`KeyLemmaFrontierRound3.probEvent_honestBadDedup_le_probEvent_E` /
   `honestBadDedup_birthday_of_lemma5_8` — no Lemma 5.12/5.14/5.16 hypotheses left).
2. CO25 Claim 5.22 (`Hyb12Step` → `Hyb12Align`/`Hyb12Accounting` → `Hyb12EagerLazy` +
   `Hyb12Budgets`): **four** remaining cores, assembled by
   `KeyLemmaFrontierRound4.hyb12Step_of_coreResiduals` (any `δ`):
   `Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual` (all-lazy fiber-redraw coupling — both
   eager tables eliminated), `Hyb12Align.Hyb12RepeatDerivationResidual` (**doubtful** for
   non-injective decoders — true for injective ones; honest general repair =
   birthday-budgeted relaxation), `Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual`
   (cross-spec `gSpec → eSpec` re-keying between two *lazy* games),
   `Hyb12Budgets.Hyb12VerifierOncePerRoundResidual` (once per round at the bare `d2fRaw`
   layer — reduces to a backtrack no-refire invariant via the round-indexed F4 toolkit;
   **honest doubt flag**: whether it holds on *every* support path, sampled-capacity
   collision paths included, mirrors the Lemma 5.12 raw-trace subtlety). Closed in round
   4: `Hyb2FreshAlignResidual` (B1, outright — `hyb2FreshAlign_holds`, via the generic
   lazy-memo = eager-uniform CPS master theorem) and `Hyb12ProverPipelineBudgetResidual`
   (B3, outright — `hyb12ProverPipelineBudget`, `θ★ = tₚ`).
3. CO25 Claim 5.23 (`Hyb23Step` → `Hyb23Delta0` → `Hyb23Decoded` + `Hyb23Delta0Lift`), at
   `δ = 0` — **step C (salt erasure) is fully PROVEN** (`hyb23SaltErasure_delta0`: the
   round-3 distributional content plus the round-4 fixed-table log-coupling bisimulation
   `hyb23SaltErasureLiftDelta0`); the round-2 falsity flag is confined to `δ > 0`.
   Remaining **two** cores (`KeyLemmaFrontierRound4.hyb23Step(Eps)_delta0_of_coreResiduals`):
   `Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual` (step A's fixed-table cross-spec
   lift — the reachability invariant, `φ⁻¹`-injectivity on its success domain, and the
   uniform `eSpec`/salted-table re-indexing are all discharged by
   `hyb23DecodedQuery_delta0_of_crossLift`; what remains is the same deterministic
   `simulateQ` bisimulation plumbing class as the proven step C lift) and
   `Hyb23MemoTransparency(Eps)Residual`@0 (step B; exact-`0` doubtful at every `δ`: the
   repeat-key re-exposure event is salt-free; any `ε ≤ 7/(2|Σ|^c)` is absorbed at the
   unchanged `ηStarPaper` by the proven F1b slack `claimSum_add_le_ηStarPaper`). The
   `δ = 0` chain is **not** fully closed — `Hyb23Step(Eps)Residual`@0 is a two-hypothesis
   theorem, not a proven fact.
4. CO25 Claim 5.24 (`Hyb34Step`): `Hyb34DivergenceResidual` / `Hyb34CollapseResidual`
   (the symmetric Eq. 55 halves at `claim5_24Bound/2` each; satisfiable only for
   `1 ≤ L`, see `claim5_24Bound_nonneg`). Unchanged from round 2; the dedup'd honest-bad
   channel of item 1 also feeds this lane's bad-event mass.

Off the critical path:

5. M2 (`BacktrackLemmas`): CO25 Lemmas 5.12/5.14/5.16 (honest forms) are **PROVEN for
   deduplicated traces** (`lemma5_1{2,4,6}Honest_of_noRedundant`) — the paper's own
   setting, and the only form the `E`-mass plumbing needs (folded hypothesis-free into
   `KeyLemmaFrontierRound3`). The raw-trace surface `Lemma5_12HonestResidual` is
   **machine-checked FALSE** (`lemma5_12HonestResidual_not_universal`); the 5.14/5.16
   redundant-trace corners stay open but nothing on the critical path consumes them.
6. `BirthdayBound.Lemma5_8EagerBirthdayResidual` — subsumed by item 1 (either
   granularity discharges it via `Hyb01Step.lemma5_8Eager_of_freshSplit`).

**Closed in round 1**: `D2sQueryStepGSpecBudgetResidual` (F4),
`D2fOuterImplSharedBudgetResidual` (F4b), `SimulatedProverChallengeBudgetResidual` (M1c),
`SimulatedProverSharedBudgetResidual` (M1d) — all proven in `SimulatorBudgets`.
**Closed in round 3** (all axiom-clean): `Hyb₁ = Hyb1TableResampled` (outright); the salt
erasure distributional content at `δ = 0` (modulo the deterministic lift); the M2 dedup'd
cores (outright) and the M2-free `E`-mass channel; the `θ★`/`claim5_22Bound` accounting
theorem.
**Closed in round 4** (all axiom-clean): `Hyb2FreshAlignResidual` (B1, outright, any `δ`);
`Hyb12ProverPipelineBudgetResidual` (B3, outright, any `δ`);
`Hyb23SaltErasureLiftDelta0Residual` (outright) and with it
`Hyb23SaltErasureResidual`@`δ=0` (step C, unconditional). The cores above are the finest
honest frontier.

The legacy `KeyLemma.KeyLemmaResidual` (i.i.d.-oracle surface, `ηStar` with exponent `C+1`)
is numerically over-strong (`KeyLemmaFoundations.ηStar_le_ηStarPaper` direction) and likely
unwitnessable; it is **not** a target of this assembly.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

-- `[∀ i, DecidableEq (pSpec.Message i)]` is required by the proofs (the `SimulatorBudgets`
-- M1c/M1d theorems carry it) but not by the statements; silencing the type-only linter keeps
-- the hypothesis where the proof needs it (repo precedent: the sibling lane modules).
set_option linter.unusedDecidableInType false

namespace DuplexSpongeFS.KeyLemmaAssembly

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-- **Campaign frontier** (CO25 Lemma 5.1, eager surface): the four hybrid-step residuals
(Claims 5.21–5.24) alone imply the full eager key lemma. The witness budget conjuncts
(a)/(b) of Lemma 5.1 are no longer hypotheses — they are discharged by the proven
`SimulatorBudgets.simulatedProverChallengeBudget` (M1c, `θ★ = tₚ`) and
`SimulatorBudgets.simulatedProverSharedBudget` (M1d, 1:1 `oSpec` forwarding). -/
theorem keyLemmaEager_of_hybSteps
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp)
    (h01 : Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h12 : Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h23 : Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h34 : Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  keyLemmaEager_of_steps T_H T_P δ Salt oImpl h01 h12 h23 h34
    (SimulatorBudgets.simulatedProverChallengeBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P))
    (SimulatorBudgets.simulatedProverSharedBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P))

/-- **Claim 5.24 via the proven Eq. 55 skeleton**: Claims 5.21–5.23 plus any strict-split
coupling pair — `εA` bounding `Δ(Hyb₃, Hyb3Strict)` (the bad-event mass off the replay
path) and `εB` bounding `Δ(Hyb3Strict, Hyb₄)` (the hit-path collapse), summing to
`claim5_24Bound` — imply the full eager key lemma. This composes
`VerifierReplay.hyb34Step_of_strictSplit` with `keyLemmaEager_of_hybSteps`. -/
theorem keyLemmaEager_of_steps_strictSplit
    [DecidableEq ι] [SampleableType U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp)
    (h01 : Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h12 : Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h23 : Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (εA εB : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hA : ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
      (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × pSpec.Messages))
      (tₕ tₚ tₚᵢ L : ℕ),
      pSpec.totalNumPermQueries ≤ L →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
      SPMF.tvDist (Hyb3 T_H T_P δ Salt oImpl V P)
          (VerifierReplay.Hyb3Strict T_H T_P δ Salt oImpl V P)
        ≤ εA tₕ tₚ tₚᵢ L)
    (hB : ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
      (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × pSpec.Messages))
      (tₕ tₚ tₚᵢ L : ℕ),
      pSpec.totalNumPermQueries ≤ L →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
      SPMF.tvDist (VerifierReplay.Hyb3Strict T_H T_P δ Salt oImpl V P)
          (Hyb4 oImpl V
            (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
        ≤ εB tₕ tₚ tₚᵢ L)
    (hsum : ∀ tₕ tₚ tₚᵢ L : ℕ,
      εA tₕ tₚ tₚᵢ L + εB tₕ tₚ tₚᵢ L ≤ claim5_24Bound U tₕ tₚ tₚᵢ L) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  keyLemmaEager_of_hybSteps T_H T_P δ Salt oImpl h01 h12 h23
    (VerifierReplay.hyb34Step_of_strictSplit T_H T_P δ Salt oImpl εA εB hA hB hsum)

end DuplexSpongeFS.KeyLemmaAssembly

#print axioms DuplexSpongeFS.KeyLemmaAssembly.keyLemmaEager_of_hybSteps
#print axioms DuplexSpongeFS.KeyLemmaAssembly.keyLemmaEager_of_steps_strictSplit

end
