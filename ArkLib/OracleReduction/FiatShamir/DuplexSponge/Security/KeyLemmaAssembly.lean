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

## Residual census after campaign round 2 (the honest remaining-work map)

Round 2 ran one lane per step residual (`Hyb01Step`/`Hyb12Step`/`Hyb23Step`/`Hyb34Step`).
**No step residual closed outright**, but each now carries a *proven* split skeleton onto
strictly finer named residuals; the composition is the round-2 frontier
`KeyLemmaFrontier.keyLemmaEager_of_finestResiduals` (the tightest top-level theorem —
the items below are exactly its hypotheses).

Open residuals **on the eager key-lemma critical path**:

1. CO25 Claim 5.21 (`Hyb01Step`): `Hyb01OffEventCouplingResidual` (the off-`E` BackTrack
   coupling, §5.6/5.9–5.10) plus the Lemma 5.8 split `DDSFreshSwitchResidual εsw` (eager-
   lazy carrier switch) / `FreshTraceEventResidual εev` (fresh-world event decomposition)
   — or the unsplit `BirthdayBound.Lemma5_8EagerBirthdayResidual`
   (`KeyLemmaFrontier.keyLemmaEager_of_birthdayLanes`). Proven in the lane: the SPMF TV
   accumulator, the fresh/without-replacement switching lemma at `T(T−1)/(2|X|)`, flavor
   budget recombination, and `hyb01Step_of_offEventCoupling_of_{birthday,freshSplit}`.
2. CO25 Claim 5.22 (`Hyb12Step`): `Hyb12ResampleAlignResidual` (`Δ(Hyb₁, Hyb12Mid) = 0`
   fiber-resample alignment; open content = the §5.4 no-repeated-derivation argument) and
   `Hyb12BiasAccountingResidual` (`Δ(Hyb12Mid, Hyb₂) ≤ claim5_22Bound`; per-derivation
   `ε_cdc,i` cost proven, open content = the θ★ pipeline accounting). Proven in the lane:
   the cross-monad impl-closeness lifting brick, the per-query Eq. 53 coupling, and
   `hyb12Step_of_resampleSplit`.
3. CO25 Claim 5.23 (`Hyb23Step`): `Hyb23DecodedQueryResidual` (the paper's query
   re-format, `= 0`; open core = the game-level lift, blocked on upstream `private`
   parser visibility), `Hyb23MemoTransparencyResidual`, `Hyb23SaltErasureResidual`;
   reduction `hyb23Step_of_saltedSplit` proven. **Structural flag (decide upstream)**:
   the salt-erasure leg appears genuinely *false* for `δ > 0` (salt-grinding
   distinguisher) — CO25 keeps the salted FS oracle through Hyb₄; restrict to `δ = 0` or
   re-key the eager surface on salted statements. The memo-transparency exact-`0` is
   also doubtful (repeat-key squeeze re-exposure is a birthday event).
4. CO25 Claim 5.24 (`Hyb34Step`): `Hyb34DivergenceResidual` / `Hyb34CollapseResidual`
   (the symmetric Eq. 55 halves at `claim5_24Bound/2` each; satisfiable only for
   `1 ≤ L`, see `claim5_24Bound_nonneg`). Proven in the lane: the εB per-query
   determinism layer (eager-table keystone + hit-only coherent serve) and
   `hyb34Step_of_divergence_collapse`; the generic skeleton
   `VerifierReplay.hyb34Step_of_strictSplit` remains available for asymmetric splits
   (consumed here by `keyLemmaEager_of_steps_strictSplit`).

Open residuals **off the critical path** (bad-event bookkeeping for the §5.6 analysis,
feeding the Claim 5.21/5.24 trace arguments):

5. `KeyLemmaFoundations.Lemma5_12HonestResidual` / `Lemma5_14HonestResidual` /
   `Lemma5_16HonestResidual` (M2) — `¬E ⇒ ¬E_*honest` backtrack case analyses;
   consumed by `BirthdayBound.probEvent_honestBad_le_probEvent_E` and
   `BirthdayBound.honestBad_birthday_of_residuals`. Not attacked in round 2.
6. `BirthdayBound.Lemma5_8EagerBirthdayResidual` — subsumed by item 1 (either
   granularity discharges it via `Hyb01Step.lemma5_8Eager_of_freshSplit`).

**Closed in round 1** (formerly open in `KeyLemmaFoundations`):
`D2sQueryStepGSpecBudgetResidual` (F4), `D2fOuterImplSharedBudgetResidual` (F4b),
`SimulatedProverChallengeBudgetResidual` (M1c), `SimulatedProverSharedBudgetResidual` (M1d)
— all proven in `SimulatorBudgets`. Round 2 closed no step residual; it delivered the four
split skeletons above (all proven, axiom-clean) and the frontier composition in
`KeyLemmaFrontier`.

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
