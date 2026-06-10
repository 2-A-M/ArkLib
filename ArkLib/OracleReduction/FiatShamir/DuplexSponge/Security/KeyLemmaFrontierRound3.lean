/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFrontier
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Align
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Accounting
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Delta0
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackLemmas

/-!
# CO25 Lemma 5.1 — round-3 assembly: the `δ = 0` frontier and the M2 fold

Round 3 ran four lanes (`Hyb12Align`, `Hyb12Accounting`, `Hyb23Delta0`, `BacktrackLemmas`);
none of the round-2 step residuals closed outright, but each lane delivered proven split
skeletons onto strictly finer residuals, plus two structural verdicts:

- **`δ = 0` is the honest home of the eager ladder**: the salt-erasure leg of Claim 5.23
  (false for `δ > 0`) has its distributional content *proven* at `δ = 0`
  (`Hyb23Delta0.hyb23SaltErasure_delta0_of_lift`), modulo one deterministic fixed-table
  bisimulation (`Hyb23SaltErasureLiftDelta0Residual`).
- **The raw-trace M2 surface is dead**: `Lemma5_12HonestResidual` is machine-checked FALSE
  (`BacktrackLemmas.lemma5_12HonestResidual_not_universal`), while the dedup'd-trace cores
  of CO25 Lemmas 5.12/5.14/5.16 are PROVEN (`lemma5_1{2,4,6}Honest_of_noRedundant`).

This module wires both into the tightest honest top-level theorems:

## The `δ = 0` frontier (CO25 Lemma 5.1, eager surface, unsalted DSFS)

- `hyb12Step_of_finestResiduals` (any `δ`) — the Claim 5.22 step from its six finest
  residuals, composing `Hyb12Align.hyb12ResampleAlign_of_lazySplit` and
  `Hyb12Accounting.hyb12BiasAccounting_of_freshPipeline` through
  `Hyb12Step.hyb12Step_of_resampleSplit`.
- `keyLemmaEagerDelta0_of_finestResiduals` — **the round-3 exact frontier at `δ = 0`**:
  thirteen finest open residuals imply the full eager key lemma. The Claim 5.23 lane needs
  only {decoded-query lift, memo transparency, fixed-table lift} — salt erasure is no
  longer a hypothesis.
- `keyLemmaEagerDelta0_of_finestResidualsEps23` — **the honest headline**: the memo
  transparency leg (whose exact-`0` form is doubtful *also* at `δ = 0` — the repeat-key
  re-exposure event is salt-free) consumed in ε-budget form, with any
  `ε ≤ 7/(2|Σ|^c)` absorbed by the proven F1b slack
  (`Hyb23Delta0.keyLemmaEager_of_steps_eps23`) at the **unchanged** `ηStarPaper` bound.

Honest flags carried from the lanes (read the lane docstrings before attacking):
`Hyb12RepeatDerivationResidual` is DOUBTFUL for non-injective decoders (true for injective
ones; honest general repair = birthday-budgeted relaxation); the exact-`0`
`Hyb23MemoTransparencyResidual` is doubtful at every `δ`; the Claim 5.24 split needs
`1 ≤ L`.

## The M2 fold (E-mass plumbing of the Claim 5.21/5.24 lanes, M2-free on dedup'd traces)

`BirthdayBound.probEvent_honestBad_le_probEvent_E` consumed the three raw-trace M2
residuals — of which the 5.12 one is now machine-checked false. The honest repair, executed
here: CO25 states the §5.6 events for the *deduplicated* trace, `E` already reads
`removeRedundantEntryDS`, and the dedup output carries its redundancy-freeness proof. So on
the dedup'd surface the domination is **unconditional**:

- `E_dedup_congr` / `E_removeRedundant_iff` — `E` is invariant under dedup
  (`E ((removeRedundantEntryDS tr).1) ↔ E tr`).
- `probEvent_honestBadDedup_le_probEvent_E` — honest bad events *on the dedup'd trace* are
  dominated by `Pr[E]`, with **no residual hypotheses** (the proven
  `lemma5_1{2,4,6}Honest_of_noRedundant` cores plug in directly).
- `honestBadDedup_birthday_of_lemma5_8` — the §5.6 → §5.8 channel of
  `BirthdayBound.honestBad_birthday_of_residuals` with the three M2 hypotheses **deleted**:
  only `Lemma5_8EagerBirthdayResidual` remains.

Downstream (the `E`-mass analyses of `FreshTraceEventResidual` and
`Hyb34DivergenceResidual`) should consume the dedup'd-trace channel; the raw-trace channel
survives only via the (partly false) corner residuals of `BacktrackLemmas`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.KeyLemmaFrontierRound3

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

-- The frontier theorems share one DSFS-wide variable block; each hypothesis uses only a
-- slice of it (repo precedent: the sibling lane modules and `KeyLemmaFrontier`).
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## The M2 fold: honest bad events on the dedup'd trace, no residual hypotheses

This section is deliberately placed *before* the DSFS variable block: its statements need
only `[SpongeUnit U] [SpongeSize]` (plus the eager-carrier instances for the birthday
assembly), exactly like their `BirthdayBound` counterparts. -/

section HonestBadDedup

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- `E` is a function of the deduplicated trace alone: traces with equal dedups carry equal
`E`-events (every disjunct of `E` reads `removeRedundantEntryDS`). -/
lemma E_dedup_congr {tr tr' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : removeRedundantEntryDS tr = removeRedundantEntryDS tr') :
    E tr ↔ E tr' := by
  unfold BadEventDS.E BadEventDS.combined BadEventDS.capacitySegmentDup
    BadEventDS.capacitySegmentDupHash BadEventDS.capacitySegmentDupPerm
    BadEventDS.capacitySegmentDupPermInv BadEventDS.notFunction
  rw [h]

/-- `E` is invariant under deduplication: the dedup'd trace (which is redundancy-free by
construction, hence a dedup fixed point) carries the same `E`-event as the raw trace. -/
lemma E_removeRedundant_iff (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    E ((removeRedundantEntryDS tr).1 : QueryLog (duplexSpongeChallengeOracle StmtIn U))
      ↔ E tr :=
  E_dedup_congr
    (BacktrackLemmas.removeRedundantEntryDS_eq_self _ (removeRedundantEntryDS tr).2)

/-- **The M2 fold (R1e, dedup'd surface, unconditional)**: for any probabilistic experiment
exposing a trace and a target state, the probability that some backtrack family of the
*deduplicated* trace witnesses an honest bad event (CO25 Defs. 5.11/5.13/5.15) is at most
`Pr[E]` — with **no** M2 residual hypotheses: the proven redundancy-free cores
`BacktrackLemmas.lemma5_1{2,4,6}Honest_of_noRedundant` discharge them, because the dedup'd
trace carries its own `NoRedundantEntryDS` witness and `E` is dedup-invariant. This is the
CO25 §5.6 channel as the paper states it (events over the deduplicated trace); the raw-trace
variant (`BirthdayBound.probEvent_honestBad_le_probEvent_E`) keeps its hypotheses, of which
the 5.12 one is machine-checked unsatisfiable in general. -/
theorem probEvent_honestBadDedup_le_probEvent_E
    {β : Type} (game : ProbComp β)
    (tr : β → QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (st : β → CanonicalSpongeState U) :
    Pr[ fun z => ∃ S : Backtrack.S_BT
          ((removeRedundantEntryDS (tr z)).1 :
            QueryLog (duplexSpongeChallengeOracle StmtIn U)) (st z),
        E_inv_honest ((removeRedundantEntryDS (tr z)).1) (st z) S
          ∨ E_fork_honest ((removeRedundantEntryDS (tr z)).1) (st z) S
          ∨ E_time_honest ((removeRedundantEntryDS (tr z)).1) (st z) S | game]
      ≤ Pr[ fun z => E (tr z) | game] := by
  refine probEvent_mono'' fun z hz => ?_
  obtain ⟨S, hS⟩ := hz
  by_contra hE
  have hE' : ¬ E ((removeRedundantEntryDS (tr z)).1 :
      QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
    fun h => hE ((E_removeRedundant_iff (tr z)).mp h)
  rcases hS with h | h | h
  · exact BacktrackLemmas.lemma5_12Honest_of_noRedundant _ _ S
      (removeRedundantEntryDS (tr z)).2 hE' h
  · exact BacktrackLemmas.lemma5_14Honest_of_noRedundant _ _ S
      (removeRedundantEntryDS (tr z)).2 hE' h
  · exact BacktrackLemmas.lemma5_16Honest_of_noRedundant _ _ S
      (removeRedundantEntryDS (tr z)).2 hE' h

/-- **R1 assembly, M2-free**: the dedup'd-trace honest bad events of the eager
`D_𝔖`-carrier game obey the birthday bound given `Lemma5_8EagerBirthdayResidual` **alone**
— the three M2 hypotheses of `BirthdayBound.honestBad_birthday_of_residuals` are deleted
(folded in as the proven redundancy-free cores). This is the §5.6 → §5.8 channel the
Claim 5.21/5.24 `E`-mass analyses should consume. -/
theorem honestBadDedup_birthday_of_lemma5_8
    [Fintype U] [DecidableEq U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (h58 : BirthdayBound.Lemma5_8EagerBirthdayResidual StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT
          ((removeRedundantEntryDS z.2).1 :
            QueryLog (duplexSpongeChallengeOracle StmtIn U)) st₀,
          E_inv_honest ((removeRedundantEntryDS z.2).1) st₀ S
            ∨ E_fork_honest ((removeRedundantEntryDS z.2).1) st₀ S
            ∨ E_time_honest ((removeRedundantEntryDS z.2).1) st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ BirthdayBound.lemma5_8Bound U T := by
  refine le_trans (ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) ?_) (h58 P T hT)
  exact probEvent_honestBadDedup_le_probEvent_E _
    (fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => z.2) (fun _ => st₀)

end HonestBadDedup

/-! ## The DSFS variable block (shared by the frontier theorems below) -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-! ## Claim 5.22 from its six finest residuals (any `δ`) -/

/-- **Claim 5.22 at the finest round-3 granularity** (any `δ`): the two fiber-resample
alignment legs (`Hyb12Align`: lazy/eager + repeat-derivation through the memoized pivot
`Hyb12MidMemo`) and the four bias-accounting legs (`Hyb12Accounting`: two eager↔lazy
alignments onto the fresh pivot + the two pipeline budgets feeding the proven `θ★`
accounting `tvDist_hyb2GameFresh_le`) assemble into the full `Hyb12StepResidual`.
Honest flag: `Hyb12RepeatDerivationResidual` is doubtful for non-injective decoders (see
its docstring); all reductions consumed here are proven and axiom-clean. -/
theorem hyb12Step_of_finestResiduals [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hLazy : Hyb12Align.Hyb12LazyEagerResampleResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hAlignE : Hyb12Accounting.Hyb2FreshAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hAlignMid : Hyb12Accounting.Hyb12MidFreshAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hProv : Hyb12Accounting.Hyb12ProverPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P δ)
    (hVerif : Hyb12Accounting.Hyb12VerifierPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  Hyb12Step.hyb12Step_of_resampleSplit T_H T_P δ oImpl
    (Hyb12Align.hyb12ResampleAlign_of_lazySplit T_H T_P δ oImpl hLazy hRepeat)
    (Hyb12Accounting.hyb12BiasAccounting_of_freshPipeline T_H T_P δ oImpl
      hAlignMid hAlignE hProv hVerif)

/-! ## The `δ = 0` frontier -/

/-- **The round-3 `δ = 0` frontier, exact form** (CO25 Lemma 5.1, eager surface, unsalted
DSFS transform): the thirteen finest open residuals imply the full eager key lemma at
`δ = 0`. Relative to the round-2 frontier (`KeyLemmaFrontier.keyLemmaEager_of_finestResiduals`):

- the Claim 5.22 lane is consumed at the finest (six-residual) granularity;
- the Claim 5.23 salt-erasure leg — *false* for `δ > 0` — is **gone**: its distributional
  content is proven at `δ = 0` (`Hyb23Delta0.hyb23SaltErasure_delta0_of_lift`), leaving the
  deterministic fixed-table lift `Hyb23SaltErasureLiftDelta0Residual`.

Honest flags: `hRepeat` is doubtful for non-injective decoders and `h23B`'s exact-`0` is
doubtful at every `δ` (use `keyLemmaEagerDelta0_of_finestResidualsEps23` for the honest
ε-budget routing); the Claim 5.24 split needs `1 ≤ L`. Every reduction consumed here is
proven and axiom-clean. -/
theorem keyLemmaEagerDelta0_of_finestResiduals
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
    -- Claim 5.22 lane (finest granularity)
    (hLazy : Hyb12Align.Hyb12LazyEagerResampleResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hAlignE : Hyb12Accounting.Hyb2FreshAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hAlignMid : Hyb12Accounting.Hyb12MidFreshAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hProv : Hyb12Accounting.Hyb12ProverPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P 0)
    (hVerif : Hyb12Accounting.Hyb12VerifierPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0)
    -- Claim 5.23 lane at `δ = 0` (no salt-erasure hypothesis)
    (h23A : Hyb23Step.Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h23B : Hyb23Step.Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h23L : Hyb23Delta0.Hyb23SaltErasureLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    -- Claim 5.24 lane
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  Hyb34Step.keyLemmaEager_of_steps_divergenceCollapse T_H T_P 0 Salt oImpl
    (Hyb01Step.hyb01Step_of_offEventCoupling_of_freshSplit T_H T_P 0 oImpl h01C
      εsw εev h01sw h01ev h01sum)
    (hyb12Step_of_finestResiduals T_H T_P 0 oImpl hLazy hRepeat hAlignE hAlignMid
      hProv hVerif)
    (Hyb23Delta0.hyb23Step_delta0_of_lift T_H T_P Salt oImpl h23A h23B h23L)
    h34A h34B

/-- **The round-3 `δ = 0` frontier, ε-budget form (the honest headline)**: same as
`keyLemmaEagerDelta0_of_finestResiduals`, but the memo-transparency leg — whose exact-`0`
form is doubtful at every `δ` (the repeat-key raw-`ρ̂ᵢ` re-exposure event is a
permutation-state collision, salt-free) — is consumed with an ε-budget
`ε ≤ 7/(2|Σ|^c)`, absorbed by the proven F1b slack
(`Hyb23Delta0.claimSum_add_le_ηStarPaper`) at the **unchanged** `ηStarPaper` bound. The
M1c/M1d witness budgets are discharged by the proven `SimulatorBudgets` theorems.
Caveat (from the `Hyb23Delta0` header): the slack is linear in `t` while the re-exposure
event is birthday-quadratic — for large budgets the honest route is re-stating Claims
5.21/5.24 across the memo switch, not this additive ε. -/
theorem keyLemmaEagerDelta0_of_finestResidualsEps23
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
    -- Claim 5.22 lane (finest granularity)
    (hLazy : Hyb12Align.Hyb12LazyEagerResampleResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hAlignE : Hyb12Accounting.Hyb2FreshAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hAlignMid : Hyb12Accounting.Hyb12MidFreshAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hProv : Hyb12Accounting.Hyb12ProverPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P 0)
    (hVerif : Hyb12Accounting.Hyb12VerifierPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0)
    -- Claim 5.23 lane at `δ = 0`, memo transparency with ε-budget
    (h23A : Hyb23Step.Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h23B : Hyb23Delta0.Hyb23MemoTransparencyEpsResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      T_H T_P 0 Salt oImpl ε)
    (h23L : Hyb23Delta0.Hyb23SaltErasureLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    -- Claim 5.24 lane
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  Hyb23Delta0.keyLemmaEager_of_steps_eps23 T_H T_P 0 Salt oImpl hε
    (Hyb01Step.hyb01Step_of_offEventCoupling_of_freshSplit T_H T_P 0 oImpl h01C
      εsw εev h01sw h01ev h01sum)
    (hyb12Step_of_finestResiduals T_H T_P 0 oImpl hLazy hRepeat hAlignE hAlignMid
      hProv hVerif)
    (Hyb23Delta0.hyb23StepEps_delta0_of_lift T_H T_P Salt oImpl h23A h23B h23L)
    (Hyb34Step.hyb34Step_of_divergence_collapse T_H T_P 0 Salt oImpl h34A h34B)
    (SimulatorBudgets.simulatedProverChallengeBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := 0) (Salt := Salt) (T_H := T_H) (T_P := T_P))
    (SimulatorBudgets.simulatedProverSharedBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := 0) (Salt := Salt) (T_H := T_H) (T_P := T_P))

end DuplexSpongeFS.KeyLemmaFrontierRound3

#print axioms DuplexSpongeFS.KeyLemmaFrontierRound3.E_dedup_congr
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound3.E_removeRedundant_iff
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound3.probEvent_honestBadDedup_le_probEvent_E
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound3.honestBadDedup_birthday_of_lemma5_8
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound3.hyb12Step_of_finestResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound3.keyLemmaEagerDelta0_of_finestResiduals
#print axioms DuplexSpongeFS.KeyLemmaFrontierRound3.keyLemmaEagerDelta0_of_finestResidualsEps23

end
