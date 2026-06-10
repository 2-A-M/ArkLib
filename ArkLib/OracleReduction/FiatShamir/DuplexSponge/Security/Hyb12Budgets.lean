/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Accounting
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets

/-!
# CO25 Claim 5.22 — the two pipeline budget residuals of `Hyb12Accounting`

This module attacks the two F4/M1c-genre bookkeeping residuals left open by
`Hyb12Accounting` (the `θ★` bias-accounting pipeline for `Hyb12Mid → Hyb₂`):

## Proven here (no `sorry`, axiom-clean)

1. **`hyb12ProverPipelineBudget` — `Hyb12ProverPipelineBudgetResidual` is true** (B3, CO25
   §5.4 / Eq. 53 prover side): the `d2fRaw`-with-logging prover pipeline at the `Hyb₂`
   instantiation makes at most `θ★ = tₚ` challenge-oracle queries whenever the malicious
   prover makes at most `tₚ` forward-perm queries. The proof replays the
   `SimulatorBudgets.simulatedProverChallengeBudget` (M1c) pattern at the
   `gImplDecodedChallenge` realization:
   - `gImplDecodedChallenge` makes exactly one `eSpec` challenge query per `gSpec` query
     (the `ψ⁻¹` preimage sampler is challenge-free, `uniformDeserializePreimage_left_free`);
   - F4 (`d2sQueryStepGSpecBudget`: ≤ 1 `gSpec` query per dispatcher step, only on a
     forward-perm query) transfers through the `d2sQueryImpl` stack via F3a;
   - the composed `d2fOuterImpl` step budget transfers through `d2fRaw` via F3b;
   - the `loggingOracle` wrapper is budget-transparent
     (VCVio's `isQueryBoundP_run_simulateQ_loggingOracle_iff`).

2. **`hyb12VerifierPipelineBudget_of_oncePerRound` — the proven reduction for B4**: the
   verifier-side residual `Hyb12VerifierPipelineBudgetResidual` follows from the
   logging-stripped `Hyb12VerifierOncePerRoundResidual` below (same statement at the bare
   `d2fRaw` layer), again by logging budget transparency.

3. **The round-indexed dispatcher toolkit** (the provable refinement of F4 needed to attack
   the open core): the round of the §5.4 Item 4(e)i `gᵢ` query is `backTrack`'s output
   round, a *state-dependent* classifier, so the F3a/F3b per-step carriers (whose budgets
   may depend only on the source query index) **cannot** transport a per-round budget.
   What they *can* transport is proven here:
   - `d2sQueryStep_round_budget` — round-indexed F4: per dispatcher step, at most
     `d2sStepRoundFires i qq st` round-`i` `gSpec` queries, where `d2sStepRoundFires`
     is `1` exactly when the step is a forward-perm query whose `backTrack` at the current
     state succeeds at round `i` with codec-image messages (branch-tree analysis of
     `d2sHandleForwardPermQuery`/`d2sHandleBacktrackSome`);
   - `d2sQueryImpl_decoded_round_budget` / `d2fOuterImpl_decoded_round_step` — the same
     fire-classified budget lifted through the `Hyb₂` pipeline implementation, classifying
     outer challenge queries by `challengeRoundOf · = some i`;
   - `isQueryBoundP_simulateQ_stateT2_optionT_fireOnce` — the **fire-once carrier**: if a
     per-step budget is `1` exactly on `Fire`-steps, firing reaches only `Dead` states,
     `Dead` is stable, and `Dead` states never fire, then the whole simulation makes at
     most one target query. This is the generic counting brick that converts a no-refire
     invariant into the `≤ 1` budget.

## Open core (named `*Residual : Prop`, NOT proven) — strictly finer than B4

- `Hyb12VerifierOncePerRoundResidual` — the bare (un-logged) verifier pipeline derives each
  round's challenge at most once. By the toolkit above, this reduces to a **no-refire
  invariant for `backTrack` along the honest verifier's run**: once the dispatcher has
  fired the round-`i` derivation, no later honest-verifier perm query can make `backTrack`
  succeed at round `i` again (CO25 implicitly uses chain-length monotonicity of the honest
  replay here). That is a §5.2 backtrack-analysis obligation of the `BacktrackLemmas`
  genre — the `Dead` certificate for `isQueryBoundP_simulateQ_stateT2_optionT_fireOnce` —
  and is *not* discharged by per-step bookkeeping. **Honest doubt flag**: on sampled-
  capacity collision paths the backward scan may conceivably re-parse round `i` without a
  fork abort; whether the residual holds on *every* support path (as `IsQueryBoundP`
  demands) is exactly the open analysis, mirroring the Lemma 5.12 raw-trace subtlety.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb12Budgets

open Backtrack DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations
open KeyLemmaHybrids Hyb12Accounting

open private d2sHandleForwardPermQuery d2sHandleBacktrackSome d2sInCodecImagePredicate
  from ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform

open private d2fAuxImpl isQueryBoundP_run2_bind isQueryBoundP_run2_lift_bind
  isQueryBoundP_run2_lift_failure isQueryBoundP_simulateQ_inclusion d2fOuterImpl_run_inl
  d2fOuterImpl_run_inr d2sHandleBacktrackNoResult_left_budget d2sSampleState_left_budget
  d2sRateBlocksFromChallenge_left_budget d2sSynthesizeStateFromRateBlocks_left_budget
  d2sHandleBacktrackSome_left_budget
  from ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## Generic `IsQueryBoundP` bricks -/

section GenericBricks

universe u

/-- `IsQueryBoundP` is antitone in the target predicate: a budget for `p`-queries bounds the
queries of any sub-predicate `q ⊆ p`. -/
theorem isQueryBoundP_mono_pred {ι₁ : Type u} {spec : OracleSpec ι₁} {α : Type u}
    {p q : ι₁ → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ t, q t → p t) {oa : OracleComp spec α} {b : ℕ}
    (h : IsQueryBoundP oa p b) : IsQueryBoundP oa q b := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h ⊢
      refine ⟨?_, fun u => ?_⟩
      · rcases h.1 with hnp | hpos
        · exact Or.inl fun hq => hnp (hpq t hq)
        · exact Or.inr hpos
      · have hu : IsQueryBoundP (mx u) p (if q t then b - 1 else b) := by
          have h2 := h.2 u
          by_cases hpt : p t
          · rw [if_pos hpt] at h2
            by_cases hqt : q t
            · rwa [if_pos hqt]
            · rw [if_neg hqt]
              exact h2.mono (Nat.sub_le b 1)
          · rw [if_neg hpt] at h2
            rw [if_neg fun hqt => hpt (hpq t hqt)]
            exact h2
        exact ih u hu

variable {ι' : Type} {spec' : OracleSpec ι'} {q : ι' → Prop} [DecidablePred q]

/-- Tail companion of `isQueryBoundP_run2_lift_bind`: budget transfer through a bare
`StateT.lift ∘ OptionT.lift` (no following bind). -/
private lemma isQueryBoundP_run2_lift {σ α : Type}
    {oa : OracleComp spec' α} {b : ℕ} (st : σ)
    (h : IsQueryBoundP oa q b) :
    IsQueryBoundP
      (((StateT.lift (OptionT.lift oa) : StateT σ (AbortComp spec') α).run st).run) q b := by
  rw [← bind_pure (StateT.lift (OptionT.lift oa) : StateT σ (AbortComp spec') α)]
  refine isQueryBoundP_run2_lift_bind (n := b) (m := 0) h (fun a => ?_)
  simp only [StateT.run_pure, OptionT.run_pure]
  exact isQueryBoundP_pure _ _ _

/-- **Fire-once budget carrier**: through a two-`StateT`/`OptionT` simulation whose per-step
target budget is `1` exactly on (state-dependent) `Fire`-steps, the whole run makes at most
one target query — provided firing lands in `Dead` first-component states, `Dead` is stable
under every step, and `Dead` states never fire. This converts a *no-refire invariant* (the
`Dead` certificate, e.g. the backtrack no-refire analysis for the honest DSFS verifier)
into the CO25 Eq. 53 once-per-round budget; companion of
`KeyLemmaFoundations.isQueryBoundP_simulateQ_stateT2_optionT_of_step`, whose per-step
budgets may depend only on the source query and hence cannot express "at most once
globally". -/
theorem isQueryBoundP_simulateQ_stateT2_optionT_fireOnce
    {ι₁ : Type} {spec : OracleSpec ι₁} {α σ₁ σ₂ : Type}
    {impl : QueryImpl spec (StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec'))))}
    (Fire : (t : ι₁) → σ₁ → Prop) [∀ t s₁, Decidable (Fire t s₁)]
    (Dead : σ₁ → Prop) [DecidablePred Dead]
    (hstep : ∀ t s₁ s₂, IsQueryBoundP ((((impl t).run s₁).run s₂).run) q
      (if Fire t s₁ then 1 else 0))
    (hdead_nofire : ∀ t s₁, Dead s₁ → ¬ Fire t s₁)
    (hfire_dead : ∀ t s₁ s₂, Fire t s₁ →
      ∀ x ∈ support ((((impl t).run s₁).run s₂).run),
        ∀ (u : spec.Range t) (s₁' : σ₁) (s₂' : σ₂), x = some ((u, s₁'), s₂') → Dead s₁')
    (hdead_stable : ∀ t s₁ s₂, Dead s₁ →
      ∀ x ∈ support ((((impl t).run s₁).run s₂).run),
        ∀ (u : spec.Range t) (s₁' : σ₁) (s₂' : σ₂), x = some ((u, s₁'), s₂') → Dead s₁')
    {oa : OracleComp spec α} (s₁ : σ₁) (s₂ : σ₂) :
    IsQueryBoundP ((((simulateQ impl oa).run s₁).run s₂).run) q 1 := by
  suffices h : ∀ (s₁ : σ₁) (s₂ : σ₂),
      IsQueryBoundP ((((simulateQ impl oa).run s₁).run s₂).run) q
        (if Dead s₁ then 0 else 1) from
    (h s₁ s₂).mono (by split <;> omega)
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s₁ s₂
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      intro s₁ s₂
      rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind, OptionT.run_bind]
      unfold Option.elimM
      have heq : ((((liftM (impl t) : StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))
            (spec.Range t)).run s₁).run s₂).run)
          = ((((impl t).run s₁).run s₂).run) := by
        simp
      have hstep' : IsQueryBoundP
          ((((liftM (impl t) : StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))
            (spec.Range t)).run s₁).run s₂).run)
          q (if Fire t s₁ then 1 else 0) := by
        rw [heq]
        exact hstep t s₁ s₂
      have hrest : ∀ x ∈ support ((((liftM (impl t) :
            StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))
            (spec.Range t)).run s₁).run s₂).run),
          IsQueryBoundP
            (Option.elim x (pure none)
              (fun uss => (((simulateQ impl (mx uss.1.1)).run uss.1.2).run uss.2).run))
            q (if Dead s₁ ∨ Fire t s₁ then 0 else 1) := by
        intro x hx
        rw [heq] at hx
        match x with
        | none => exact isQueryBoundP_pure _ _ _
        | some uss =>
            obtain ⟨⟨u, s₁'⟩, s₂'⟩ := uss
            by_cases hd : Dead s₁
            · have hd' : Dead s₁' := hdead_stable t s₁ s₂ hd _ hx u s₁' s₂' rfl
              have hcont := ih u s₁' s₂'
              rw [if_pos hd'] at hcont
              simpa [hd] using hcont
            · by_cases hf : Fire t s₁
              · have hd' : Dead s₁' := hfire_dead t s₁ s₂ hf _ hx u s₁' s₂' rfl
                have hcont := ih u s₁' s₂'
                rw [if_pos hd'] at hcont
                simpa [hd, hf] using hcont
              · have hcont := (ih u s₁' s₂').mono (m := 1) (by split <;> omega)
                simpa [hd, hf] using hcont
      refine (isQueryBoundP_bind hstep' hrest).mono ?_
      by_cases hd : Dead s₁
      · have hnf := hdead_nofire t s₁ hd
        simp [hd, hnf]
      · by_cases hf : Fire t s₁ <;> simp [hd, hf]

end GenericBricks

/-! ## DSFS context (mirrors `Hyb12Accounting`) -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {δ : ℕ}
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- `SpongeUnit` provides `Zero`; expose the canonical `Inhabited` locally. Not exported. -/
local instance : Inhabited U := ⟨0⟩

/-! ## B3 — the prover-stage `θ★` challenge budget

The M1c chain (`SimulatorBudgets.simulatedProverChallengeBudget`), replayed at the `Hyb₂`
instantiation: `gImplDecodedChallenge` in place of the Eq. 16 memoized bridge, the eager
`eSpec` surface in place of the basic-FS challenge oracle, and the `loggingOracle` wrapper
of `proverPipeline` stripped by budget transparency. -/

section ProverBudget

/-- The `ψ⁻¹` uniform-preimage sampler makes no challenge-summand (left) queries, over an
arbitrary challenge spec (generalizes
`KeyLemmaFoundations.uniformDeserializePreimage_left_budget`, which fixes the basic-FS
spec). -/
private lemma uniformDeserializePreimage_left_free
    {κ : Type} {challengeSpec : OracleSpec κ}
    {i : pSpec.ChallengeIdx} (ch : pSpec.Challenge i) :
    IsQueryBoundP
      (uniformDeserializePreimage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) ch)
      (fun j => j.isLeft = true) 0 := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [HasQuery.instOfMonadLift_query]
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp), fun u => isQueryBoundP_pure _ _ _⟩

/-- The `Hyb₂` `gᵢ`-realization makes exactly one challenge-summand query per `gSpec` query:
the single `eᵢ` query of CO25 §5.4 Item 4(e)i (the `ψ⁻¹` resampling step is
challenge-free). Per-step `gᵢ`-budget feeding the `θ★` accounting, the `Hyb₂` analogue of
`KeyLemmaFoundations.d2sCodecBridgeImplMemo_challenge_budget` (F5). -/
private lemma gImplDecodedChallenge_challenge_budget
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) (s : PUnit) :
    IsQueryBoundP
      (((gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        gq).run s).run)
      (fun j => j.isLeft = true) 1 := by
  unfold gImplDecodedChallenge
  refine isQueryBoundP_run2_lift_bind (n := 1) (m := 0) ?_ (fun ch => ?_)
  · -- the single `eᵢ` challenge query
    simp only [HasQuery.instOfMonadLift_query]
    exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => one_pos)
  · -- the `ψ⁻¹` resampling step is challenge-free
    exact isQueryBoundP_run2_lift _ (uniformDeserializePreimage_left_free ch)

/-- The `Hyb₂` `d2sQueryImpl` stack makes at most one challenge-summand query per source
query, and only on a forward-permutation query: F4 (≤ 1 `gSpec` query, only on perm)
composed with the one-query `gᵢ`-realization budget through F3a. Mirror of
`SimulatorBudgets.d2sQueryImpl_bridge_run_left_budget` at the `Hyb₂` instantiation. -/
private lemma d2sQueryImpl_decoded_run_challenge_budget
    (dsq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : PUnit) :
    IsQueryBoundP
      ((((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (m := StateT PUnit (OptionT (OracleComp
            (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)))))
          (gImpl := gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ))
          (auxImpl := d2fAuxImpl)
          dsq).run s₁).run s₂).run)
      (fun j => j.isLeft = true)
      (match dsq with | .inr (.inl _) => 1 | _ => 0) := by
  unfold d2sQueryImpl
  refine isQueryBoundP_run2_bind
    (n := match dsq with | .inr (.inl _) => 1 | _ => 0) (m := 0)
    ?_ (fun pairOpt m' => ?_)
  · -- the simulated dispatcher run: F3a with F4 + the one-query `gᵢ` budget
    refine isQueryBoundP_simulateQ_stateT_optionT_of_step
      (p := fun j => j.isLeft = true)
      (SimulatorBudgets.d2sQueryStepGSpecBudget (T_H := T_H) (T_P := T_P) dsq s₁)
      (fun t s => ?_) s₂
    match t with
    | Sum.inl gq =>
        simp only [Sum.isLeft_inl, QueryImpl.add_apply_inl]
        exact gImplDecodedChallenge_challenge_budget (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ) gq s
    | Sum.inr aux =>
        simp only [Sum.isLeft_inr, QueryImpl.add_apply_inr]
        have h0 : IsQueryBoundP
            ((query (spec := D2SChallengePlusUnitOracle (U := U)
                (eSpec (U := U) StmtIn pSpec δ)) (Sum.inr aux) :
                OracleComp (D2SChallengePlusUnitOracle (U := U)
                  (eSpec (U := U) StmtIn pSpec δ)) _)
              >>= fun u => pure (some (u, s)))
            (fun j => j.isLeft = true) 0 := by
          simp only [HasQuery.instOfMonadLift_query]
          exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
            ⟨Or.inl (by simp), fun u => isQueryBoundP_pure _ _ _⟩
        exact h0
  · -- the `match pairOpt` postlude makes no queries
    match pairOpt with
    | none => exact isQueryBoundP_run2_lift_failure _ _
    | some p =>
        simp only [StateT.run_pure, OptionT.run_pure]
        exact isQueryBoundP_pure _ _ _

/-- Per-step challenge budget of `d2fOuterImpl` at the `Hyb₂` instantiation: at most one
challenge-oracle query per source query, and only on a forward-permutation query —
classified directly by `Hyb12Accounting.challengeRoundOf`. Mirror of
`SimulatorBudgets.d2fOuterImpl_bridge_challenge_step`. -/
private lemma d2fOuterImpl_decoded_challenge_step
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : PUnit) :
    IsQueryBoundP
      ((((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
          (gImpl := gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ)) t).run s₁).run s₂).run)
      (fun j => (challengeRoundOf (oSpec := oSpec) (δ := δ) j).isSome = true)
      (if DuplexSpongeFS.dsQueryFlavor t = DuplexSpongeFS.DSQueryFlavor.perm
        then 1 else 0) := by
  match t with
  | Sum.inl qo =>
      rw [d2fOuterImpl_run_inl]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨Or.inl (by simp [challengeRoundOf]), fun u => isQueryBoundP_pure _ _ _⟩
  | Sum.inr dsq =>
      rw [d2fOuterImpl_run_inr]
      have hbound : (if DuplexSpongeFS.dsQueryFlavor
            (Sum.inr dsq : ι ⊕ (StmtIn ⊕ CanonicalSpongeState U
              ⊕ CanonicalSpongeState U)) = DuplexSpongeFS.DSQueryFlavor.perm
          then 1 else 0)
          = (match dsq with | .inr (.inl _) => 1 | _ => 0) := by
        match dsq with
        | Sum.inl _ => simp [DuplexSpongeFS.dsQueryFlavor]
        | Sum.inr (Sum.inl _) => simp [DuplexSpongeFS.dsQueryFlavor]
        | Sum.inr (Sum.inr _) => simp [DuplexSpongeFS.dsQueryFlavor]
      rw [hbound]
      exact isQueryBoundP_simulateQ_inclusion
        (d2sQueryImpl_decoded_run_challenge_budget (T_H := T_H) (T_P := T_P) dsq s₁ s₂)
        (fun t => by cases t <;> simp [challengeRoundOf])

/-- **B3 — `Hyb12ProverPipelineBudgetResidual` is true** (CO25 §5.4, Eq. 53 prover side):
the `d2fRaw`-with-logging prover pipeline at the `Hyb₂` instantiation makes at most
`θ★ = tₚ` challenge-oracle queries — one per forward-perm query of the malicious prover.
Logging transparency + F3b + the per-step `d2fOuterImpl` budget. -/
theorem hyb12ProverPipelineBudget :
    Hyb12ProverPipelineBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) T_H T_P δ := by
  intro P tₕ tₚ tₚᵢ hHash hPerm hPermInv
  unfold Hyb12Accounting.proverPipeline
  rw [isQueryBoundP_run_simulateQ_loggingOracle_iff]
  unfold d2fRaw
  exact isQueryBoundP_simulateQ_stateT2_optionT_of_step hPerm
    (fun t s₁ s₂ => d2fOuterImpl_decoded_challenge_step (oSpec := oSpec) t s₁ s₂)
    default default

end ProverBudget

/-! ## B4 — the verifier-stage once-per-round budget: proven reduction + open core -/

section VerifierBudget

/-- Open core for B4 — **once-per-round at the bare `d2fRaw` layer**: the (un-logged) honest
verifier replay through the `Hyb₂` dispatcher pipeline derives each round's challenge at
most once. By `d2fOuterImpl_decoded_round_step` below, the round-`i` challenge queries are
exactly the dispatcher steps whose `backTrack` fires at round `i` with codec-image
messages, so this residual is precisely a **no-refire invariant of `backTrack` along the
honest verifier's run** — the `Dead` certificate demanded by
`isQueryBoundP_simulateQ_stateT2_optionT_fireOnce`. That is a §5.2 backtrack-analysis
obligation (`BacktrackLemmas` genre), not per-step bookkeeping. -/
def Hyb12VerifierOncePerRoundResidual
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (messages : pSpec.Messages) (mm : PUnit)
    (i : pSpec.ChallengeIdx),
    IsQueryBoundP
      ((d2fRaw (T_H := T_H) (T_P := T_P)
        (gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        ((V.duplexSpongeFiatShamir.run
          stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)
        mm).run)
      (fun t => challengeRoundOf (oSpec := oSpec) (δ := δ) t = some i) 1

/-- **The proven reduction for B4**: `Hyb12VerifierPipelineBudgetResidual` follows from the
logging-stripped `Hyb12VerifierOncePerRoundResidual` (the `loggingOracle` wrapper is
budget-transparent). -/
theorem hyb12VerifierPipelineBudget_of_oncePerRound
    (h : Hyb12VerifierOncePerRoundResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12VerifierPipelineBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ := by
  intro V stmtIn messages mm i
  unfold Hyb12Accounting.verifierPipeline
  rw [isQueryBoundP_run_simulateQ_loggingOracle_iff]
  exact h V stmtIn messages mm i

end VerifierBudget

/-! ## The round-indexed dispatcher toolkit (round-indexed F4)

The per-round classification of a fired `gᵢ` query is *state-dependent*: the round is
`backTrack`'s output on the current dispatcher state. The F3a/F3b carriers transport only
query-indexed budgets, so the bricks below expose the fire-classified per-step budgets that
`isQueryBoundP_simulateQ_stateT2_optionT_fireOnce` consumes. -/

section RoundToolkit

/-- Classify a `d2sQueryOracles` index by the round of its `gSpec` summand. -/
def gSpecRoundOf
    (t : (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Domain) :
    Option pSpec.ChallengeIdx :=
  match t with
  | .inl gq => some gq.1
  | .inr _ => none

/-- Classify a `Hyb₂` mid-spec index (`eSpec + (Unit →ₒ U) + unifSpec`) by the round of its
challenge summand. -/
def midChallengeRoundOf
    (t : (D2SChallengePlusUnitOracle (U := U)
      (eSpec (U := U) StmtIn pSpec δ)).Domain) :
    Option pSpec.ChallengeIdx :=
  match t with
  | .inl qe => some qe.1
  | .inr _ => none

/-- A round-classified `gSpec` query is in particular a left-summand query. -/
private lemma gSpecRound_isLeft {i : pSpec.ChallengeIdx}
    (t : (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Domain)
    (ht : gSpecRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) t = some i) :
    t.isLeft = true := by
  match t with
  | .inl _ => rfl
  | .inr _ => simp [gSpecRoundOf] at ht

/-- The number of round-`i` `gᵢ` fires of one dispatcher step: `1` exactly on a forward-perm
query whose `backTrack` at the current state succeeds with codec-image messages at round
`i` (CO25 §5.4 Item 4(e)i), `0` otherwise. -/
noncomputable def d2sStepRoundFires (i : pSpec.ChallengeIdx)
    (qq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : ℕ :=
  match qq with
  | .inr (.inl stateIn) =>
      match backTrack (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with
      | .some out =>
          if d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true
              ∧ out.roundIdx = i
            then 1 else 0
      | _ => 0
  | _ => 0

/-- The §5.4 Item 4(e)i `gᵢ` query makes one round-`i` `gSpec` query iff its round is `i`. -/
private lemma d2sQueryG_round_budget (i j : pSpec.ChallengeIdx) (stmt : StmtIn)
    (salt : Vector U δ) (em : pSpec.EncodedMessagesBefore U j.1.castSucc) :
    IsQueryBoundP
      (d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) j stmt salt em)
      (fun t => gSpecRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        t = some i)
      (if j = i then 1 else 0) := by
  unfold d2sQueryG
  simp only [HasQuery.instOfMonadLift_query]
  refine (isQueryBoundP_query_iff _ _ _).mpr (fun hp => ?_)
  have hj : j = i := by simpa [gSpecRoundOf] using hp
  simp [hj]

/-- Round-indexed budget of the backtrack-success branch: one round-`i` `gSpec` query iff
the backtrack output is at round `i` with codec-image messages; none otherwise (the `gᵢ`
query of a round-`j ≠ i` fire is classified away, the non-image and lookup branches are
`gSpec`-free). -/
private lemma d2sHandleBacktrackSome_round_budget (i : pSpec.ChallengeIdx)
    (stateIn : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleBacktrackSome (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn out).run st).run)
      (fun t => gSpecRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        t = some i)
      (if d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true
          ∧ out.roundIdx = i
        then 1 else 0) := by
  unfold d2sHandleBacktrackSome
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases himg : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      out = true
  · rw [if_pos himg]
    have hbudget : (if d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) out = true ∧ out.roundIdx = i then 1 else 0)
        = (if out.roundIdx = i then 1 else 0) := by
      simp [himg]
    rw [hbudget]
    refine IsQueryBoundP.mono (isQueryBoundP_run2_lift_bind
      (n := if out.roundIdx = i then 1 else 0) (m := 0)
      (d2sQueryG_round_budget i out.roundIdx out.stmt out.salt out.encodedMessages)
      (fun sampledRhoHat => ?_)) (le_of_eq (Nat.add_zero _))
    split
    · -- Item 4(e)ii — forward cache hit
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
    · -- Item 4(e)iii — reshape + synthesize (`gSpec`-free)
      refine isQueryBoundP_run2_lift_bind (n := 0) (m := 0)
        (isQueryBoundP_mono_pred (gSpecRound_isLeft (i := i))
          (d2sRateBlocksFromChallenge_left_budget _)) (fun rateBlocks => ?_)
      refine isQueryBoundP_run2_bind (n := 0) (m := 0)
        (isQueryBoundP_mono_pred (gSpecRound_isLeft (i := i))
          (d2sSynthesizeStateFromRateBlocks_left_budget _ _)) (fun sc s' => ?_)
      obtain ⟨s_out, cache'⟩ := sc
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
  · rw [if_neg himg]
    have hbudget : (if d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) out = true ∧ out.roundIdx = i then 1 else 0) = 0 := by
      simp [himg]
    rw [hbudget]
    split
    · -- Item 4(d)i — cache hit
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
    · -- Item 4(d)ii — fresh sample (`gSpec`-free)
      refine IsQueryBoundP.mono (isQueryBoundP_run2_lift_bind (n := 0) (m := 0)
        (isQueryBoundP_mono_pred (gSpecRound_isLeft (i := i))
          d2sSampleState_left_budget)
        (fun sampled => by
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            OptionT.run_pure]
          exact isQueryBoundP_pure _ _ _)) (Nat.le_refl _)

/-- Round-indexed budget of the forward-perm handler: the dispatch over `backTrack`'s
outcome (abort / no-result / success). -/
private lemma d2sHandleForwardPermQuery_round_budget (i : pSpec.ChallengeIdx)
    (stateIn : CanonicalSpongeState U)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st).run)
      (fun t => gSpecRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        t = some i)
      (d2sStepRoundFires (T_H := T_H) (T_P := T_P) i (.inr (.inl stateIn)) st) := by
  unfold d2sHandleForwardPermQuery d2sStepRoundFires
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hbt : backTrack (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with
  | err =>
      exact isQueryBoundP_run2_lift_failure _ _
  | noResult =>
      exact isQueryBoundP_mono_pred (gSpecRound_isLeft (i := i))
        (d2sHandleBacktrackNoResult_left_budget _ _)
  | some out =>
      exact d2sHandleBacktrackSome_round_budget i stateIn out st

/-- **Round-indexed F4** — the §5.4 dispatcher `d2sQueryStep` makes at most
`d2sStepRoundFires i qq st` round-`i` `gSpec` queries: one exactly on a forward-perm query
whose `backTrack` fires at round `i` with codec-image messages, none otherwise. The
state-dependent refinement of `SimulatorBudgets.d2sQueryStepGSpecBudget`. -/
theorem d2sQueryStep_round_budget (i : pSpec.ChallengeIdx)
    (qq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) qq).run st).run)
      (fun t => gSpecRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        t = some i)
      (d2sStepRoundFires (T_H := T_H) (T_P := T_P) i qq st) := by
  match qq with
  | Sum.inl stmt =>
      exact isQueryBoundP_mono_pred (gSpecRound_isLeft (i := i))
        (SimulatorBudgets.d2sQueryStepGSpecBudget (T_H := T_H) (T_P := T_P)
          (Sum.inl stmt) st)
  | Sum.inr (Sum.inr stateOut) =>
      exact isQueryBoundP_mono_pred (gSpecRound_isLeft (i := i))
        (SimulatorBudgets.d2sQueryStepGSpecBudget (T_H := T_H) (T_P := T_P)
          (Sum.inr (Sum.inr stateOut)) st)
  | Sum.inr (Sum.inl stateIn) =>
      exact d2sHandleForwardPermQuery_round_budget i stateIn st

/-- The `Hyb₂` `gᵢ`-realization fires a round-`i` challenge query iff the `gSpec` query is
at round `i` (the single `eᵢ` query carries the *same* round as its `gSpec` key). -/
private lemma gImplDecodedChallenge_round_budget (i : pSpec.ChallengeIdx)
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) (s : PUnit) :
    IsQueryBoundP
      (((gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        gq).run s).run)
      (fun j => midChallengeRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) j = some i)
      (if gq.1 = i then 1 else 0) := by
  unfold gImplDecodedChallenge
  refine isQueryBoundP_run2_lift_bind (n := if gq.1 = i then 1 else 0) (m := 0)
    ?_ (fun ch => ?_)
  · -- the single `eᵢ` query carries the round of its `gSpec` key
    simp only [HasQuery.instOfMonadLift_query]
    refine (isQueryBoundP_query_iff _ _ _).mpr (fun hp => ?_)
    have hj : gq.1 = i := by simpa [midChallengeRoundOf] using hp
    simp [hj]
  · -- the `ψ⁻¹` resampling step is challenge-free
    refine isQueryBoundP_run2_lift _
      (isQueryBoundP_mono_pred (p := fun j => j.isLeft = true) ?_
        (uniformDeserializePreimage_left_free ch))
    intro t ht
    match t with
    | .inl _ => rfl
    | .inr _ => simp [midChallengeRoundOf] at ht

/-- Round-indexed fire-classified budget of the `Hyb₂` `d2sQueryImpl` stack: per source
query, at most `d2sStepRoundFires i dsq s₁` round-`i` challenge queries (F3a over the
round-indexed F4, with the round-preserving `gᵢ`-realization). -/
private lemma d2sQueryImpl_decoded_run_round_budget (i : pSpec.ChallengeIdx)
    (dsq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : PUnit) :
    IsQueryBoundP
      ((((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (m := StateT PUnit (OptionT (OracleComp
            (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)))))
          (gImpl := gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ))
          (auxImpl := d2fAuxImpl)
          dsq).run s₁).run s₂).run)
      (fun j => midChallengeRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) j = some i)
      (d2sStepRoundFires (T_H := T_H) (T_P := T_P) i dsq s₁) := by
  unfold d2sQueryImpl
  refine isQueryBoundP_run2_bind
    (n := d2sStepRoundFires (T_H := T_H) (T_P := T_P) i dsq s₁) (m := 0)
    ?_ (fun pairOpt m' => ?_)
  · refine isQueryBoundP_simulateQ_stateT_optionT_of_step
      (p := fun t => gSpecRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        t = some i)
      (d2sQueryStep_round_budget i dsq s₁) (fun t s => ?_) s₂
    match t with
    | Sum.inl gq =>
        simp only [QueryImpl.add_apply_inl]
        simpa only [gSpecRoundOf, Option.some.injEq] using
          gImplDecodedChallenge_round_budget (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ) i gq s
    | Sum.inr aux =>
        simp only [QueryImpl.add_apply_inr, gSpecRoundOf, reduceCtorEq, if_false]
        have h0 : IsQueryBoundP
            ((query (spec := D2SChallengePlusUnitOracle (U := U)
                (eSpec (U := U) StmtIn pSpec δ)) (Sum.inr aux) :
                OracleComp (D2SChallengePlusUnitOracle (U := U)
                  (eSpec (U := U) StmtIn pSpec δ)) _)
              >>= fun u => pure (some (u, s)))
            (fun j => midChallengeRoundOf (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
              (δ := δ) j = some i) 0 := by
          simp only [HasQuery.instOfMonadLift_query]
          exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
            ⟨Or.inl (by simp [midChallengeRoundOf]),
              fun u => isQueryBoundP_pure _ _ _⟩
        exact h0
  · match pairOpt with
    | none => exact isQueryBoundP_run2_lift_failure _ _
    | some p =>
        simp only [StateT.run_pure, OptionT.run_pure]
        exact isQueryBoundP_pure _ _ _

/-- The number of round-`i` fires of one outer pipeline step (shared `oSpec` queries fire
nothing). -/
noncomputable def d2fStepRoundFires (i : pSpec.ChallengeIdx)
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : ℕ :=
  match t with
  | .inr dsq => d2sStepRoundFires (T_H := T_H) (T_P := T_P) i dsq st
  | .inl _ => 0

/-- **Round-indexed fire-classified per-step budget of the `Hyb₂` pipeline**: per source
query, `d2fOuterImpl` at the `Hyb₂` instantiation makes at most
`d2fStepRoundFires i t s₁` round-`i` challenge queries (classified by
`challengeRoundOf · = some i`). This is the `hstep` input for the fire-once carrier: the
open `Hyb12VerifierOncePerRoundResidual` is exactly a `Dead` certificate (backtrack
no-refire along the honest verifier run) away from B4. -/
theorem d2fOuterImpl_decoded_round_step (i : pSpec.ChallengeIdx)
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : PUnit) :
    IsQueryBoundP
      ((((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
          (gImpl := gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ)) t).run s₁).run s₂).run)
      (fun j => challengeRoundOf (oSpec := oSpec) (δ := δ) j = some i)
      (d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t s₁) := by
  match t with
  | Sum.inl qo =>
      rw [d2fOuterImpl_run_inl]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨Or.inl (by simp [challengeRoundOf]), fun u => isQueryBoundP_pure _ _ _⟩
  | Sum.inr dsq =>
      rw [d2fOuterImpl_run_inr]
      exact isQueryBoundP_simulateQ_inclusion
        (d2sQueryImpl_decoded_run_round_budget (T_H := T_H) (T_P := T_P) i dsq s₁ s₂)
        (fun t => by cases t <;> simp [challengeRoundOf, midChallengeRoundOf])

end RoundToolkit

end DuplexSpongeFS.Hyb12Budgets

#print axioms DuplexSpongeFS.Hyb12Budgets.isQueryBoundP_mono_pred
#print axioms DuplexSpongeFS.Hyb12Budgets.isQueryBoundP_simulateQ_stateT2_optionT_fireOnce
#print axioms DuplexSpongeFS.Hyb12Budgets.hyb12ProverPipelineBudget
#print axioms DuplexSpongeFS.Hyb12Budgets.hyb12VerifierPipelineBudget_of_oncePerRound
#print axioms DuplexSpongeFS.Hyb12Budgets.d2sQueryStep_round_budget
#print axioms DuplexSpongeFS.Hyb12Budgets.d2fOuterImpl_decoded_round_step

end
