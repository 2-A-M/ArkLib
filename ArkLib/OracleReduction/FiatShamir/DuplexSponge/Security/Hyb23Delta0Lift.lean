/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Delta0
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFrontierRound3

/-!
# The `δ = 0` fixed-table salt-erasure lift — `Hyb23SaltErasureLiftDelta0Residual` is TRUE

Round 3 left the salt-erasure leg of CO25 Claim 5.23 at `δ = 0` reduced
(`Hyb23Delta0.hyb23SaltErasure_delta0_of_lift`, proven) to one named deterministic
obligation: `Hyb23SaltErasureLiftDelta0Residual` — at every *fixed* salted table `c`, the
`Hyb3SaltedMemo` game body (salted memoized Eq. 16 bridge + line-4 salt erasure) and the
`Hyb₃` body at the `delta0Salt`-section-restricted table (eager salt-erasing bridge +
identity line 4) have equal output distributions. All probabilistic content (the
uniform-table re-indexing) was already discharged; what remained was a `simulateQ`
bisimulation through `d2fRaw`/`loggingOracle`.

**This module proves that residual** — the two bodies are *equal computations*, not merely
equidistributed. The proof is a deterministic log-coupling bisimulation:

- `eraseSaltRawEntry`/`eraseSaltRawLog` — per-entry salt erasure on the **raw** (simulator-
  spec) query log, the pre-projection form of `Hyb23Step.eraseSaltLog`;
  `project_eraseSaltRawLog` commutes it with `projectChallengePlusUnitQueryLog`.
- `EraseLogCoupled` — the coupling relation: against the fixed tables `c` (salted world) and
  `saltSectionRestrict delta0Salt c` (eager world), the logged-and-table-instantiated runs
  of two computations are equal up to `eraseSaltRawLog` on the log channel.
- closure bricks: `EraseLogCoupled` is preserved by `pure`, `bind`, shared-`oSpec` queries,
  auxiliary sampling queries, and — the `δ = 0` content — *canonical-salt* FS-challenge
  queries (`saltSectionRestrict` makes the two table reads literally equal; `encode_delta0`
  puts every bridge-emitted key in canonical-salt form).
- `bridge_coupled` — the per-`gᵢ`-query layer: the salted memoized bridge and the eager
  bridge couple at every key and memo (hit: both pure; miss: one challenge query + one
  `ψ⁻¹` index draw, related entrywise).
- `inner_coupled` / `pipe_coupled` — the two structural inductions lifting the per-query
  layer through `d2sQueryStep` (the §5.4 Items 2–4 dispatcher) and through the full
  `d2fRaw` prover/verifier pipeline.
- **`hyb23SaltErasureLiftDelta0`** — the residual, proven: the two `hybGameEagerBody`s are
  equal `ProbComp` computations at every fixed table.
- **`hyb23SaltErasure_delta0`** — headline corollary: `Hyb23SaltErasureResidual` (CO25
  Claim 5.23, step C) holds **unconditionally** at `δ = 0` — the round-2 falsity flag is
  confined to `δ > 0`.
- `hyb23Step_delta0_of_AB` / `hyb23StepEps_delta0_of_AB` — the Claim 5.23 frontier at
  `δ = 0` shrinks to {step A, step B}: the fixed-table lift hypothesis is gone.
- `keyLemmaEagerDelta0_of_finestResiduals'` / `keyLemmaEagerDelta0_of_finestResidualsEps23'`
  — **the round-4 frontier**: the round-3 keystones with the lift hypothesis discharged.
  The eager Key Lemma at `δ = 0` now needs *twelve* finest residuals (exact form) — the
  Claim 5.23 lane is down to {decoded-query lift, memo transparency}.

Everything here is `sorry`-free and axiom-clean (`#print axioms` at the bottom).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb23Delta0Lift

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
  VerifierReplay Hyb23Step Hyb23Delta0

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it
-- (repo precedent: the sibling lane modules `Hyb23Delta0`, `SimulatorBudgets`).
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

/-! ## Raw-log salt erasure (the pre-projection form of `Hyb23Step.eraseSaltLog`) -/

section RawLog

variable {Salt : Type}

/-- Per-entry salt erasure on the **raw** simulator-spec log
`oSpec + D2SChallengePlusUnitOracle (fsChallengeOracle (StmtIn × Salt) pSpec)`: the salt
component of an FS-challenge key is dropped; shared and auxiliary entries are kept
verbatim. -/
def eraseSaltRawEntry :
    ((t : (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)).Domain) ×
      (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)).Range t) →
    ((t : (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)).Domain) ×
      (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)).Range t)
  | ⟨.inl q, r⟩ => ⟨.inl q, r⟩
  | ⟨.inr (.inl ⟨i, ((x, _s), msgs)⟩), ch⟩ => ⟨.inr (.inl ⟨i, (x, msgs)⟩), ch⟩
  | ⟨.inr (.inr aux), r⟩ => ⟨.inr (.inr aux), r⟩

/-- Raw-log salt erasure: entrywise `eraseSaltRawEntry`. -/
def eraseSaltRawLog
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec))) :
    QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle StmtIn pSpec)) :=
  log.map (eraseSaltRawEntry (oSpec := oSpec))

@[simp]
lemma eraseSaltRawLog_nil :
    eraseSaltRawLog (oSpec := oSpec) (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
      (Salt := Salt) [] = [] := rfl

lemma eraseSaltRawLog_cons (e) (l) :
    eraseSaltRawLog (oSpec := oSpec) (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (Salt := Salt) (e :: l)
      = eraseSaltRawEntry (oSpec := oSpec) e :: eraseSaltRawLog (oSpec := oSpec) l := rfl

lemma eraseSaltRawLog_append (l₁ l₂ : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec))) :
    eraseSaltRawLog (oSpec := oSpec) (l₁ ++ l₂)
      = eraseSaltRawLog (oSpec := oSpec) l₁ ++ eraseSaltRawLog (oSpec := oSpec) l₂ :=
  List.map_append ..

/-- The auxiliary-log projection commutes with salt erasure: projecting the salt-erased raw
log is the line-4 salt erasure of the projected raw log. This is the bridge between the raw
bisimulation logs and the `hybGameEagerBody` output surface. -/
lemma project_eraseSaltRawLog
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec))) :
    projectChallengePlusUnitQueryLog (U := U)
        (eraseSaltRawLog (oSpec := oSpec) log)
      = Hyb23Step.eraseSaltLog (oSpec := oSpec)
          (projectChallengePlusUnitQueryLog (U := U) log) := by
  unfold eraseSaltRawLog Hyb23Step.eraseSaltLog projectChallengePlusUnitQueryLog
  rw [List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun entry _ => ?_
  rcases entry with ⟨q | ⟨i, ⟨⟨x, s⟩, msgs⟩⟩ | aux, r⟩ <;> rfl

end RawLog

/-! ## Leg algebra: logged-and-instantiated runs of fixed-table computations

`leg impl Y := simulateQ impl ((simulateQ loggingOracle Y).run)` is the run of `Y` against
the fixed-table implementation `impl` carrying the raw query log. The three lemmas below
are its monad-morphism laws; everything downstream is phrased through them. -/

section LegAlgebra

universe u

variable {ι' : Type} {spec : OracleSpec ι'}

/-- The logged-and-instantiated run of a computation against a fixed implementation. -/
private def leg (impl : QueryImpl spec ProbComp) {β : Type}
    (Y : OracleComp spec β) : ProbComp (β × QueryLog spec) :=
  simulateQ impl ((simulateQ loggingOracle Y).run)

private lemma leg_pure (impl : QueryImpl spec ProbComp) {β : Type} (x : β) :
    leg impl (pure x : OracleComp spec β) = pure (x, []) := by
  unfold leg
  simp [loggingOracle]

private lemma leg_bind (impl : QueryImpl spec ProbComp) {β γ : Type}
    (A : OracleComp spec β) (B : β → OracleComp spec γ) :
    leg impl (A >>= B)
      = leg impl A >>= fun p =>
          (fun q => (q.1, p.2 ++ q.2)) <$> leg impl (B p.1) := by
  unfold leg
  rw [show (simulateQ loggingOracle (A >>= B)).run
      = (simulateQ loggingOracle A).run >>= fun p =>
          Prod.map id (p.2 ++ ·) <$> (simulateQ loggingOracle (B p.1)).run from
    OracleComp.withQueryLog_bind A B]
  rw [simulateQ_bind]
  exact bind_congr fun p => by rw [simulateQ_map]; rfl

private lemma leg_query_bind (impl : QueryImpl spec ProbComp) {β : Type}
    (t : spec.Domain) (k : spec.Range t → OracleComp spec β) :
    leg impl (liftM (spec.query t) >>= k)
      = impl t >>= fun u =>
          (fun p => (p.1, ⟨t, u⟩ :: p.2)) <$> leg impl (k u) := by
  unfold leg
  rw [OracleComp.run_simulateQ_loggingOracle_query_bind, simulateQ_bind,
    simulateQ_spec_query]
  exact bind_congr fun u => by rw [simulateQ_map]

end LegAlgebra

/-! ## Generic run-shape helpers for the `StateT`/`OptionT` towers -/

section RunShapes

variable {ι₁ ι₂ : Type} {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}

/-- Run shape of a `simulateQ` into `StateT σ (OptionT (OracleComp spec'))` at a
query-headed bind. -/
private lemma run1_simulateQ_query_bind {σ β : Type}
    (impl : QueryImpl spec (StateT σ (OptionT (OracleComp spec'))))
    (t : spec.Domain) (k : spec.Range t → OracleComp spec β) (s : σ) :
    ((simulateQ impl (liftM (spec.query t) >>= k)).run s).run
      = (((impl t).run s).run) >>= fun o =>
          match o with
          | none => pure none
          | some us => ((simulateQ impl (k us.1)).run us.2).run := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OptionT.run_bind]
  unfold Option.elimM
  refine bind_congr fun o => ?_
  match o with
  | none => rfl
  | some us => rfl

/-- Run shape of a `simulateQ` into `StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))`
at a query-headed bind. -/
private lemma run2_simulateQ_query_bind {σ₁ σ₂ β : Type}
    (impl : QueryImpl spec (StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))))
    (t : spec.Domain) (k : spec.Range t → OracleComp spec β) (s₁ : σ₁) (s₂ : σ₂) :
    (((simulateQ impl (liftM (spec.query t) >>= k)).run s₁).run s₂).run
      = ((((impl t).run s₁).run s₂).run) >>= fun o =>
          match o with
          | none => pure none
          | some uss => (((simulateQ impl (k uss.1.1)).run uss.1.2).run uss.2).run := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_bind,
    OptionT.run_bind]
  unfold Option.elimM
  refine bind_congr fun o => ?_
  match o with
  | none => rfl
  | some uss => rfl

/-- `pure` run shape in the two-state tower. -/
private lemma run2_simulateQ_pure {σ₁ σ₂ β : Type}
    (impl : QueryImpl spec (StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))))
    (x : β) (s₁ : σ₁) (s₂ : σ₂) :
    (((simulateQ impl (pure x : OracleComp spec β)).run s₁).run s₂).run
      = pure (some ((x, s₁), s₂)) := by
  simp [simulateQ_pure]

/-- `pure` run shape in the one-state tower. -/
private lemma run1_simulateQ_pure {σ β : Type}
    (impl : QueryImpl spec (StateT σ (OptionT (OracleComp spec'))))
    (x : β) (s : σ) :
    ((simulateQ impl (pure x : OracleComp spec β)).run s).run
      = pure (some (x, s)) := by
  simp [simulateQ_pure]

end RunShapes

/-! ## DSFS-specific run shapes: the `d2sQueryImpl` dispatcher and the auxiliary lift -/

section DispatcherShapes

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U] {δ : ℕ}
variable {κ : Type} {challengeSpec : OracleSpec κ} {M : Type}

/-- The right-injection inclusion implementation appearing in the `d2fOuterImpl` run shape
on duplex-sponge queries. -/
private def incl (challengeSpec : OracleSpec κ) :
    QueryImpl (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :=
  fun t =>
    (liftM ((D2SChallengePlusUnitOracle (U := U) challengeSpec).query t) :
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) _)

private lemma incl_apply (challengeSpec : OracleSpec κ)
    (t : (D2SChallengePlusUnitOracle (U := U) challengeSpec).Domain) :
    incl (oSpec := oSpec) challengeSpec t
      = liftM ((oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec).query
          (Sum.inr t)) := rfl

/-- Run shape of the §5.4 `d2sQueryImpl` dispatcher: the simulated `d2sQueryStep` run
followed by the deterministic abort/repackage postlude. -/
private lemma d2sQueryImpl_run_shape
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec)
      (StateT M (OptionT (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (m : M) :
    (((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (m := StateT M (OptionT (OracleComp
          (D2SChallengePlusUnitOracle (U := U) challengeSpec))))
        (gImpl := gImpl) (auxImpl := auxImpl) q).run st).run m).run
      = ((simulateQ (gImpl + auxImpl)
          (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)).run m).run
        >>= fun o =>
          match o with
          | none => pure none
          | some pom =>
              match pom.1 with
              | none => pure none
              | some pr => pure (some (pr, pom.2)) := by
  show (((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := StateT M (OptionT (OracleComp
        (D2SChallengePlusUnitOracle (U := U) challengeSpec))))
      (gImpl := gImpl) (auxImpl := auxImpl) q) st).run m).run = _
  unfold d2sQueryImpl
  rw [StateT.run_bind, OptionT.run_bind]
  unfold Option.elimM
  refine bind_congr fun o => ?_
  match o with
  | none => rfl
  | some pom =>
      match hpom : pom.1 with
      | none =>
          simp only [Option.elim]
          obtain ⟨po, m'⟩ := pom
          simp only at hpom
          subst hpom
          simp [OptionT.run_failure]
      | some pr =>
          simp only [Option.elim]
          obtain ⟨po, m'⟩ := pom
          simp only at hpom
          subst hpom
          rfl

/-- The auxiliary `(Unit →ₒ U) + unifSpec` realization baked into `d2fOuterImpl` (in-module
copy of the private `SimulatorBudgets.d2fAuxImpl`, definitionally equal to the inline
lambda of `ProverTransform.d2fOuterImpl`). -/
private def auxLift :
    QueryImpl ((Unit →ₒ U) + unifSpec)
      (StateT M (OptionT (OracleComp
        (D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
  fun aux =>
    MonadLift.monadLift
      (MonadLift.monadLift
        (query
          (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
          (Sum.inr aux) :
            OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) _) :
        OptionT (OracleComp
          (D2SChallengePlusUnitOracle (U := U) challengeSpec)) _)

/-- Run shape of the auxiliary lift. -/
private lemma auxLift_run_shape
    (a : ((Unit →ₒ U) + unifSpec).Domain) (m : M) :
    (((auxLift (U := U) (challengeSpec := challengeSpec) (M := M) a).run m).run)
      = (liftM ((D2SChallengePlusUnitOracle (U := U) challengeSpec).query (Sum.inr a)) :
          OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) _)
        >>= fun u => pure (some (u, m)) := by
  unfold auxLift
  simp [OptionT.run_lift, map_eq_bind_pure_comp, MonadLift.monadLift, Function.comp]

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Run-shape of `d2fOuterImpl` on a shared `oSpec` query: one forwarded query (in-module
twin of the private `SimulatorBudgets.d2fOuterImpl_run_inl`; holds definitionally). -/
private lemma outer_run_inl
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (qo : ι)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (m : M) :
    (((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P) gImpl
        (Sum.inl qo)).run st).run m).run
      = (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec).query
            (Sum.inl qo)) :
          OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) _)
          >>= fun u => pure (some ((u, st), m)) := rfl

/-- Run-shape of `d2fOuterImpl` on a duplex-sponge query: the `d2sQueryImpl` run re-indexed
along the right injection (in-module twin of the private
`SimulatorBudgets.d2fOuterImpl_run_inr`; holds definitionally). -/
private lemma outer_run_inr
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (dsq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (m : M) :
    (((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P) gImpl
        (Sum.inr dsq)).run st).run m).run
      = simulateQ (incl (oSpec := oSpec) challengeSpec)
          ((((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
              (m := StateT M (OptionT (OracleComp
                (D2SChallengePlusUnitOracle (U := U) challengeSpec))))
              (gImpl := gImpl)
              (auxImpl := auxLift)
              dsq).run st).run m).run) := rfl

end DispatcherShapes

/-! ## Run shapes of the raw Eq. 16 bridge, query-preserving forms -/

section BridgeRawShapes

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- Parse failure: the raw bridge is `pure none` (no queries, no log). -/
private lemma bridge_raw_run_none
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = none) :
    (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run
      = pure none := by
  unfold d2sCodecBridgeImpl
  simp [hparse]

/-- Parse success: the raw bridge is one FS-challenge query at the replayed key followed by
the `ψ⁻¹` preimage sampler (queries kept, no table substituted). -/
private lemma bridge_raw_run_some
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs) :
    (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run
      = (liftM ((D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec)).query
            (Sum.inl (replayKey (Salt := Salt) gq msgs))) :
          OracleComp (D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec)) _)
        >>= fun ch =>
          uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch
          >>= fun v => pure (some v) := by
  unfold d2sCodecBridgeImpl
  simp only [hparse]
  simp only [OptionT.run_bind, OptionT.run_lift, pure_bind, Option.elimM, Option.elim,
    bind_assoc]
  rfl

/-- The `ψ⁻¹` preimage sampler is oblivious to the salt-erasing spec re-keying: simulating
it through `saltEraseChallengePlusUnitImpl` is the unsalted sampler on the nose. -/
private lemma simulateQ_saltErase_udp {i : pSpec.ChallengeIdx} (ch : pSpec.Challenge i) :
    simulateQ
        (saltEraseChallengePlusUnitImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (Salt := Salt))
        (uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch)
      = uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle StmtIn pSpec) ch := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- Memo-miss/parse-success shape of the **salted** memoized bridge under the
right-injection inclusion: one outer-spec FS-challenge query at the replayed (salted) key,
the (inclusion-simulated) `ψ⁻¹` sampler, and the deterministic memo insert. -/
private lemma incl_bridgeMemo_miss_some_shape
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (m : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) m gq.1 gq.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 = none) :
    simulateQ (incl (oSpec := oSpec) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run m).run)
      = (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec)).query
            (Sum.inr (Sum.inl (replayKey (Salt := Salt) gq msgs)))) :
          OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec)) _)
        >>= fun ch =>
          simulateQ (incl (oSpec := oSpec) (fsChallengeOracle (StmtIn × Salt) pSpec))
            (uniformDeserializePreimage (pSpec := pSpec) (U := U)
              (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch)
          >>= fun v =>
            pure (some (v, insertD2SAlgoMemo m (bridgeMemoEntry (Salt := Salt) gq v))) := by
  rw [d2sCodecBridgeImplMemo_run_miss gq m hl, bridge_raw_run_some gq msgs hparse]
  rfl

/-- Memo-miss/parse-success shape of the **eager** (salt-erasing) bridge under the
right-injection inclusion: one outer-spec FS-challenge query at the **erased** key, the
(inclusion-simulated) unsalted `ψ⁻¹` sampler, and the *same* memo insert. -/
private lemma incl_bridgeEager_miss_some_shape
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (m : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) m gq.1 gq.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 = none) :
    simulateQ (incl (oSpec := oSpec) (fsChallengeOracle StmtIn pSpec))
        (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run m).run)
      = (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle StmtIn pSpec)).query
            (Sum.inr (Sum.inl ⟨gq.1, (gq.2.1, msgs)⟩))) :
          OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle StmtIn pSpec)) _)
        >>= fun ch =>
          simulateQ (incl (oSpec := oSpec) (fsChallengeOracle StmtIn pSpec))
            (uniformDeserializePreimage (pSpec := pSpec) (U := U)
              (challengeSpec := fsChallengeOracle StmtIn pSpec) ch)
          >>= fun v =>
            pure (some (v, insertD2SAlgoMemo m (bridgeMemoEntry (Salt := Salt) gq v))) := by
  rw [d2sCodecBridgeImplMemoEager_run_eq gq m, d2sCodecBridgeImplMemo_run_miss gq m hl,
    bridge_raw_run_some gq msgs hparse]
  rfl

end BridgeRawShapes

/-! ## The fixed-table coupling at `δ = 0`

Everything below this point works at `δ = 0` with a fixed salted table `c`, its
`delta0Salt`-section restriction in the eager world, and a fixed shared-oracle
implementation `oImpl`. -/

section Coupling

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
variable {Salt : Type} [SaltCodec U 0 Salt] [SampleableType U]
variable (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
variable (oImpl : QueryImpl oSpec ProbComp)

/-- The `unifSpec` coin realization of `hybGameEagerBody`. -/
private def probCoins : QueryImpl unifSpec ProbComp :=
  fun m => (liftM (unifSpec.query m) : ProbComp _)

/-- The salted-world fixed-table implementation (the `Hyb3SaltedMemo` body's `impl`). -/
private def implS :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) ProbComp :=
  oImpl + (tableQueryImpl c + (d2sUnitSampleImpl (U := U) + probCoins))

/-- The eager-world fixed-table implementation (the `Hyb₃` body's `impl` at the
section-restricted table). -/
private def implE :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle StmtIn pSpec)) ProbComp :=
  oImpl + (tableQueryImpl
    (saltSectionRestrict (delta0Salt (U := U) Salt) c) + (d2sUnitSampleImpl (U := U) + probCoins))

/-- **The coupling relation**: the eager-world logged run equals the salted-world logged
run with the salt erased entrywise on the log channel. -/
private def EC {β : Type}
    (YS : OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) β)
    (YE : OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle StmtIn pSpec)) β) : Prop :=
  leg (implE c oImpl) YE
    = (fun p => (p.1, eraseSaltRawLog (oSpec := oSpec) p.2)) <$> leg (implS c oImpl) YS

/-! ### Closure bricks for `EC` -/

private lemma ec_pure {β : Type} (x : β) :
    EC (U := U) c oImpl (pure x) (pure x) := by
  unfold EC
  rw [leg_pure, leg_pure]
  simp

private lemma ec_bind {β γ : Type}
    {AS : OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) β}
    {AE : OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle StmtIn pSpec)) β}
    (hA : EC c oImpl AS AE)
    {BS : β → OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) γ}
    {BE : β → OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle StmtIn pSpec)) γ}
    (hB : ∀ b, EC c oImpl (BS b) (BE b)) :
    EC c oImpl (AS >>= BS) (AE >>= BE) := by
  unfold EC at hA hB ⊢
  rw [leg_bind, leg_bind, hA, bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  rw [hB p.1, Functor.map_map, Functor.map_map]
  refine congrFun (congrArg _ ?_) _
  funext q
  show (q.1, eraseSaltRawLog (oSpec := oSpec) p.2 ++ eraseSaltRawLog (oSpec := oSpec) q.2)
    = (q.1, eraseSaltRawLog (oSpec := oSpec) (p.2 ++ q.2))
  rw [eraseSaltRawLog_append]

/-- Shared-`oSpec` query coupling: both worlds forward to `oImpl`, the entry is preserved
verbatim by the erasure. -/
private lemma ec_query_inl {β : Type} (qo : oSpec.Domain)
    {kS : oSpec.Range qo → OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) β}
    {kE : oSpec.Range qo → OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle StmtIn pSpec)) β}
    (hk : ∀ u, EC c oImpl (kS u) (kE u)) :
    EC c oImpl
      (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)).query (Sum.inl qo)) >>= kS)
      (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)).query (Sum.inl qo)) >>= kE) := by
  unfold EC at hk ⊢
  rw [leg_query_bind, leg_query_bind]
  show (oImpl qo >>= fun u => _) = _ <$> (oImpl qo >>= fun u => _)
  rw [map_bind]
  refine bind_congr fun u => ?_
  rw [hk u, Functor.map_map, Functor.map_map]
  refine congrFun (congrArg _ ?_) _
  funext p
  rfl

/-- Auxiliary sampling query coupling: both worlds use the same
`d2sUnitSampleImpl + probCoins` realization, the entry is preserved by the erasure. -/
private lemma ec_query_aux {β : Type} (a : ((Unit →ₒ U) + unifSpec).Domain)
    {kS : ((Unit →ₒ U) + unifSpec).Range a →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)) β}
    {kE : ((Unit →ₒ U) + unifSpec).Range a →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)) β}
    (hk : ∀ u, EC c oImpl (kS u) (kE u)) :
    EC c oImpl
      (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)).query (Sum.inr (Sum.inr a))) >>= kS)
      (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)).query (Sum.inr (Sum.inr a))) >>= kE) := by
  unfold EC at hk ⊢
  rw [leg_query_bind, leg_query_bind]
  show ((d2sUnitSampleImpl (U := U) + probCoins) a >>= fun u => _)
    = _ <$> ((d2sUnitSampleImpl (U := U) + probCoins) a >>= fun u => _)
  rw [map_bind]
  refine bind_congr fun u => ?_
  rw [hk u, Functor.map_map, Functor.map_map]
  refine congrFun (congrArg _ ?_) _
  funext p
  cases a <;> rfl

/-- **The `δ = 0` content**: a canonical-salt FS-challenge query couples — the
section-restricted table read in the eager world is *literally* the salted table read at
the canonical salt, and the erased entry matches the eager entry. -/
private lemma ec_query_challenge {β : Type} (i : pSpec.ChallengeIdx) (x : StmtIn)
    (msgs : pSpec.MessagesUpTo i.1.castSucc)
    {kS : pSpec.Challenge i → OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) β}
    {kE : pSpec.Challenge i → OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle StmtIn pSpec)) β}
    (hk : ∀ u, EC c oImpl (kS u) (kE u)) :
    EC c oImpl
      (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)).query
          (Sum.inr (Sum.inl ⟨i, ((x, delta0Salt (U := U) Salt), msgs)⟩))) >>= kS)
      (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)).query
          (Sum.inr (Sum.inl ⟨i, (x, msgs)⟩))) >>= kE) := by
  unfold EC at hk ⊢
  rw [leg_query_bind, leg_query_bind]
  show ((pure (c ⟨i, ((x, delta0Salt (U := U) Salt), msgs)⟩) : ProbComp _) >>= fun u => _)
    = _ <$> ((pure (c ⟨i, ((x, delta0Salt (U := U) Salt), msgs)⟩) : ProbComp _)
        >>= fun u => _)
  rw [pure_bind, pure_bind]
  rw [hk (c ⟨i, ((x, delta0Salt (U := U) Salt), msgs)⟩), Functor.map_map, Functor.map_map]
  refine congrFun (congrArg _ ?_) _
  funext p
  rfl

/-! ### The per-`gᵢ`-query bridge coupling -/

/-- The `ψ⁻¹` sampler couples (one shared auxiliary index draw, identical preimage list). -/
private lemma ec_udp {i : pSpec.ChallengeIdx} (ch : pSpec.Challenge i)
    {β : Type}
    {kS : Vector U (challengeSize (pSpec := pSpec) i) →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)) β}
    {kE : Vector U (challengeSize (pSpec := pSpec) i) →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)) β}
    (hk : ∀ v, EC c oImpl (kS v) (kE v)) :
    EC c oImpl
      (simulateQ (incl (oSpec := oSpec) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch) >>= kS)
      (simulateQ (incl (oSpec := oSpec) (fsChallengeOracle StmtIn pSpec))
        (uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle StmtIn pSpec) ch) >>= kE) := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  exact ec_query_aux c oImpl _ fun u => hk _

/-- **Per-query bridge coupling at `δ = 0`**: at every `gSpec` key and shared memo, the
salted memoized Eq. 16 bridge (salted world) and the eager salt-erasing bridge (eager
world) couple — equal results and memo evolution, salt-erased logs. -/
private lemma bridge_coupled
    (gq : (gSpec (U := U) StmtIn pSpec 0).Domain)
    (m : D2SAlgoMemo StmtIn U 0 Salt pSpec)
    {β : Type}
    {kS : Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
        × D2SAlgoMemo StmtIn U 0 Salt pSpec) →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)) β}
    {kE : Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
        × D2SAlgoMemo StmtIn U 0 Salt pSpec) →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle StmtIn pSpec)) β}
    (hk : ∀ o, EC c oImpl (kS o) (kE o)) :
    EC c oImpl
      (simulateQ (incl (oSpec := oSpec) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt) gq).run m).run) >>= kS)
      (simulateQ (incl (oSpec := oSpec) (fsChallengeOracle StmtIn pSpec))
        (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt) gq).run m).run) >>= kE) := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := 0) (Salt := Salt)
      (pSpec := pSpec) m gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := 0) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r =>
      rw [d2sCodecBridgeImplMemo_run_hit gq m r hl,
        d2sCodecBridgeImplMemoEager_run_hit gq m r hl]
      exact hk (some (r, m))
  | none =>
      cases hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 with
      | none =>
          rw [d2sCodecBridgeImplMemoEager_run_eq gq m,
            d2sCodecBridgeImplMemo_run_miss gq m hl, bridge_raw_run_none gq hparse]
          exact hk none
      | some msgs =>
          rw [incl_bridgeMemo_miss_some_shape gq m msgs hparse hl,
            incl_bridgeEager_miss_some_shape gq m msgs hparse hl]
          -- canonicalize the salted key (δ = 0): `bin τ̂ = delta0Salt`
          unfold replayKey
          rw [encode_delta0 (U := U) (Salt := Salt) gq.2.2.1]
          -- reassociate (definitional) to expose the challenge-query head
          show EC (U := U) c oImpl
            ((liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec)).query
                (Sum.inr (Sum.inl ⟨gq.1, ((gq.2.1, delta0Salt (U := U) Salt), msgs)⟩))) :
              OracleComp _ _) >>= fun ch =>
              simulateQ (incl (oSpec := oSpec) (fsChallengeOracle (StmtIn × Salt) pSpec))
                (uniformDeserializePreimage (pSpec := pSpec) (U := U)
                  (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch)
              >>= fun v =>
                kS (some (v, insertD2SAlgoMemo m (bridgeMemoEntry (Salt := Salt) gq v))))
            ((liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle StmtIn pSpec)).query
                (Sum.inr (Sum.inl ⟨gq.1, (gq.2.1, msgs)⟩))) :
              OracleComp _ _) >>= fun ch =>
              simulateQ (incl (oSpec := oSpec) (fsChallengeOracle StmtIn pSpec))
                (uniformDeserializePreimage (pSpec := pSpec) (U := U)
                  (challengeSpec := fsChallengeOracle StmtIn pSpec) ch)
              >>= fun v =>
                kE (some (v, insertD2SAlgoMemo m (bridgeMemoEntry (Salt := Salt) gq v))))
          refine ec_query_challenge (U := U) c oImpl gq.1 gq.2.1 msgs fun ch => ?_
          refine ec_udp (U := U) c oImpl ch fun v => ?_
          exact hk _

/-! ### The two structural inductions -/

/-- Inner coupling: the §5.4 dispatcher computation (any `w` over
`gSpec + ((Unit →ₒ U) + unifSpec)`), simulated against the two bridge realizations and
re-injected into the outer spec, couples at every shared memo. -/
private lemma inner_coupled {β : Type}
    (w : OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
      (δ := 0)) β)
    (m : D2SAlgoMemo StmtIn U 0 Salt pSpec) :
    EC c oImpl
      (simulateQ (incl (oSpec := oSpec) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (((simulateQ
          ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
            (Salt := Salt))
            + auxLift (U := U) (M := D2SAlgoMemo StmtIn U 0 Salt pSpec)
              (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) w).run m).run))
      (simulateQ (incl (oSpec := oSpec) (fsChallengeOracle StmtIn pSpec))
        (((simulateQ
          ((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := 0) (Salt := Salt))
            + auxLift (U := U) (M := D2SAlgoMemo StmtIn U 0 Salt pSpec)
              (challengeSpec := fsChallengeOracle StmtIn pSpec)) w).run m).run)) := by
  induction w using OracleComp.inductionOn generalizing m with
  | pure x =>
      rw [run1_simulateQ_pure, run1_simulateQ_pure]
      exact ec_pure c oImpl _
  | query_bind t k ih =>
      rw [run1_simulateQ_query_bind, run1_simulateQ_query_bind]
      rw [simulateQ_bind, simulateQ_bind]
      match t with
      | Sum.inl gq =>
          refine bridge_coupled c oImpl gq m fun o => ?_
          match o with
          | none => exact ec_pure c oImpl none
          | some um => exact ih um.1 um.2
      | Sum.inr a =>
          -- expose the auxiliary query head (definitional re-typing)
          show EC (U := U) c oImpl
            ((liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec)).query
                (Sum.inr (Sum.inr a))) : OracleComp _ _) >>= fun u =>
              simulateQ (incl (oSpec := oSpec) (fsChallengeOracle (StmtIn × Salt) pSpec))
                (((simulateQ
                  ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
                    (δ := 0) (Salt := Salt))
                    + auxLift (U := U) (M := D2SAlgoMemo StmtIn U 0 Salt pSpec)
                      (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
                  (k u)).run m).run))
            ((liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle StmtIn pSpec)).query
                (Sum.inr (Sum.inr a))) : OracleComp _ _) >>= fun u =>
              simulateQ (incl (oSpec := oSpec) (fsChallengeOracle StmtIn pSpec))
                (((simulateQ
                  ((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
                    (δ := 0) (Salt := Salt))
                    + auxLift (U := U) (M := D2SAlgoMemo StmtIn U 0 Salt pSpec)
                      (challengeSpec := fsChallengeOracle StmtIn pSpec))
                  (k u)).run m).run))
          refine ec_query_aux (U := U) c oImpl a fun u => ?_
          exact ih u m

/-- **The pipeline coupling** (the master bisimulation): the full `d2fRaw` pipeline of any
adversary computation, run against the two bridge worlds from any shared simulator state
and memo, couples — equal results (including the threaded `tr_i` memo), salt-erased logs. -/
private lemma pipe_coupled {α : Type}
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (st : D2SQueryState (δ := 0) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (m : D2SAlgoMemo StmtIn U 0 Salt pSpec) :
    EC c oImpl
      ((((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
        (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt))) comp).run st).run m).run)
      ((((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
        (d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt))) comp).run st).run m).run) := by
  induction comp using OracleComp.inductionOn generalizing st m with
  | pure x =>
      rw [run2_simulateQ_pure, run2_simulateQ_pure]
      exact ec_pure c oImpl _
  | query_bind t k ih =>
      rw [run2_simulateQ_query_bind, run2_simulateQ_query_bind]
      match t with
      | Sum.inl qo =>
          rw [outer_run_inl _ qo st m, outer_run_inl _ qo st m]
          -- expose the shared query head (definitional re-typing)
          show EC (U := U) c oImpl
            ((liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec)).query (Sum.inl qo)) :
              OracleComp _ _) >>= fun u =>
              (((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
                (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
                  (δ := 0) (Salt := Salt))) (k u)).run st).run m).run)
            ((liftM ((oSpec + D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle StmtIn pSpec)).query (Sum.inl qo)) :
              OracleComp _ _) >>= fun u =>
              (((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
                (d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
                  (δ := 0) (Salt := Salt))) (k u)).run st).run m).run)
          refine ec_query_inl (U := U) c oImpl qo fun u => ?_
          exact ih u st m
      | Sum.inr dsq =>
          rw [outer_run_inr _ dsq st m, outer_run_inr _ dsq st m,
            d2sQueryImpl_run_shape, d2sQueryImpl_run_shape]
          rw [simulateQ_bind, simulateQ_bind]
          refine ec_bind (U := U) c oImpl
            (ec_bind (U := U) c oImpl (inner_coupled c oImpl _ m) fun x => ?_)
            fun o => ?_
          · match x with
            | none => exact ec_pure c oImpl none
            | some pom =>
                match pom with
                | (none, m') => exact ec_pure c oImpl none
                | (some pr, m') => exact ec_pure c oImpl _
          · match o with
            | none => exact ec_pure c oImpl none
            | some uss => exact ih uss.1.1 uss.1.2 uss.2

end Coupling

/-! ## The residual, proven -/

section MainTheorem

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
variable {Salt : Type} [SaltCodec U 0 Salt] [SampleableType U]

/-- **The `δ = 0` fixed-table salt-erasure lift is TRUE** (the named round-3 obligation
`Hyb23Delta0.Hyb23SaltErasureLiftDelta0Residual`): at every fixed salted table `c`, the
`Hyb3SaltedMemo` body (salted memoized bridge + line-4 salt erasure) and the `Hyb₃` body at
the `delta0Salt`-section restriction (eager bridge + identity line 4) are **equal**
`ProbComp` computations — hence equidistributed. -/
theorem hyb23SaltErasureLiftDelta0
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    (oImpl : QueryImpl oSpec ProbComp) :
    Hyb23SaltErasureLiftDelta0Residual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl := by
  intro V P c
  refine congrArg evalDist ?_
  show leg (implS c oImpl)
      ((((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
        (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt))) P).run default).run default).run)
      >>= _
    = leg (implE c oImpl)
      ((((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
        (d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt))) P).run default).run default).run)
      >>= _
  have hP := pipe_coupled (T_H := T_H) (T_P := T_P) c oImpl P default default
  unfold EC at hP
  rw [hP, bind_map_left]
  refine bind_congr fun p => ?_
  obtain ⟨pRes?, pLogRaw⟩ := p
  match pRes? with
  | none => rfl
  | some ⟨⟨⟨stmtIn, messages⟩, _⟩, memo⟩ =>
      show leg (implS c oImpl)
          ((((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
            (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
              (Salt := Salt)))
            ((V.duplexSpongeFiatShamir.run
              stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)).run
                default).run memo).run)
          >>= _
        = leg (implE c oImpl)
          ((((simulateQ (d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
            (d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
              (δ := 0) (Salt := Salt)))
            ((V.duplexSpongeFiatShamir.run
              stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)).run
                default).run memo).run)
          >>= _
      have hV := pipe_coupled (T_H := T_H) (T_P := T_P) c oImpl
        ((V.duplexSpongeFiatShamir.run
          stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run) default memo
      unfold EC at hV
      rw [hV, bind_map_left]
      refine bind_congr fun v => ?_
      obtain ⟨vRes?, vLogRaw⟩ := v
      match vRes? with
      | none => rfl
      | some ⟨⟨stmtOut?, _⟩, _⟩ =>
          match stmtOut? with
          | none => rfl
          | some stmtOut =>
              show (simulateQ (d2sUnitSampleImpl (U := U))
                    ((saltErasingLineFour (Salt := Salt)
                      (projectChallengePlusUnitQueryLog (U := U) pLogRaw)).run)
                    >>= fun pLog'? =>
                  simulateQ (d2sUnitSampleImpl (U := U))
                    ((saltErasingLineFour (Salt := Salt)
                      (projectChallengePlusUnitQueryLog (U := U) vLogRaw)).run)
                    >>= fun vLog'? =>
                  match pLog'?, vLog'? with
                  | some pLog', some vLog' =>
                      pure (some (stmtIn, stmtOut, messages, pLog', vLog'))
                  | _, _ => pure none)
                = (simulateQ (d2sUnitSampleImpl (U := U))
                    ((pure (projectChallengePlusUnitQueryLog (U := U)
                      (eraseSaltRawLog (oSpec := oSpec) pLogRaw)) :
                        UnitSampleM U _).run)
                    >>= fun pLog'? =>
                  simulateQ (d2sUnitSampleImpl (U := U))
                    ((pure (projectChallengePlusUnitQueryLog (U := U)
                      (eraseSaltRawLog (oSpec := oSpec) vLogRaw)) :
                        UnitSampleM U _).run)
                    >>= fun vLog'? =>
                  match pLog'?, vLog'? with
                  | some pLog', some vLog' =>
                      pure (some (stmtIn, stmtOut, messages, pLog', vLog'))
                  | _, _ => pure none)
              rw [project_eraseSaltRawLog, project_eraseSaltRawLog]
              rfl

/-- **CO25 Claim 5.23, step C, holds at `δ = 0`** — `Hyb23SaltErasureResidual` proven
unconditionally: `Δ(Hyb3SaltedMemo, Hyb₃) = 0`. The round-2 falsity flag (the salt-grinding
distinguisher) is confined to `δ > 0`. -/
theorem hyb23SaltErasure_delta0
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) :
    Hyb23SaltErasureResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl :=
  hyb23SaltErasure_delta0_of_lift T_H T_P Salt oImpl
    (hyb23SaltErasureLiftDelta0 T_H T_P Salt oImpl)

/-- The Claim 5.23 step at `δ = 0` from steps A and B alone (exact form): the fixed-table
lift hypothesis of `Hyb23Delta0.hyb23Step_delta0_of_lift` is discharged. -/
theorem hyb23Step_delta0_of_AB
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hA : Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hB : Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl :=
  hyb23Step_delta0_of_lift T_H T_P Salt oImpl hA hB
    (hyb23SaltErasureLiftDelta0 T_H T_P Salt oImpl)

/-- The honest ε-budget Claim 5.23 step at `δ = 0` from steps A and B alone: the
fixed-table lift hypothesis of `Hyb23Delta0.hyb23StepEps_delta0_of_lift` is discharged. -/
theorem hyb23StepEps_delta0_of_AB
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) {ε : ℝ}
    (hA : Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hB : Hyb23MemoTransparencyEpsResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε) :
    Hyb23StepEpsResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε :=
  hyb23StepEps_delta0_of_lift T_H T_P Salt oImpl hA hB
    (hyb23SaltErasureLiftDelta0 T_H T_P Salt oImpl)

/-- **The round-4 `δ = 0` frontier, exact form**: the round-3 keystone
`KeyLemmaFrontierRound3.keyLemmaEagerDelta0_of_finestResiduals` with the fixed-table lift
**discharged** — *twelve* finest open residuals imply the full eager key lemma at `δ = 0`.
The Claim 5.23 lane is down to {decoded-query lift (step A), memo transparency (step B)};
salt erasure (step C) is fully proven. Honest flags carried from round 3: `hRepeat` is
doubtful for non-injective decoders, and `h23B`'s exact-`0` form is doubtful at every `δ`
(use the ε-budget form below). -/
theorem keyLemmaEagerDelta0_of_finestResiduals'
    [DecidableEq ι]
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
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
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
    (h23A : Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h23B : Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  KeyLemmaFrontierRound3.keyLemmaEagerDelta0_of_finestResiduals T_H T_P Salt oImpl
    h01C εsw εev h01sw h01ev h01sum hLazy hRepeat hAlignE hAlignMid hProv hVerif
    h23A h23B (hyb23SaltErasureLiftDelta0 T_H T_P Salt oImpl) h34A h34B

/-- **The round-4 `δ = 0` frontier, ε-budget form (the honest headline)**: the round-3
keystone `KeyLemmaFrontierRound3.keyLemmaEagerDelta0_of_finestResidualsEps23` with the
fixed-table lift **discharged** — memo transparency consumed with any
`ε ≤ 7/(2|Σ|^c)` absorbed by the proven F1b slack at the **unchanged** `ηStarPaper`
bound. -/
theorem keyLemmaEagerDelta0_of_finestResidualsEps23'
    [DecidableEq ι]
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
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
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
    (h23A : Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h23B : Hyb23MemoTransparencyEpsResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε)
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  KeyLemmaFrontierRound3.keyLemmaEagerDelta0_of_finestResidualsEps23 T_H T_P Salt oImpl
    hε h01C εsw εev h01sw h01ev h01sum hLazy hRepeat hAlignE hAlignMid hProv hVerif
    h23A h23B (hyb23SaltErasureLiftDelta0 T_H T_P Salt oImpl) h34A h34B

end MainTheorem

#print axioms DuplexSpongeFS.Hyb23Delta0Lift.project_eraseSaltRawLog
#print axioms DuplexSpongeFS.Hyb23Delta0Lift.hyb23SaltErasureLiftDelta0
#print axioms DuplexSpongeFS.Hyb23Delta0Lift.hyb23SaltErasure_delta0
#print axioms DuplexSpongeFS.Hyb23Delta0Lift.hyb23Step_delta0_of_AB
#print axioms DuplexSpongeFS.Hyb23Delta0Lift.hyb23StepEps_delta0_of_AB
#print axioms DuplexSpongeFS.Hyb23Delta0Lift.keyLemmaEagerDelta0_of_finestResiduals'
#print axioms DuplexSpongeFS.Hyb23Delta0Lift.keyLemmaEagerDelta0_of_finestResidualsEps23'

end DuplexSpongeFS.Hyb23Delta0Lift

end
