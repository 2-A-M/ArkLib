/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Step

/-!
# CO25 Claim 5.23 at `δ = 0` — salt erasure is sound, memo transparency gets an ε-budget

Round 2 flagged two legs of the `Hyb₂ → Hyb₃` salted split (`Hyb23Step`) as doubtful or
false:

- `Hyb23SaltErasureResidual` (step C) — **genuinely false for `δ > 0`** (salt-grinding
  distinguisher: two absorb paths differing only in the salt read independent salted table
  cells but the same erased cell);
- `Hyb23MemoTransparencyResidual` (step B) — exact-`0` doubtful (repeat-key raw `ρ̂ᵢ`
  re-exposure through fresh squeeze states is a positive-probability birthday event).

This module is the **`δ = 0` specialization** of that frontier. The driving observation:
at `δ = 0` the on-sponge salt type `Vector U 0` is a *subsingleton*, so `bin = SaltCodec.encode`
is constant on it — every salted FS key the Eq. 16 bridge can ever read has the **one** salt
value `delta0Salt`. The salted→unsalted key map is therefore a *bijection between the
reachable salted keys (the `delta0Salt` section) and the unsalted keys*, and the
salt-grinding distinguisher vanishes: there are no two distinct salts to grind.

## Proven here (no `sorry`, axiom-clean)

Salt erasure at `δ = 0`, fully factored:

- `simulateQ_uniformDeserializePreimage_fsTableAux_congr` /
  `..._fsTableAux_cross` — the `ψ⁻¹` preimage sampler is oblivious to the FS-table summand
  (same-spec and cross-spec forms).
- `fsTableAux_bridge_run_shape` / `fsTableAux_bridge_run_none` — run shape of the raw Eq. 16
  bridge against a fixed salted table (extracted from `VerifierReplay`'s inline proof).
- `saltErase_bridge_run_shape` / `saltErase_bridge_run_none` — run shape of the **salt-erased**
  raw bridge against a fixed *unsalted* table (any `δ`): the single table read happens at the
  erased key.
- `simulateQ_fsTableAux_bridge_congr` / `simulateQ_fsTableAux_bridgeMemo_congr` (any `δ`) —
  the raw/memoized bridge run depends on the salted table **only through its value at the
  replayed key** `(i, (𝕩, bin τ̂), φ⁻¹(α̂))`.
- **`simulateQ_bridgeMemoEager_restrict_eq_bridgeMemo_delta0`** — the per-query content of
  step C at `δ = 0`: against a salted table `c` and its `delta0Salt`-section restriction
  `saltSectionRestrict delta0Salt c`, the `Hyb₃` eager (salt-erasing) memoized bridge and the
  salted memoized bridge are **equal** computations at *every* key and *every* memo —
  unconditionally (no parse hypothesis: on parse failure both abort identically). This
  refutes the round-2 falsity flag *for `δ = 0`* at the per-query level.
- **`probOutput_uniformSalted_bind_restrict`** — the distributional content of "the key map
  is a bijection on reachable keys": restricting a uniform salted table to the
  `s₀`-section *is* a uniform unsalted table (pushforward equality, proven by a
  swap-involution fiber argument; consumes only the `SampleableType` axioms plus
  `[Fintype]` of the unsalted table space).
- `hybGameEagerBody` + `hybGameEager_uniform_eq` — the Figure-4 body at a fixed table
  realization; the eager game is literally `uniform table >>= body`.
- **`hyb23SaltErasure_delta0_of_lift`** — the reduction theorem: the named fixed-table
  residual `Hyb23SaltErasureLiftDelta0Residual` (pointwise game equality at every *fixed*
  pair of section-coupled tables) implies the full `Hyb23SaltErasureResidual` at `δ = 0`.
  The uniform-table re-indexing — the part that is *false* for `δ > 0` — is **discharged**.
- `hyb23Step_delta0_of_lift` — headline: at `δ = 0` the `Hyb23StepResidual` follows from
  {decoded-query lift (step A), memo transparency (step B), fixed-table lift} via
  `hyb23Step_of_saltedSplit`.

Memo transparency at `δ = 0`, ε-budget routing:

- `Hyb23MemoTransparencyEpsResidual` / `Hyb23StepEpsResidual` — ε-budget forms of step B and
  of the whole Claim 5.23 step.
- `hyb23StepEps_of_saltedSplit` (any `δ`) and `hyb23StepEps_delta0_of_lift` — the ε-budget
  split skeletons (proven triangle assemblies).
- **`claimSum_add_le_ηStarPaper`** — the numeric finding, formalized: the CO25 §5.8 claim
  assignment gives the `Hyb₂ → Hyb₃` step a budget of exactly `0`, but the F1b numeric
  assembly `claimSum_le_ηStarPaper` has slack **exactly `(14·t + 7)/(2|Σ|^c)`**
  (`t = tₕ + tₚ + tₚᵢ`); any memo-transparency cost `ε` up to that slack is absorbable with
  **no change** to `ηStarPaper` or to the Claim 5.21/5.22/5.24 budgets.
- **`keyLemmaEager_of_steps_eps23`** — the ε-aware ladder assembly: with
  `ε ≤ 7/(2|Σ|^c)` (the budget-uniform part of the slack) the eager key lemma still closes
  at the *unchanged* `ηStarPaper` bound.

## Honest analysis: does the memo-transparency doubt persist at `δ = 0`?

**Yes.** The round-2 obstruction to step B's exact-`0` form is the `ψ⁻¹` *resampling
asymmetry*: on a repeated `gᵢ` key the memoless bridge draws a fresh uniform preimage of the
same challenge while the memoized bridge replays the stored one; the raw encoded `ρ̂ᵢ` can be
re-exposed to the prover through fresh squeeze states after a backward-edge/capacity
collision. The salt plays **no role** in this event — it is a collision among permutation
states — so setting `δ = 0` does not remove it. The honest `δ = 0` frontier is therefore:
step C *exactly* `0` (this module), step B with an ε-budget.

**Structural finding (named, as requested by the claim-assignment audit).** The Hyb₂→Hyb₃
step has **no** ε-budget in CO25's claim assignment (Claim 5.23 `= 0`). Two routings exist
for a genuine step-B cost:
1. *Slack absorption* (formalized here): up to `(14t + 7)/(2|Σ|^c)` fits inside the existing
   F1b slack — `keyLemmaEager_of_steps_eps23` closes the ladder at the unchanged paper
   bound. **Caveat**: this capacity is *linear* in `t`, while the re-exposure event is
   birthday-*quadratic* (`≈ T²/|Σ|^c`); slack absorption alone covers it only for
   small query budgets.
2. *Budget re-routing into Claims 5.21/5.24*: the re-exposure event is a sub-event of the
   §5.6 trace bad-event family `E` whose mass those claims already pay for. Re-routing means
   proving the Claim 5.21/5.24 steps for hybrid pairs that **also** differ in memoization
   (i.e. moving the memo switch into the `Hyb₀→Hyb₁` or `Hyb₃→Hyb₄` coupling), not adding a
   new ε — an upstream re-statement of the ladder, recorded here as the honest alternative.

## Open at `δ = 0` (named obligations, NOT proven)

- `Hyb23SaltErasureLiftDelta0Residual` — the fixed-table game-level lift: push the proven
  per-query equality (`simulateQ_bridgeMemoEager_restrict_eq_bridgeMemo_delta0`) and the
  per-entry log relation (`Hyb23Step.eraseSaltLog`) through `d2fRaw`/`loggingOracle` —
  a `simulateQ` bisimulation with *no remaining probabilistic content* (both sides are
  deterministic given the table; the coupling is the identity).
- `Hyb23DecodedQueryResidual` at `δ = 0` (step A) — unchanged from round 2; its game-level
  lift additionally needs a reachability invariant (parse-failed `eSpec` keys are read by
  `Hyb₂` but unreachable through the simulator's Item 4(e) image check), which the step-C
  lift does *not* need (salt erasure is total).
- `Hyb23MemoTransparencyResidual`/`...EpsResidual` at `δ = 0` (step B) — see analysis above.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb23Delta0

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
  VerifierReplay Hyb23Step
open scoped ENNReal NNReal

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it
-- (repo precedent: the sibling lane modules `Hyb23Step`, `VerifierReplay`).
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

/-! ## The `δ = 0` subsingleton salt -/

section Delta0Salt

omit [SpongeUnit U] in
/-- `Vector U 0` is a subsingleton: the empty vector is unique. The engine of every `δ = 0`
specialization in this module. -/
lemma vector_zero_eq (v w : Vector U 0) : v = w := by
  ext i h
  exact absurd h (Nat.not_lt_zero i)

variable (Salt : Type) [SaltCodec U 0 Salt]

/-- The single reachable FS-standard salt at `δ = 0`: `bin` of the unique empty on-sponge
salt (CO25 line 1188 at `δ★ = 0`). -/
noncomputable def delta0Salt : Salt :=
  SaltCodec.encode (U := U) (δ := 0) (Salt := Salt) (Vector.replicate 0 (0 : U))

variable {Salt}

/-- At `δ = 0` the salt encoding is constant: every encoded salt is `delta0Salt`. -/
lemma encode_delta0 (v : Vector U 0) :
    SaltCodec.encode (U := U) (δ := 0) (Salt := Salt) v = delta0Salt (U := U) Salt :=
  congrArg _ (vector_zero_eq v _)

end Delta0Salt

/-! ## Fixed-table implementations and `ψ⁻¹` obliviousness bricks -/

section TableImpls

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- Instantiate the **unsalted** FS-challenge summand of the `Hyb₃` bridge surface with a
fixed eager table `f`, leaving the auxiliary `(Unit →ₒ U) + unifSpec` sampling oracles free
(unsalted twin of `VerifierReplay.fsTableAuxImpl`). -/
def fsUnsaltedTableAuxImpl (f : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    QueryImpl
      (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle StmtIn pSpec))
      (OracleComp ((Unit →ₒ U) + unifSpec)) :=
  fun q =>
    match q with
    | .inl qf => pure (f qf)
    | .inr aux => query (spec := (Unit →ₒ U) + unifSpec) aux

/-- The `ψᵢ⁻¹` uniform-preimage sampler is oblivious to the salted FS-table summand: against
any two fixed salted tables it is the *same* `(Unit →ₒ U) + unifSpec` computation. -/
lemma simulateQ_uniformDeserializePreimage_fsTableAux_congr
    (c₁ c₂ : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    {i : pSpec.ChallengeIdx} (ch : pSpec.Challenge i) :
    simulateQ (fsTableAuxImpl (U := U) c₁)
        (uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch)
      = simulateQ (fsTableAuxImpl (U := U) c₂)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch) := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- Cross-spec form: the `ψᵢ⁻¹` sampler simulated against a fixed **unsalted** table and
against a fixed **salted** table is the same auxiliary computation (twin of
`Hyb23Step.simulateQ_uniformDeserializePreimage_tableAux_eq`). -/
lemma simulateQ_uniformDeserializePreimage_fsTableAux_cross
    (f : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    {i : pSpec.ChallengeIdx} (ch : pSpec.Challenge i) :
    simulateQ (fsUnsaltedTableAuxImpl (U := U) f)
        (uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle StmtIn pSpec) ch)
      = simulateQ (fsTableAuxImpl (U := U) c)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch) := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

end TableImpls

/-! ## Run shapes of the raw Eq. 16 bridge against fixed tables (any `δ`) -/

section BridgeShapes

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- Parse-failure shape, salted table: the raw bridge aborts before any table read. -/
lemma fsTableAux_bridge_run_none
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = none) :
    simulateQ (fsTableAuxImpl (U := U) c)
        ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run)
      = pure none := by
  unfold d2sCodecBridgeImpl
  simp [hparse]

/-- Run shape, salted table (extracted from the inline `hshape` of
`VerifierReplay.deserialize_of_mem_support_bridge_table`): on a parse success the raw bridge
is one table read at the replayed key followed by the table-oblivious `ψ⁻¹` sample. -/
lemma fsTableAux_bridge_run_shape
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs) :
    simulateQ (fsTableAuxImpl (U := U) c)
        ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run)
      = (simulateQ (fsTableAuxImpl (U := U) c)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
            (c (replayKey (Salt := Salt) gq msgs)))) >>= fun v => pure (some v) := by
  unfold d2sCodecBridgeImpl
  simp only [hparse]
  simp only [OptionT.run_bind, OptionT.run_lift, pure_bind, Option.elimM, Option.elim,
    simulateQ_bind, simulateQ_map, bind_pure_comp]
  rfl

/-- Parse-failure shape, salt-erased view: the salt-erased raw bridge aborts identically. -/
lemma saltErase_bridge_run_none
    (f : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = none) :
    simulateQ (fsUnsaltedTableAuxImpl (U := U) f)
        (simulateQ
          (saltEraseChallengePlusUnitImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (Salt := Salt))
          ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (Salt := Salt) gq).run))
      = pure none := by
  unfold d2sCodecBridgeImpl
  simp [hparse]

/-- Run shape of the **salt-erased** raw bridge against a fixed *unsalted* table (any `δ`):
the single table read happens at the **erased** key `(i, 𝕩, φ⁻¹(α̂))` — the salt is gone
before the table is consulted. -/
lemma saltErase_bridge_run_shape
    (f : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs) :
    simulateQ (fsUnsaltedTableAuxImpl (U := U) f)
        (simulateQ
          (saltEraseChallengePlusUnitImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (Salt := Salt))
          ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (Salt := Salt) gq).run))
      = (simulateQ (fsUnsaltedTableAuxImpl (U := U) f)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle StmtIn pSpec)
            (f ⟨gq.1, (gq.2.1, msgs)⟩))) >>= fun v => pure (some v) := by
  unfold d2sCodecBridgeImpl
  simp only [hparse]
  unfold uniformDeserializePreimage sampleFromList
  simp only [OptionT.run_bind, OptionT.run_lift, pure_bind, Option.elimM, Option.elim,
    simulateQ_bind, simulateQ_map, bind_pure_comp]
  rfl

/-- **Single-read dependence** (any `δ`): the raw Eq. 16 bridge run depends on the salted
table only through its value at the replayed key. -/
theorem simulateQ_fsTableAux_bridge_congr
    (c₁ c₂ : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (h : ∀ msgs : pSpec.MessagesUpTo gq.1.1.castSucc,
      hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs →
      c₁ (replayKey (Salt := Salt) gq msgs) = c₂ (replayKey (Salt := Salt) gq msgs)) :
    simulateQ (fsTableAuxImpl (U := U) c₁)
        ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run)
      = simulateQ (fsTableAuxImpl (U := U) c₂)
          ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (Salt := Salt) gq).run) := by
  cases hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 with
  | none =>
      rw [fsTableAux_bridge_run_none c₁ gq hparse, fsTableAux_bridge_run_none c₂ gq hparse]
  | some msgs =>
      rw [fsTableAux_bridge_run_shape c₁ gq msgs hparse,
        fsTableAux_bridge_run_shape c₂ gq msgs hparse, h msgs hparse,
        simulateQ_uniformDeserializePreimage_fsTableAux_congr c₁ c₂]

/-- **Single-read dependence, memoized** (any `δ`): the memoized Eq. 16 bridge run depends on
the salted table only through its value at the replayed key (hit: no read at all; miss: the
single raw-bridge read). -/
theorem simulateQ_fsTableAux_bridgeMemo_congr
    (c₁ c₂ : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : ∀ msgs : pSpec.MessagesUpTo gq.1.1.castSucc,
      hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs →
      c₁ (replayKey (Salt := Salt) gq msgs) = c₂ (replayKey (Salt := Salt) gq msgs)) :
    simulateQ (fsTableAuxImpl (U := U) c₁)
        (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run memo).run)
      = simulateQ (fsTableAuxImpl (U := U) c₂)
          (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (Salt := Salt) gq).run memo).run) := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r =>
      rw [d2sCodecBridgeImplMemo_run_hit gq memo r hl]
      rfl
  | none =>
      rw [d2sCodecBridgeImplMemo_run_miss gq memo hl]
      simp only [simulateQ_bind]
      rw [simulateQ_fsTableAux_bridge_congr c₁ c₂ gq h]
      refine bind_congr fun o => ?_
      match o with
      | none => rfl
      | some resp => rfl

end BridgeShapes

/-! ## The `δ = 0` section restriction and the per-query salt-erasure coupling -/

section Delta0Coupling

variable {Salt : Type} [SaltCodec U 0 Salt]

/-- Restrict a salted table to the section at a fixed salt `s₀`: the pullback along the
key embedding `(i, (𝕩, α)) ↦ (i, ((𝕩, s₀), α))`. At `δ = 0` with `s₀ = delta0Salt` this
section contains **every reachable key** of the salted bridges. -/
def saltSectionRestrict (s₀ : Salt)
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OracleFamily (fsChallengeOracle StmtIn pSpec) :=
  fun k => c ⟨k.1, ((k.2.1, s₀), k.2.2)⟩

/-- **Per-query salt erasure at `δ = 0`, raw bridge**: against a salted table `c` and its
`delta0Salt`-section restriction, the salt-erased raw bridge and the salted raw bridge are
equal computations — at *every* `gSpec` key (parse failures abort identically on both
sides). -/
theorem simulateQ_restrict_saltErase_bridge_run_delta0
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec 0).Domain) :
    simulateQ
        (fsUnsaltedTableAuxImpl (U := U)
          (saltSectionRestrict (delta0Salt (U := U) Salt) c))
        (simulateQ
          (saltEraseChallengePlusUnitImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (Salt := Salt))
          ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
            (Salt := Salt) gq).run))
      = simulateQ (fsTableAuxImpl (U := U) c)
          ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
            (Salt := Salt) gq).run) := by
  cases hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 with
  | none =>
      rw [saltErase_bridge_run_none _ gq hparse, fsTableAux_bridge_run_none c gq hparse]
  | some msgs =>
      rw [saltErase_bridge_run_shape _ gq msgs hparse,
        fsTableAux_bridge_run_shape c gq msgs hparse]
      have hval : saltSectionRestrict (delta0Salt (U := U) Salt) c
          ⟨gq.1, (gq.2.1, msgs)⟩ = c (replayKey (Salt := Salt) gq msgs) := by
        change c ⟨gq.1, ((gq.2.1, delta0Salt (U := U) Salt), msgs)⟩
          = c ⟨gq.1, ((gq.2.1, SaltCodec.encode (U := U) (δ := 0) (Salt := Salt) gq.2.2.1),
              msgs)⟩
        rw [encode_delta0]
      rw [hval, simulateQ_uniformDeserializePreimage_fsTableAux_cross
        (saltSectionRestrict (delta0Salt (U := U) Salt) c) c]

/-- **The per-query content of step C at `δ = 0`** (headline brick): against a salted table
`c` and its `delta0Salt`-section restriction, the `Hyb₃` eager (salt-erasing) memoized
bridge and the `Hyb3SaltedMemo` salted memoized bridge are **equal** computations at every
`gSpec` key and every shared `tr_i` memo. With `Vector U 0` a subsingleton, the
salted→unsalted key map is a bijection on the reachable keys, so the salt-grinding
distinguisher of the round-2 falsity flag does not exist at `δ = 0`. -/
theorem simulateQ_bridgeMemoEager_restrict_eq_bridgeMemo_delta0
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec 0).Domain)
    (memo : D2SAlgoMemo StmtIn U 0 Salt pSpec) :
    simulateQ
        (fsUnsaltedTableAuxImpl (U := U)
          (saltSectionRestrict (delta0Salt (U := U) Salt) c))
        (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt) gq).run memo).run)
      = simulateQ (fsTableAuxImpl (U := U) c)
          (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
            (Salt := Salt) gq).run memo).run) := by
  rw [d2sCodecBridgeImplMemoEager_run_eq gq memo]
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := 0) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := 0) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r =>
      rw [d2sCodecBridgeImplMemo_run_hit gq memo r hl]
      rfl
  | none =>
      rw [d2sCodecBridgeImplMemo_run_miss gq memo hl]
      simp only [simulateQ_bind]
      rw [simulateQ_restrict_saltErase_bridge_run_delta0 c gq]
      refine bind_congr fun o => ?_
      match o with
      | none => rfl
      | some resp => rfl

end Delta0Coupling

/-! ## Uniform-table re-indexing: the section restriction of a uniform salted table is a
uniform unsalted table (the "bijection on reachable keys" content, distribution level) -/

section UniformReindex

variable {Salt : Type}

open Classical in
/-- Fiber-swap involution: swap the values `f₁ k ↔ f₂ k` of a salted table at every key of
the `s₀`-section, leave the off-section cells untouched. Carries the fiber of `f₁` under
`saltSectionRestrict s₀` onto the fiber of `f₂`. -/
private noncomputable def saltSectionSwapFun (s₀ : Salt)
    (f₁ f₂ : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec) :=
  fun k =>
    letI : Decidable ((k.2.1.2 : Salt) = s₀) := Classical.propDecidable _
    if (k.2.1.2 : Salt) = s₀ then
      (Equiv.swap (α := pSpec.Challenge k.1)
        (f₁ ⟨k.1, (k.2.1.1, k.2.2)⟩) (f₂ ⟨k.1, (k.2.1.1, k.2.2)⟩)) (c k)
    else c k

private lemma saltSectionSwapFun_involutive (s₀ : Salt)
    (f₁ f₂ : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    Function.Involutive
      (saltSectionSwapFun (Salt := Salt) s₀ f₁ f₂) := by
  intro c
  funext k
  unfold saltSectionSwapFun
  by_cases h : (k.2.1.2 : Salt) = s₀
  · rw [if_pos h, if_pos h, Equiv.swap_apply_self]
  · rw [if_neg h, if_neg h]

/-- The fiber-swap as a permutation of salted tables. -/
private noncomputable def saltSectionSwap (s₀ : Salt)
    (f₁ f₂ : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    Equiv.Perm (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  Function.Involutive.toPerm _ (saltSectionSwapFun_involutive s₀ f₁ f₂)

private lemma saltSectionRestrict_swapFun (s₀ : Salt)
    (f₁ f₂ : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (k : (fsChallengeOracle StmtIn pSpec).Domain) :
    saltSectionRestrict s₀ (saltSectionSwapFun s₀ f₁ f₂ c) k
      = Equiv.swap (α := pSpec.Challenge k.1) (f₁ k) (f₂ k)
          (saltSectionRestrict s₀ c k) := by
  unfold saltSectionRestrict saltSectionSwapFun
  rw [if_pos rfl]
  rfl

private lemma saltSectionRestrict_swapFun_eq_iff (s₀ : Salt)
    (f₁ f₂ : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    saltSectionRestrict s₀ (saltSectionSwapFun s₀ f₁ f₂ c) = f₂
      ↔ saltSectionRestrict s₀ c = f₁ := by
  constructor
  · intro h
    funext k
    have hk := congrFun h k
    rw [saltSectionRestrict_swapFun] at hk
    have h2 := congrArg (Equiv.swap (α := pSpec.Challenge k.1) (f₁ k) (f₂ k)) hk
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
    exact h2
  · intro h
    funext k
    rw [saltSectionRestrict_swapFun, congrFun h k, Equiv.swap_apply_left]

variable [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
  [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]

/-- The pushforward of the uniform salted table along the section restriction is constant
(fiber-swap argument; mirrors `OracleReduction.probOutput_uniform_marginal_eq`). -/
private lemma probOutput_map_saltSectionRestrict_eq (s₀ : Salt)
    (f₁ f₂ : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    Pr[= f₁ | (saltSectionRestrict s₀) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
      = Pr[= f₂ | (saltSectionRestrict s₀) <$>
          ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] := by
  classical
  rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
  rw [← Equiv.tsum_eq (saltSectionSwap (Salt := Salt) s₀ f₁ f₂)
    (fun c => Pr[= c | $ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)]
      * Pr[= f₂ | (pure (saltSectionRestrict s₀ c) :
          ProbComp (OracleFamily (fsChallengeOracle StmtIn pSpec)))])]
  refine tsum_congr fun c => ?_
  have hsample : Pr[= saltSectionSwap (Salt := Salt) s₀ f₁ f₂ c |
        $ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)]
      = Pr[= c | $ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)] :=
    probOutput_uniformSample_inj _ _ _
  have hpure : Pr[= f₂ | (pure (saltSectionRestrict s₀
        (saltSectionSwap (Salt := Salt) s₀ f₁ f₂ c)) :
        ProbComp (OracleFamily (fsChallengeOracle StmtIn pSpec)))]
      = Pr[= f₁ | (pure (saltSectionRestrict s₀ c) :
          ProbComp (OracleFamily (fsChallengeOracle StmtIn pSpec)))] := by
    rw [probOutput_pure, probOutput_pure]
    by_cases h : saltSectionRestrict s₀ c = f₁
    · have h2 : saltSectionRestrict s₀
          (saltSectionSwap (Salt := Salt) s₀ f₁ f₂ c) = f₂ :=
        (saltSectionRestrict_swapFun_eq_iff s₀ f₁ f₂ c).mpr h
      rw [if_pos h2.symm, if_pos h.symm]
    · have h2 : ¬ saltSectionRestrict s₀
          (saltSectionSwap (Salt := Salt) s₀ f₁ f₂ c) = f₂ := fun hh =>
        h ((saltSectionRestrict_swapFun_eq_iff s₀ f₁ f₂ c).mp hh)
      rw [if_neg (fun hh => h2 hh.symm), if_neg (fun hh => h hh.symm)]
  rw [hsample, hpure]

/-- The pushforward of the uniform salted table along the section restriction is exactly
uniform over unsalted tables. -/
private lemma probOutput_map_saltSectionRestrict
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))] (s₀ : Salt)
    (f : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    Pr[= f | (saltSectionRestrict s₀) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
      = (Fintype.card (OracleFamily (fsChallengeOracle StmtIn pSpec)) : ℝ≥0∞)⁻¹ := by
  classical
  have hfail : Pr[⊥ | (saltSectionRestrict s₀) <$>
      ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] = 0 := by
    rw [probFailure_map]
    exact HasEvalPMF.probFailure_eq_zero _
  have hsum : ∑ f' : OracleFamily (fsChallengeOracle StmtIn pSpec),
      Pr[= f' | (saltSectionRestrict s₀) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] = 1 :=
    sum_probOutput_eq_one hfail
  have hconst : ∑ _f' : OracleFamily (fsChallengeOracle StmtIn pSpec),
      Pr[= f | (saltSectionRestrict s₀) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] = 1 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun f' _ =>
      probOutput_map_saltSectionRestrict_eq s₀ f f'
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] at hconst
  exact ENNReal.eq_inv_of_mul_eq_one_left hconst

/-- **Uniform re-indexing along the `s₀` section** (the distributional content of "the
salted→unsalted key map is a bijection on reachable keys"): binding any continuation through
the section restriction of a uniform salted table is the same as binding it on a uniform
unsalted table. -/
theorem probOutput_uniformSalted_bind_restrict {γ : Type}
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))] (s₀ : Salt)
    (g : OracleFamily (fsChallengeOracle StmtIn pSpec) → ProbComp γ) (z : γ) :
    Pr[= z | ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun c =>
        g (saltSectionRestrict s₀ c)]
      = Pr[= z | ($ᵗ OracleFamily (fsChallengeOracle StmtIn pSpec)) >>= g] := by
  classical
  have hassoc : (($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun c =>
        g (saltSectionRestrict s₀ c))
      = ((saltSectionRestrict s₀) <$>
          ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))) >>= g := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp only [Function.comp_apply, pure_bind]
  rw [hassoc, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun f => ?_
  rw [probOutput_map_saltSectionRestrict s₀ f, probOutput_uniformSample]

end UniformReindex

/-! ## The eager game body at a fixed table and the fixed-table lift residual -/

section GameBody

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- CO25 §5.8, Figure 4 lines 2–4 at a **fixed** challenge-oracle realization `cImpl`
(the body of `KeyLemmaHybrids.hybGameEager` after line 1's sample). -/
noncomputable def hybGameEagerBody [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M] (δ : ℕ)
    (cImpl : QueryImpl challengeSpec ProbComp)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) := do
  let coins : QueryImpl unifSpec ProbComp := fun m => (liftM (unifSpec.query m) : ProbComp _)
  let impl : QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) ProbComp :=
    oImpl + (cImpl + (d2sUnitSampleImpl (U := U) + coins))
  let ⟨pRes?, pLogRaw⟩ ←
    simulateQ impl
      ((simulateQ loggingOracle
        ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl P default).run)).run)
  match pRes? with
  | none => pure none
  | some ⟨⟨⟨stmtIn, messages⟩, _⟩, memo⟩ => do
      let ⟨vRes?, vLogRaw⟩ ←
        simulateQ impl
          ((simulateQ loggingOracle
            ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl
              ((V.duplexSpongeFiatShamir.run
                stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)
              memo).run)).run)
      match vRes? with
      | none => pure none
      | some ⟨⟨stmtOut?, _⟩, _⟩ =>
          match stmtOut? with
          | none => pure none
          | some stmtOut => do
              let pLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) pLogRaw)).run)
              let vLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) vLogRaw)).run)
              match pLog'?, vLog'? with
              | some pLog', some vLog' =>
                  pure (some ⟨stmtIn, stmtOut, messages, pLog', vLog'⟩)
              | _, _ => pure none

/-- The eager hybrid game over a uniform table distribution is literally
`uniform table >>= body`. -/
lemma hybGameEager_uniform_eq [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M]
    [SampleableType (OracleFamily challengeSpec)] (δ : ℕ)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    hybGameEager (T_H := T_H) (T_P := T_P) δ
        (OracleDistribution.uniform challengeSpec) gImpl lineFour oImpl V P
      = ($ᵗ OracleFamily challengeSpec) >>= fun c =>
          hybGameEagerBody (T_H := T_H) (T_P := T_P) δ
            (tableQueryImpl c) gImpl lineFour oImpl V P := rfl

end GameBody

section LiftResidual

variable {Salt : Type}

/-- **The fixed-table lift residual at `δ = 0`** (named obligation, NOT proven): at every
*fixed* salted table `c`, the `Hyb3SaltedMemo` body (salted memoized bridge + line-4 salt
erasure) and the `Hyb₃` body at the section-restricted table (eager salt-erasing bridge +
identity line 4) have the same output distribution.

This is the residual plumbing of step C at `δ = 0` — the per-query coupling
(`simulateQ_bridgeMemoEager_restrict_eq_bridgeMemo_delta0`, proven, unconditional) lifted
through `d2fRaw`/`loggingOracle` with `Hyb23Step.eraseSaltLog` relating the raw logs. All
the probabilistic content of the step (the uniform-table re-indexing) is **already
discharged** by `hyb23SaltErasure_delta0_of_lift`; what remains is a deterministic-coupling
`simulateQ` bisimulation. -/
def Hyb23SaltErasureLiftDelta0Residual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)),
    𝒟[hybGameEagerBody (T_H := T_H) (T_P := T_P) 0
        (tableQueryImpl c)
        (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
          (Salt := Salt))
        (saltErasingLineFour (Salt := Salt)) oImpl V P]
      = 𝒟[hybGameEagerBody (T_H := T_H) (T_P := T_P) 0
          (tableQueryImpl (saltSectionRestrict (delta0Salt (U := U) Salt) c))
          (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := 0) (Salt := Salt))
          (fun log => pure log) oImpl V P]

/-- **Salt erasure holds at `δ = 0`, modulo the fixed-table lift** (the reduction theorem):
the named deterministic-coupling residual implies the full `Hyb23SaltErasureResidual` at
`δ = 0`. The uniform-table re-indexing — exactly the content that makes the residual *false*
for `δ > 0` — is discharged by `probOutput_uniformSalted_bind_restrict`. -/
theorem hyb23SaltErasure_delta0_of_lift [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hlift : Hyb23SaltErasureLiftDelta0Residual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl) :
    Hyb23SaltErasureResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl := by
  intro V P
  have h1 : Hyb3SaltedMemo (pSpec := pSpec) T_H T_P 0 Salt oImpl V P
      = 𝒟[hybGameEager (T_H := T_H) (T_P := T_P) 0
          (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
          (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := 0)
            (Salt := Salt))
          (saltErasingLineFour (Salt := Salt)) oImpl V P] := rfl
  have h2 : Hyb3 (pSpec := pSpec) T_H T_P 0 Salt oImpl V P
      = 𝒟[hybGameEager (T_H := T_H) (T_P := T_P) 0
          (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
          (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := 0) (Salt := Salt))
          (fun log => pure log) oImpl V P] := rfl
  have hgames : Hyb3SaltedMemo (pSpec := pSpec) T_H T_P 0 Salt oImpl V P
      = Hyb3 (pSpec := pSpec) T_H T_P 0 Salt oImpl V P := by
    rw [h1, h2, hybGameEager_uniform_eq, hybGameEager_uniform_eq]
    refine evalDist_ext fun z => ?_
    rw [← probOutput_uniformSalted_bind_restrict (delta0Salt (U := U) Salt)
      (fun f => hybGameEagerBody (T_H := T_H) (T_P := T_P) 0 (tableQueryImpl f)
        (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := 0) (Salt := Salt))
        (fun log => pure log) oImpl V P) z]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun c => ?_
    rw [evalDist_ext_iff.mp (hlift V P c) z]
  rw [hgames, SPMF.tvDist_self]

/-- **Headline, exact form**: at `δ = 0` the full `Hyb23StepResidual` (CO25 Claim 5.23,
`Δ(Hyb₂, Hyb₃) = 0`) follows from the decoded-query lift (step A), memo transparency
(step B), and the fixed-table lift — the salt-erasure leg's distributional content is
proven. -/
theorem hyb23Step_delta0_of_lift [SampleableType U]
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
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (hlift : Hyb23SaltErasureLiftDelta0Residual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl) :
    Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl :=
  hyb23Step_of_saltedSplit T_H T_P 0 Salt oImpl hA hB
    (hyb23SaltErasure_delta0_of_lift T_H T_P Salt oImpl hlift)

end LiftResidual

/-! ## Memo transparency: ε-budget forms and split skeletons (any `δ`) -/

section EpsResiduals

/-- ε-budget form of step B (`tr_i` memo transparency): the memoized and memoless salted
bridges induce game distributions at most `ε` apart. The exact-`0` form
(`Hyb23Step.Hyb23MemoTransparencyResidual`) remains doubtful **also at `δ = 0`**: the
repeat-key raw-`ρ̂ᵢ` re-exposure event is a permutation-state collision and does not involve
the salt. -/
def Hyb23MemoTransparencyEpsResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) (ε : ℝ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb3SaltedFresh T_H T_P δ Salt oImpl V P)
      (Hyb3SaltedMemo T_H T_P δ Salt oImpl V P) ≤ ε

/-- ε-budget form of the whole Claim 5.23 step: `Δ(Hyb₂, Hyb₃) ≤ ε`. CO25's claim
assignment gives this step the budget `0`; `claimSum_add_le_ηStarPaper` quantifies exactly
how much ε is absorbable without touching any claim bound. -/
def Hyb23StepEpsResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) (ε : ℝ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb2 T_H T_P δ oImpl V P) (Hyb3 T_H T_P δ Salt oImpl V P) ≤ ε

/-- ε-budget salted split skeleton (any `δ`): steps A and C exact, step B with budget `ε`,
assemble into the ε-budget Claim 5.23 step. -/
theorem hyb23StepEps_of_saltedSplit [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) {ε : ℝ}
    (hA : Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hB : Hyb23MemoTransparencyEpsResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl ε)
    (hC : Hyb23SaltErasureResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb23StepEpsResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl ε := by
  intro V P
  have h1 := hA V P
  have h2 := hB V P
  have h3 := hC V P
  have t1 := SPMF.tvDist_triangle (Hyb2 T_H T_P δ oImpl V P)
    (Hyb3SaltedFresh T_H T_P δ Salt oImpl V P) (Hyb3 T_H T_P δ Salt oImpl V P)
  have t2 := SPMF.tvDist_triangle (Hyb3SaltedFresh T_H T_P δ Salt oImpl V P)
    (Hyb3SaltedMemo T_H T_P δ Salt oImpl V P) (Hyb3 T_H T_P δ Salt oImpl V P)
  linarith

/-- **The honest `δ = 0` frontier of Claim 5.23**: decoded-query lift (step A, exact) +
memo transparency with ε-budget (step B) + the fixed-table lift (step C's remaining
deterministic coupling) give `Δ(Hyb₂, Hyb₃) ≤ ε` at `δ = 0`. -/
theorem hyb23StepEps_delta0_of_lift [SampleableType U]
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
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε)
    (hlift : Hyb23SaltErasureLiftDelta0Residual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl) :
    Hyb23StepEpsResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε :=
  hyb23StepEps_of_saltedSplit T_H T_P 0 Salt oImpl hA hB
    (hyb23SaltErasure_delta0_of_lift T_H T_P Salt oImpl hlift)

end EpsResiduals

/-! ## The ε-absorption numerics: the F1b slack is exactly `(14t + 7)/(2|Σ|^c)` -/

section EpsNumerics

/-- **ε-absorption capacity of the §5.8 numeric assembly** (the structural finding,
formalized): the three nonzero claim bounds plus any `ε` up to the *exact* F1b slack
`(14·(tₕ+tₚ+tₚᵢ) + 7)/(2|Σ|^c)` still sum to at most `ηStarPaper`. A memo-transparency
cost within this capacity needs **no** change to `ηStarPaper` or to any claim bound. -/
lemma claimSum_add_le_ηStarPaper (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) {ε : ℝ}
    (hε : ε ≤ (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7)
      / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)) :
    claim5_21Bound U tₕ tₚ tₚᵢ L + claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec
        + claim5_24Bound U tₕ tₚ tₚᵢ L + ε
      ≤ ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L εcodec := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
  have hP : (0 : ℝ) < (Fintype.card U : ℝ) ^ SpongeSize.C := pow_pos hc0 _
  have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C := by linarith
  have frac_le : ∀ x y z w : ℝ, x + y - 2 * z ≤ w →
      x / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
        + (y / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
          - z / ((Fintype.card U : ℝ) ^ SpongeSize.C))
      ≤ w / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
    intro x y z w hxyz
    have hcomb : x / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
        + (y / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
          - z / ((Fintype.card U : ℝ) ^ SpongeSize.C))
        = (x + y - 2 * z) / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
      field_simp
      ring
    rw [hcomb, div_le_div_iff₀ h2P h2P]
    exact mul_le_mul_of_nonneg_right hxyz (le_of_lt h2P)
  have main : 7 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ) ^ 2
        - 3 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ)
        + (7 * (L : ℝ) * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + (L : ℝ) + 2 * (tₚᵢ : ℝ)))
        - 2 * (5 * ((L : ℝ) + 1))
      ≤ (7 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) ^ 2
          + (28 * (L : ℝ) + 25) * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ)
          + (14 * (L : ℝ) + 1) * ((L : ℝ) + 1))
        - (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) tₕ, Nat.cast_nonneg (α := ℝ) tₚ,
      Nat.cast_nonneg (α := ℝ) tₚᵢ, Nat.cast_nonneg (α := ℝ) L]
  have step := frac_le
    (7 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ) ^ 2 - 3 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ))
    (7 * (L : ℝ) * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + (L : ℝ) + 2 * (tₚᵢ : ℝ)))
    (5 * ((L : ℝ) + 1))
    ((7 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) ^ 2
        + (28 * (L : ℝ) + 25) * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ)
        + (14 * (L : ℝ) + 1) * ((L : ℝ) + 1))
      - (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7))
    main
  have hsplitW : ((7 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) ^ 2
        + (28 * (L : ℝ) + 25) * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ)
        + (14 * (L : ℝ) + 1) * ((L : ℝ) + 1))
      - (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7))
        / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
      = (7 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) ^ 2
          + (28 * (L : ℝ) + 25) * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ)
          + (14 * (L : ℝ) + 1) * ((L : ℝ) + 1))
          / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
        - (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7)
          / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := sub_div _ _ _
  unfold claim5_21Bound claim5_22Bound claim5_24Bound ηStarPaper
  linarith [step, hε, hsplitW]

/-- The ε-aware ladder assembly (mirror of `KeyLemmaHybrids.keyLemmaEager_of_steps`): with
a memo-transparency budget `ε ≤ 7/(2|Σ|^c)` (the budget-uniform part of the F1b slack), the
four step residuals — Claim 5.23 in ε-budget form — and the witness budgets still give the
full eager key lemma at the **unchanged** `ηStarPaper` bound. -/
theorem keyLemmaEager_of_steps_eps23
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp) {ε : ℝ}
    (hε : ε ≤ 7 / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C))
    (h01 : Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h12 : Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h23 : Hyb23StepEpsResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl ε)
    (h34 : Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hM1c : SimulatedProverChallengeBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P)
    (hM1d : SimulatedProverSharedBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P tₒ tₕ tₚ tₚᵢ L hL hShared hHash hPerm hPermInv
  refine ⟨eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P,
    ?_, ?_, ?_⟩
  · intro i
    exact eagerSimulatedProver_shared_budget (δ := δ) (Salt := Salt) T_H T_P hM1d P tₒ
      hShared i
  · exact eagerSimulatedProver_challenge_budget (δ := δ) (Salt := Salt) T_H T_P hM1c P
      tₕ tₚ tₚᵢ hPerm
  · have hU : Nonempty U := ⟨0⟩
    have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
    have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
    have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C :=
      mul_pos two_pos (pow_pos hc0 _)
    have hε' : ε ≤ (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7)
        / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
      refine le_trans hε ?_
      rw [div_le_div_iff₀ h2P h2P]
      nlinarith [Nat.cast_nonneg (α := ℝ) (tₕ + tₚ + tₚᵢ)]
    have hchain := tvDist_chain4
      (Hyb0 T_H T_P δ oImpl V P) (Hyb1 T_H T_P δ oImpl V P) (Hyb2 T_H T_P δ oImpl V P)
      (Hyb3 T_H T_P δ Salt oImpl V P)
      (Hyb4 oImpl V
        (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
      (h01 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
      (h12 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
      (h23 V P)
      (h34 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
    rw [← hyb4_eq_basicFiatShamirEagerRand oImpl V
        (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P),
      ← hyb0_eq_duplexSpongeRemappedEager T_H T_P δ oImpl V P,
      SPMF.tvDist_comm]
    have hsum := claimSum_add_le_ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L
      codec.decodingBias hε'
    linarith

end EpsNumerics

#print axioms DuplexSpongeFS.Hyb23Delta0.vector_zero_eq
#print axioms DuplexSpongeFS.Hyb23Delta0.encode_delta0
#print axioms DuplexSpongeFS.Hyb23Delta0.simulateQ_uniformDeserializePreimage_fsTableAux_congr
#print axioms DuplexSpongeFS.Hyb23Delta0.simulateQ_uniformDeserializePreimage_fsTableAux_cross
#print axioms DuplexSpongeFS.Hyb23Delta0.fsTableAux_bridge_run_none
#print axioms DuplexSpongeFS.Hyb23Delta0.fsTableAux_bridge_run_shape
#print axioms DuplexSpongeFS.Hyb23Delta0.saltErase_bridge_run_none
#print axioms DuplexSpongeFS.Hyb23Delta0.saltErase_bridge_run_shape
#print axioms DuplexSpongeFS.Hyb23Delta0.simulateQ_fsTableAux_bridge_congr
#print axioms DuplexSpongeFS.Hyb23Delta0.simulateQ_fsTableAux_bridgeMemo_congr
#print axioms DuplexSpongeFS.Hyb23Delta0.simulateQ_restrict_saltErase_bridge_run_delta0
#print axioms DuplexSpongeFS.Hyb23Delta0.simulateQ_bridgeMemoEager_restrict_eq_bridgeMemo_delta0
#print axioms DuplexSpongeFS.Hyb23Delta0.probOutput_uniformSalted_bind_restrict
#print axioms DuplexSpongeFS.Hyb23Delta0.hybGameEager_uniform_eq
#print axioms DuplexSpongeFS.Hyb23Delta0.hyb23SaltErasure_delta0_of_lift
#print axioms DuplexSpongeFS.Hyb23Delta0.hyb23Step_delta0_of_lift
#print axioms DuplexSpongeFS.Hyb23Delta0.hyb23StepEps_of_saltedSplit
#print axioms DuplexSpongeFS.Hyb23Delta0.hyb23StepEps_delta0_of_lift
#print axioms DuplexSpongeFS.Hyb23Delta0.claimSum_add_le_ηStarPaper
#print axioms DuplexSpongeFS.Hyb23Delta0.keyLemmaEager_of_steps_eps23

end DuplexSpongeFS.Hyb23Delta0

end
