/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaAssembly

/-!
# CO25 Claim 5.24 — the strict split instantiated: `Hyb₃ → Hyb₄` via `(εA, εB)`

This module attacks `KeyLemmaHybrids.Hyb34StepResidual` (CO25 Claim 5.24, Eq. 55) through
the proven Eq. 55 skeleton `VerifierReplay.hyb34Step_of_strictSplit`, by **fixing the
coupling pair** `(εA, εB)` and shipping the per-query determinism layer that the
`Hyb3Strict → Hyb₄` collapse consumes.

## The chosen split

The keystone `VerifierReplay.memoCoherentTable_keystone` shows the deterministic part of
the replay is **exact**, so the entire `claim5_24Bound` budget is available for the
bad-event mass. The two legs of the strict split bound the *same* CO25 §5.8 bad event
`E_𝒱` ("the `Hyb₃` verifier's `D2SQuery` run leaves the committed replay path": a fresh
verifier-side `gᵢ` key, a `φ⁻¹` parse failure, or a BackTrack/LookAhead asymmetry) in two
adjacent experiments — `Δ(Hyb₃, Hyb3Strict)` pays it where the real bridge answers fresh,
`Δ(Hyb3Strict, Hyb₄)` pays it where the strict game aborts but the basic-FS verifier reads
on. The canonical identical-until-bad accounting therefore charges the budget **once per
leg**, and the natural split is the symmetric one:

  `εA = εB = hyb34SplitBudget = claim5_24Bound / 2`.

`hyb34SplitBudget_add_self` (the two halves recombine exactly) and
`claim5_24Bound_nonneg` (the budget is nonnegative whenever the verifier makes at least
one permutation query, `1 ≤ L` — satisfiability of each half) are proven below.

## Proven here (no `sorry`, axiom-clean)

- `hyb34Step_of_divergence_collapse`: the two finer residuals
  `Hyb34DivergenceResidual` (εA leg) and `Hyb34CollapseResidual` (εB leg) **imply the full
  `Hyb34StepResidual`** — the reduction theorem demanded by the strict split, via
  `hyb34Step_of_strictSplit` and the exact recombination of the halves.
- `keyLemmaEager_of_steps_divergenceCollapse`: the campaign frontier re-based onto the
  finer residuals — Claims 5.21–5.23 plus the two legs imply the full eager key lemma
  (composes with `KeyLemmaAssembly.keyLemmaEager_of_hybSteps`).
- **The εB per-query determinism layer** (the `Hyb3Strict → Hyb₄` toolkit):
  - `saltLiftTable` / `fsTableAuxImplEager`: the unsalted eager FS table actually sampled
    by `Hyb₃`/`Hyb3Strict`/`Hyb₄` (CO25 Eq. 54), pulled back onto the salted Eq. 16 bridge
    surface, and the bridge-local view of the once-sampled table.
  - `fsTableAuxImplEager_comp_saltErase` / `simulateQ_fsTableAuxImplEager_eager_run`: the
    salt-erasing re-keying of the `Hyb₃` bridge composed with the unsalted table **is** the
    salted bridge against the pulled-back table — the transfer that re-keys every salted
    determinism brick of `VerifierReplay` onto the unsalted surface.
  - `memoCoherentTableEager_keystone`: the verifier-replay keystone on the **unsalted eager
    surface**: against the once-sampled table `c` of `Hyb3Strict`/`Hyb₄` and a coherent
    `tr_i` memo, every response the `Hyb₃`-prover bridge commits deserializes to `c` at the
    replayed unsalted basic-FS key, and coherence is preserved across the run.
  - `d2sCodecBridgeImplMemoEagerHitOnly_support_some_inv`: inversion for the strict
    verifier bridge — every successful answer is a `tr_i` memo hit and leaves the memo
    untouched (the strict verifier *cannot* commit new keys).
  - `d2sCodecBridgeImplMemoEagerHitOnly_coherent_serve`: the εB keystone — against a
    coherent memo, **every challenge the `Hyb3Strict` verifier ever serves equals the
    table value the `Hyb₄` basic-FS verifier reads at the replayed key**. On the hit path
    the two verifiers are pointwise equal; the per-query content of `εB` is closed, and
    what remains of the εB leg is threading this equality through the Figure-4 game
    skeleton.

## Open core (named `*Residual : Prop`, NOT proven)

- `Hyb34DivergenceResidual` (εA leg): `Δ(Hyb₃, Hyb3Strict) ≤ claim5_24Bound/2`. The two
  games differ **only** in the verifier-side `gᵢ` realization
  (`d2sCodecBridgeImplMemoEager` vs `d2sCodecBridgeImplMemoEagerHitOnly`), which agree on
  every `tr_i` memo hit (`d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit`); the gap is
  exactly the mass of runs where the verifier produces a fresh `gᵢ` key — CO25's `E_𝒱`,
  to be bounded by the §5.6 trace analysis (`BirthdayBound` accumulator + the honest bad
  events of `KeyLemmaFoundations` + the M2 reductions, channelled by
  `BirthdayBound.probEvent_honestBad_le_probEvent_E`).
- `Hyb34CollapseResidual` (εB leg): `Δ(Hyb3Strict, Hyb₄) ≤ claim5_24Bound/2`. On the hit
  path the collapse is **exact** (`..._coherent_serve` + `memoCoherentTableEager_keystone`
  + ψ-roundtrip); off the hit path the strict game aborts where `Hyb₄` reads fresh table
  values — the same `E_𝒱` mass, this time in the `Hyb₄`-side experiment. Open: the
  structured-verifier analysis (the honest DSFS verifier's absorb/squeeze pattern drives
  `D2SQuery` down the committed backtrack path) through the game skeleton.

Neither residual is axiomatized; `Hyb34StepResidual` stays the single consuming obligation
upstream, and `hyb34Step_of_divergence_collapse` is the only door these two need.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb34Step

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open VerifierReplay

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## The symmetric Eq. 55 budget split -/

section BudgetNumerics

/-- The per-leg budget of the symmetric Eq. 55 split: half of the CO25 Claim 5.24 bound.
Each leg of the strict split (`Δ(Hyb₃, Hyb3Strict)` and `Δ(Hyb3Strict, Hyb₄)`) pays the
`E_𝒱` bad-event mass once; the keystone makes the deterministic part free, so the two
halves exhaust the budget exactly. -/
noncomputable def hyb34SplitBudget (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  claim5_24Bound U tₕ tₚ tₚᵢ L / 2

/-- The two halves of the split recombine to exactly the Claim 5.24 budget (the `hsum`
hypothesis of `hyb34Step_of_strictSplit`, with no slack). -/
lemma hyb34SplitBudget_add_self (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ L : ℕ) :
    hyb34SplitBudget U tₕ tₚ tₚᵢ L + hyb34SplitBudget U tₕ tₚ tₚᵢ L
      = claim5_24Bound U tₕ tₚ tₚᵢ L :=
  add_halves _

/-- Satisfiability of the split: the Claim 5.24 budget is nonnegative as soon as the
verifier makes at least one permutation query (`1 ≤ L`; recall every consumer of the §5.8
residuals carries `pSpec.totalNumPermQueries ≤ L`). At `L = 0` the CO25 Eq. 55 bound is
negative — the paper's bound is only meaningful for protocols that squeeze at least one
challenge. -/
lemma claim5_24Bound_nonneg (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ L : ℕ) (hL : 1 ≤ L) :
    0 ≤ claim5_24Bound U tₕ tₚ tₚᵢ L := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hP : (0 : ℝ) < (Fintype.card U : ℝ) ^ SpongeSize.C := by positivity
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C := by positivity
  have hsplit : (5 * ((L : ℝ) + 1)) / ((Fintype.card U : ℝ) ^ SpongeSize.C)
      = (10 * ((L : ℝ) + 1)) / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
    rw [div_eq_div_iff hP.ne' h2P.ne']
    ring
  unfold claim5_24Bound
  rw [hsplit, div_sub_div_same]
  refine div_nonneg ?_ (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) tₕ, Nat.cast_nonneg (α := ℝ) tₚ,
    Nat.cast_nonneg (α := ℝ) tₚᵢ, mul_le_mul hL' hL' zero_le_one
      (le_trans zero_le_one hL')]

/-- Each half of the budget is itself nonnegative for `1 ≤ L` (so neither leg of the split
demands a negative TV distance). -/
lemma hyb34SplitBudget_nonneg (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ L : ℕ) (hL : 1 ≤ L) :
    0 ≤ hyb34SplitBudget U tₕ tₚ tₚᵢ L :=
  div_nonneg (claim5_24Bound_nonneg U tₕ tₚ tₚᵢ L hL) (by norm_num)

end BudgetNumerics

/-! ## DSFS context -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-! ## The two legs of the strict split (CO25 Eq. 55), as finer residuals

Each is strictly smaller than `Hyb34StepResidual`: a TV bound on **one** leg of the strict
split, at **half** the Claim 5.24 budget. `hyb34Step_of_divergence_collapse` (proven below)
is the reduction back to the full step. -/

section SplitResiduals

/-- **εA leg** (CO25 Eq. 55, bad-event mass): `Δ(Hyb₃, Hyb3Strict) ≤ claim5_24Bound/2`.
`Hyb3Strict` differs from `Hyb₃` only in the verifier-side `gᵢ` bridge (hit-only vs real);
the two agree on every `tr_i` memo hit, so this is exactly the probability that the `Hyb₃`
verifier's `D2SQuery` run produces a fresh `gᵢ` key (CO25's `E_𝒱`). Open: the §5.6 trace
analysis of the verifier's replayed trace (`BirthdayBound` accumulator + honest bad events
+ M2 reductions). -/
def Hyb34DivergenceResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb3 T_H T_P δ Salt oImpl V P)
        (Hyb3Strict T_H T_P δ Salt oImpl V P)
      ≤ hyb34SplitBudget U tₕ tₚ tₚᵢ L

/-- **εB leg** (CO25 Eq. 55, hit-path collapse): `Δ(Hyb3Strict, Hyb₄) ≤ claim5_24Bound/2`.
On the hit path the strict verifier serves exactly the table values the `Hyb₄` basic-FS
verifier reads (`d2sCodecBridgeImplMemoEagerHitOnly_coherent_serve` +
`memoCoherentTableEager_keystone` + the ψ-roundtrip of `VerifierReplay`); off the hit path
the strict game aborts, costing the same `E_𝒱` mass on the `Hyb₄` side. Open: the
structured-verifier analysis through the Figure-4 game skeleton. -/
def Hyb34CollapseResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb3Strict T_H T_P δ Salt oImpl V P)
        (Hyb4 oImpl V
          (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
      ≤ hyb34SplitBudget U tₕ tₚ tₚᵢ L

/-- **The reduction theorem** (CO25 Claim 5.24 via the symmetric Eq. 55 split): the two
finer residuals imply the full `Hyb34StepResidual`. Instantiates
`VerifierReplay.hyb34Step_of_strictSplit` at `εA = εB = hyb34SplitBudget`, whose sum is
exactly `claim5_24Bound` (`hyb34SplitBudget_add_self`). -/
theorem hyb34Step_of_divergence_collapse [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hA : Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hB : Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl :=
  hyb34Step_of_strictSplit T_H T_P δ Salt oImpl
    (fun tₕ tₚ tₚᵢ L => hyb34SplitBudget U tₕ tₚ tₚᵢ L)
    (fun tₕ tₚ tₚᵢ L => hyb34SplitBudget U tₕ tₚ tₚᵢ L)
    hA hB
    (fun tₕ tₚ tₚᵢ L => le_of_eq (hyb34SplitBudget_add_self U tₕ tₚ tₚᵢ L))

end SplitResiduals

/-! ## The εB per-query determinism layer: the strict verifier serves the `Hyb₄` table

`Hyb3Strict` and `Hyb₄` sample the **same** once-eager unsalted FS table `f ← 𝒟_IP`
(CO25 Eq. 54). The bricks below re-key the salted determinism layer of `VerifierReplay`
onto that unsalted table and close the per-query content of the hit-path collapse: every
challenge the strict verifier serves is the table value the basic-FS verifier re-derives. -/

section EagerTable

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- Pull an **unsalted** eager FS table back onto the salted Eq. 16 bridge surface by
erasing the salt component of the key — the table-level counterpart of
`saltEraseChallengePlusUnitImpl` (CO25 §5.8: the `Hyb₃` bridge queries the unsalted table
at the salt-erased key). -/
@[reducible]
def saltLiftTable (c : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec) :=
  fun q => c ⟨q.1, (q.2.1.1, q.2.2)⟩

/-- Instantiate the unsalted FS-challenge summand of the eager bridge's oracle surface
with a fixed eager table `c`, leaving the auxiliary `(Unit →ₒ U) + unifSpec` sampling
oracles free — the bridge's view of the `Hyb3Strict`/`Hyb₄` experiment after line 1
(`f ← 𝒟_IP`) has been sampled (unsalted twin of `VerifierReplay.fsTableAuxImpl`). -/
def fsTableAuxImplEager (c : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    QueryImpl
      (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle StmtIn pSpec))
      (OracleComp ((Unit →ₒ U) + unifSpec)) :=
  fun q =>
    match q with
    | .inl qf => pure (c qf)
    | .inr aux => query (spec := (Unit →ₒ U) + unifSpec) aux

/-- The salt-erasing re-keying composed with the unsalted table **is** the salted table
implementation at the pulled-back table: reading the unsalted table at the salt-erased key
is reading the pulled-back salted table at the original key. -/
lemma fsTableAuxImplEager_comp_saltErase
    (c : OracleFamily (fsChallengeOracle StmtIn pSpec)) :
    (fsTableAuxImplEager (U := U) c
        ∘ₛ saltEraseChallengePlusUnitImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (Salt := Salt))
      = fsTableAuxImpl (U := U) (saltLiftTable (Salt := Salt) c) := by
  funext q
  match q with
  | .inl qf =>
      simp only [QueryImpl.apply_compose, saltEraseChallengePlusUnitImpl, fsTableAuxImpl]
      erw [simulateQ_spec_query]
      rfl
  | .inr aux =>
      simp only [QueryImpl.apply_compose, saltEraseChallengePlusUnitImpl, fsTableAuxImpl]
      erw [simulateQ_spec_query]
      rfl

/-- Table-instantiated run transfer: the **eager** memoized bridge against the unsalted
table `c` is the **salted** memoized bridge against the pulled-back table — every salted
determinism brick of `VerifierReplay` re-keys onto the unsalted surface along this
identity. -/
lemma simulateQ_fsTableAuxImplEager_eager_run
    (c : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    simulateQ (fsTableAuxImplEager (U := U) c)
        (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run)
      = simulateQ (fsTableAuxImpl (U := U) (saltLiftTable (Salt := Salt) c))
          (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ) (Salt := Salt) gq).run memo).run) := by
  rw [d2sCodecBridgeImplMemoEager_run_eq, ← QueryImpl.simulateQ_compose,
    fsTableAuxImplEager_comp_saltErase]

/-- **The verifier-replay keystone on the unsalted eager surface** (CO25 Claim 5.24,
deterministic layer, as consumed by the εB leg): against the once-sampled unsalted table
`c` of `Hyb3Strict`/`Hyb₄` and a coherent `tr_i` memo, every response the `Hyb₃`-prover
bridge serves deserializes to `c` at the replayed **unsalted** basic-FS key
`(i, 𝕩, τ⁻¹(α̂))`, and coherence is preserved. By induction from the empty memo
(`memoCoherentTable_nil`), every challenge the simulated prover absorbs via the `gᵢ` path
matches the challenge the `Hyb₄` basic-FS verifier re-derives at the same key. -/
theorem memoCoherentTableEager_keystone
    (c : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hcoh : MemoCoherentTable (U := U) (δ := δ) (saltLiftTable (Salt := Salt) c) memo)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support (simulateQ (fsTableAuxImplEager (U := U) c)
      (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run))) :
    (Deserialize.deserialize r : pSpec.Challenge gq.1) = c ⟨gq.1, (gq.2.1, msgs)⟩
    ∧ MemoCoherentTable (U := U) (δ := δ) (saltLiftTable (Salt := Salt) c) memo' := by
  rw [simulateQ_fsTableAuxImplEager_eager_run] at h
  exact memoCoherentTable_keystone (saltLiftTable (Salt := Salt) c) gq memo hcoh msgs
    hparse r memo' h

end EagerTable

/-! ## The strict verifier bridge: inversion and coherent serving -/

section HitOnlyServe

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- Inversion for the strict (hit-only) verifier bridge: every **successful** answer is a
`tr_i` memo hit, and the memo is left untouched — the `Hyb3Strict` verifier replays
committed keys only and can never commit new ones (the run is oracle-free, so no table
instantiation is needed; compose with `support_simulateQ_subset` for instantiated runs). -/
theorem d2sCodecBridgeImplMemoEagerHitOnly_support_some_inv
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support
      (((d2sCodecBridgeImplMemoEagerHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run)) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r
    ∧ memo' = memo := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r₀ =>
      rw [d2sCodecBridgeImplMemoEagerHitOnly_run_hit gq memo r₀ hl] at h
      replace h : some (r, memo') ∈ support
          ((pure (some (r₀, memo)) : OracleComp
            (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle StmtIn pSpec))
            (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
              × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hr, hm⟩ := h
      -- `cases hl :` rewrote the goal's lookup occurrence to `some r₀`; both conjuncts
      -- close by reflexivity after transporting the two equalities.
      subst hr; subst hm
      exact ⟨rfl, rfl⟩
  | none =>
      rw [d2sCodecBridgeImplMemoEagerHitOnly_run_miss gq memo hl] at h
      replace h : some (r, memo') ∈ support
          ((pure none : OracleComp
            (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle StmtIn pSpec))
            (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
              × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
      simp at h

/-- **The εB keystone** (CO25 Claim 5.24, hit-path collapse, per query): against a `tr_i`
memo coherent with the once-sampled unsalted table `c`, every challenge the `Hyb3Strict`
verifier bridge serves deserializes to **exactly** the table value the `Hyb₄` basic-FS
verifier reads at the replayed key `(i, 𝕩, τ⁻¹(α̂))` — and the memo (hence coherence) is
unchanged. Combined with `memoCoherentTableEager_keystone` for the prover run (from
`memoCoherentTable_nil`), the strict verifier's re-derived transcript coincides pointwise
with the `Hyb₄` verifier's; the open part of the εB leg is purely the game-skeleton
threading and the off-hit-path abort mass. -/
theorem d2sCodecBridgeImplMemoEagerHitOnly_coherent_serve
    (c : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hcoh : MemoCoherentTable (U := U) (δ := δ) (saltLiftTable (Salt := Salt) c) memo)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support
      (((d2sCodecBridgeImplMemoEagerHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run)) :
    (Deserialize.deserialize r : pSpec.Challenge gq.1) = c ⟨gq.1, (gq.2.1, msgs)⟩
    ∧ memo' = memo := by
  obtain ⟨hl, hm⟩ := d2sCodecBridgeImplMemoEagerHitOnly_support_some_inv gq memo r memo' h
  exact ⟨hcoh gq.1 gq.2.1
    (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
    r msgs hl hparse, hm⟩

end HitOnlyServe

/-! ## Assembly: the campaign frontier re-based onto the two legs -/

section Assembly

/-- **The eager key lemma from the split legs** (CO25 Lemma 5.1 via Claims 5.21–5.23 +
the symmetric Eq. 55 split): Claims 5.21–5.23 plus the two finer Claim 5.24 residuals
imply the full eager key lemma. Composes `hyb34Step_of_divergence_collapse` with
`KeyLemmaAssembly.keyLemmaEager_of_hybSteps` (witness budgets already discharged by
`SimulatorBudgets`). -/
theorem keyLemmaEager_of_steps_divergenceCollapse
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
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
    (hA : Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hB : Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  KeyLemmaAssembly.keyLemmaEager_of_hybSteps T_H T_P δ Salt oImpl h01 h12 h23
    (hyb34Step_of_divergence_collapse T_H T_P δ Salt oImpl hA hB)

end Assembly

end DuplexSpongeFS.Hyb34Step

#print axioms DuplexSpongeFS.Hyb34Step.hyb34SplitBudget_add_self
#print axioms DuplexSpongeFS.Hyb34Step.claim5_24Bound_nonneg
#print axioms DuplexSpongeFS.Hyb34Step.hyb34SplitBudget_nonneg
#print axioms DuplexSpongeFS.Hyb34Step.hyb34Step_of_divergence_collapse
#print axioms DuplexSpongeFS.Hyb34Step.fsTableAuxImplEager_comp_saltErase
#print axioms DuplexSpongeFS.Hyb34Step.simulateQ_fsTableAuxImplEager_eager_run
#print axioms DuplexSpongeFS.Hyb34Step.memoCoherentTableEager_keystone
#print axioms DuplexSpongeFS.Hyb34Step.d2sCodecBridgeImplMemoEagerHitOnly_support_some_inv
#print axioms DuplexSpongeFS.Hyb34Step.d2sCodecBridgeImplMemoEagerHitOnly_coherent_serve
#print axioms DuplexSpongeFS.Hyb34Step.keyLemmaEager_of_steps_divergenceCollapse

end
