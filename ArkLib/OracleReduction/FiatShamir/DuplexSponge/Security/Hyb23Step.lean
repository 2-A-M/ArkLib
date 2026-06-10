/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.VerifierReplay

/-!
# CO25 Claim 5.23 — the `Hyb₂ → Hyb₃` step: salted split and per-query coupling bricks

`KeyLemmaHybrids.Hyb23StepResidual` demands `Δ(Hyb₂, Hyb₃) = 0`. In CO25 the claim is exact
because the two hybrids differ *only* in the query format of the once-sampled challenge
oracle: `Hyb₂` answers a `gᵢ` query `(i, 𝕩, τ̂, α̂)` by `ψᵢ⁻¹(eᵢ(𝕩, τ̂, α̂))` with `e ← 𝒟_e`
(Eq. 52), while the **paper's** `Hyb₃` answers it by `ψᵢ⁻¹(fᵢ((𝕩, bin(τ̂)), φ⁻¹(α̂)))` with
`f ← 𝒟_IP` over the **salted** statement `(𝕩, τ̌)` (Eq. 54). On the simulator-gated key
space (`D2SQuery` Item 4(e) emits `gᵢ` queries only after the `∀ι, α̂_ι ∈ Im(φ_ι)` check)
the key map `(τ̂, α̂) ↦ (bin(τ̂), φ⁻¹(α̂))` is injective, both sides sample the `ψ⁻¹`
preimage **fresh per query**, and both tables are uniform — so the response processes are
identical and the step costs exactly `0`.

The in-tree eager `Hyb₃` (`KeyLemmaHybrids.Hyb3`) is **not** the paper's `Hyb₃`: the rebuilt
ladder bundles two further changes into the same step —

1. **memoization** — `d2sCodecBridgeImplMemoEager` threads the `tr_i` memo (CO25 §5.4
   D2SAlgo Item 3), so a repeated `gᵢ` key returns the *identical* stored `ρ̂ᵢ`, whereas
   `Hyb₂`'s memoless `gImplDecodedChallenge` re-samples a fresh `ψᵢ⁻¹` preimage of the same
   challenge each time;
2. **salt erasure** — the `fᵢ` query is re-keyed onto the **unsalted**
   `fsChallengeOracle StmtIn pSpec`, so two `gᵢ` keys differing only in the salt `τ̂` read
   the *same* table cell, whereas `Hyb₂`'s `eSpec` table keys on the salt and answers them
   independently.

This module therefore splits the step at the two paper-faithful intermediate hybrids

`Hyb₂ —(A: query re-format, CO25 Claim 5.23 proper)→ Hyb3SaltedFresh
      —(B: tr_i memoization)→ Hyb3SaltedMemo —(C: salt erasure)→ Hyb₃`

where `Hyb3SaltedFresh` is `hybGameEager` over the salted `𝒟_IP` with the **memoless**
Eq. 16 bridge (the paper's `Hyb₃`), and `Hyb3SaltedMemo` is the same game with the salted
memoized bridge `d2sCodecBridgeImplMemo`; both push logs to the unsalted output surface via
the deterministic per-entry salt erasure `eraseSaltLog` (line 4).

## Proven here (no `sorry`, axiom-clean)

- `hyb23Step_of_saltedSplit` — **the reduction theorem**: the three finer `= 0` residuals
  assemble (TV triangle + nonnegativity) into the full `Hyb23StepResidual`.
- `gImplDecodedChallenge_run_eq_bridgeSalted_run` — **the per-query content of Claim 5.23**:
  against fixed tables `e` / `c` that agree along the key map
  (`e(i, 𝕩, τ̂, α̂) = c(i, (𝕩, bin τ̂), φ⁻¹(α̂))`), the `Hyb₂` realization and the memoless
  salted bridge are *equal* computations at every parse-successful key.
- `simulateQ_uniformDeserializePreimage_tableAux_eq` — the `ψ⁻¹` preimage sampler is
  oblivious to the challenge-oracle summand: simulated against any two fixed tables it is
  the *same* `(Unit →ₒ U) + unifSpec` computation (the `ψ⁻¹` half of the coupling).
- `d2sCodecBridgeImplMemo_fst_run_miss` — on a `tr_i` miss the memoized bridge's *response*
  process is exactly the memoless bridge: memoization is invisible on first-seen keys.
- `deserialize_replay_eq_deserialize_fresh` — on a `tr_i` hit, the replayed response and any
  fresh memoless response **deserialize to the same challenge** against the fixed table
  (given a `c`-coherent memo): the memo/memoless asymmetry is invisible through `ψ`, hence
  invisible in the line-4 projected logs and in every decoded challenge the verifier derives.
- `d2sCodecBridgeImplSalted_run` (run shape of the memoless salted bridge) and
  `eraseSaltLog_append` (line-4 projection homomorphism).

## The finer residuals (named obligations, NOT proven) and the honest obstruction map

- `Hyb23DecodedQueryResidual` (step A) — the genuine CO25 Claim 5.23. The per-query coupling
  is proven here; what remains is the game-level lift: re-indexing the uniform `eSpec` table
  sample along the key map and pushing the pointwise equality through `hybGameEager` by a
  `simulateQ`-level coupling, plus `φ⁻¹`-injectivity on its success domain. The latter
  cannot currently even be *stated* against the in-tree parser:
  `TraceTransform.decodeMessagesPrefixPhiInv?` (and its step functions) are `private`, so an
  upstream visibility change is a prerequisite.
- `Hyb23MemoTransparencyResidual` (step B) — memoization transparency. The deterministic
  layer is covered by the bricks here and in `VerifierReplay` (miss: identical response
  process; hit: pure replay, `ψ`-equal to any fresh re-sample). **Honest caveat**: the raw
  encoded `ρ̂ᵢ` of a repeated key (memoized: identical; memoless: fresh preimage) is
  re-exposed to the prover through fresh squeeze states whenever the repeat arrives at a
  fresh forward-perm input whose backtrack reproduces an already-queried tuple
  (`d2sHandleBacktrackSome` discards the `gᵢ` response on Item 4(e)ii `inlu` hits, so this
  needs a backward-edge/capacity collision) — a birthday-type event of *positive*
  probability. The exact-`0` form of this residual therefore likely requires the §5.6 trace
  analysis to attribute that event's mass to the Claim 5.21/5.24 budgets, or an upstream
  re-statement of the step bounds.
- `Hyb23SaltErasureResidual` (step C) — **flagged as a structural gap of the eager ladder**:
  for `δ > 0` this residual appears genuinely false rather than merely open. A malicious
  prover that runs two absorb paths differing only in the salt `τ̂` obtains, at the same
  `(𝕩, α̂)`, *independent* challenges from the salted table but *equal* challenges from the
  salt-erased table; the difference is visible through the deserialized squeeze outputs and
  through same-key entries of the line-4 projected prover log, giving a distinguisher of
  advantage `≈ 1 − 1/|ℳ_{V,i}|`. CO25 never makes this change: its `Hyb₃`/`Hyb₄` (and
  Lemma 5.1 itself) stay on the **salted** FS game `fsChallengeOracle (StmtIn × Salt) pSpec`.
  Discharging step C — and hence `Hyb23StepResidual` as stated — likely requires either
  restricting to `δ = 0` (no salt blocks parsed by `backTrack`) or re-keying the eager
  surface on salted statements, mirroring CO25. This finding should be weighed upstream
  before further effort is spent on the `= 0` claim of the rebuilt step.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb23Step

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
  VerifierReplay

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it
-- (repo precedent: the sibling lane modules `VerifierReplay`, `SimulatorBudgets`).
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

/-! ## Line 4 of the salted intermediates: deterministic per-entry salt erasure -/

section SaltedLineFour

variable {Salt : Type}

/-- Erase the salt component from every challenge-oracle key of a salted basic-FS log:
`(i, ((𝕩, τ̌), α_{<i})) ↦ ρᵢ` becomes `(i, (𝕩, α_{<i})) ↦ ρᵢ`; shared-`oSpec` entries are
kept verbatim. This is the deterministic line-4 map of the salted intermediate hybrids
(the paper's `Hyb₃` log surface re-keyed onto the eager unsalted output surface). -/
def eraseSaltLog
    (log : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) :=
  log.map fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => ⟨.inl q, r⟩
    | ⟨.inr ⟨i, ((x, _s), msgs)⟩, ch⟩ => ⟨.inr ⟨i, (x, msgs)⟩, ch⟩

/-- Salt erasure is a log homomorphism (twin of `KeyLemmaFoundations.projectSharedQueryLog_append`;
needed by any game-rewrite step that splits `proveQueryLog ++ verifyQueryLog`). -/
lemma eraseSaltLog_append
    (l₁ l₂ : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    eraseSaltLog (oSpec := oSpec) (l₁ ++ l₂)
      = eraseSaltLog (oSpec := oSpec) l₁ ++ eraseSaltLog (oSpec := oSpec) l₂ := by
  simp [eraseSaltLog]

/-- CO25 §5.8, line 4 for the salted intermediate hybrids: the (pure) per-entry salt
erasure, in the `UnitSampleM` shape consumed by `hybGameEager`. -/
noncomputable def saltErasingLineFour
    (log : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  pure (eraseSaltLog (oSpec := oSpec) log)

end SaltedLineFour

/-! ## The memoless salted Eq. 16 bridge (the paper's `Hyb₃` `gᵢ`-realization) -/

section SaltedBridge

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- CO25 §5.8, the **paper's** `Hyb₃` `gᵢ`-realization: the raw Eq. 16 codec bridge
`ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` against the **salted** FS oracle, with **no** `tr_i` memo — every query
performs a fresh `ψ⁻¹` preimage sample, exactly like `Hyb₂`'s `gImplDecodedChallenge`.
Trivial inner state `M := PUnit`. -/
noncomputable def d2sCodecBridgeImplSalted :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (fsChallengeOracle (StmtIn × Salt) pSpec) PUnit :=
  fun gq =>
    StateT.lift
      (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq)

/-- Run shape of the memoless salted bridge: the trivial state is threaded through
unchanged around the raw Eq. 16 bridge (abort propagating as `none`). -/
lemma d2sCodecBridgeImplSalted_run
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) (s : PUnit) :
    ((d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run s).run
      = (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run >>= fun o =>
            match o with
            | none => pure none
            | some r => pure (some (r, s)) := by
  unfold d2sCodecBridgeImplSalted
  simp only [StateT.run_lift, OptionT.run_bind, OptionT.run_pure]
  unfold Option.elimM
  refine bind_congr fun o => ?_
  match o with
  | none => rfl
  | some r => rfl

end SaltedBridge

/-! ## The salted intermediate hybrids -/

section SaltedHybrids

/-- The **paper's** `Hyb₃` (CO25 §5.8, Eq. 54): the salted basic-FS challenge functions
`f = (fᵢ)ᵢ ← 𝒟_IP` over `fsChallengeOracle (StmtIn × Salt) pSpec` sampled eagerly as one
uniform table, `gᵢ` realized by the **memoless** Eq. 16 bridge (fresh `ψ⁻¹` per query, like
`Hyb₂`); line-4 map = deterministic salt erasure onto the unsalted output surface. -/
noncomputable def Hyb3SaltedFresh [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (saltErasingLineFour (Salt := Salt)) oImpl V P]

/-- The salted **memoized** intermediate: as `Hyb3SaltedFresh`, but with the `tr_i`-memoized
salted Eq. 16 bridge `d2sCodecBridgeImplMemo` (CO25 §5.4 D2SAlgo Item 3). Differs from
`Hyb3SaltedFresh` only in memoization, and from the in-tree `Hyb₃` only in the salt
erasure boundary (here at line 4; there inside the bridge at the `fᵢ`-query boundary). -/
noncomputable def Hyb3SaltedMemo [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt))
      (saltErasingLineFour (Salt := Salt)) oImpl V P]

end SaltedHybrids

/-! ## The three finer step residuals (CO25 Claim 5.23, factored) -/

section StepResiduals

/-- Step A — **CO25 Claim 5.23 proper**: switching the decoded challenge table `e ← 𝒟_e`
(keys = encoded salted tuples) for the salted basic-FS table `f ← 𝒟_IP` behind the memoless
`ψ⁻¹ ∘ f ∘ φ⁻¹` bridge is a pure query re-format — TV distance exactly `0`. Open core: the
game-level lift of the proven per-query coupling
(`gImplDecodedChallenge_run_eq_bridgeSalted_run`) — re-index the uniform table sample along
the key map `(τ̂, α̂) ↦ (bin τ̂, φ⁻¹ α̂)` and push through `hybGameEager`; needs
`φ⁻¹`-injectivity on its success domain (blocked: the parser is `private` upstream). -/
def Hyb23DecodedQueryResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb2 T_H T_P δ oImpl V P)
      (Hyb3SaltedFresh T_H T_P δ Salt oImpl V P) = 0

/-- Step B — `tr_i` **memoization transparency**: adding the D2SAlgo Item 3 memo to the
salted bridge does not change the game distribution. Deterministic toolkit proven here
(`d2sCodecBridgeImplMemo_fst_run_miss`, `deserialize_replay_eq_deserialize_fresh`) and in
`VerifierReplay` (hit purity/commit/replay). Open core: repeat-key raw responses re-exposed
through fresh squeeze states are a positive-probability (birthday-type) event — see the
module header for why the exact-`0` form likely needs the §5.6 budget attribution. -/
def Hyb23MemoTransparencyResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb3SaltedFresh T_H T_P δ Salt oImpl V P)
      (Hyb3SaltedMemo T_H T_P δ Salt oImpl V P) = 0

/-- Step C — **salt erasure**: moving the salt erasure from line 4 (after the salted table
read) into the bridge's `fᵢ`-query boundary (before the table read) does not change the
game distribution. **Flagged**: for `δ > 0` this appears genuinely false (salt-grinding
distinguisher, see the module header) — CO25 keeps the salted FS oracle through `Hyb₄` and
never performs this re-keying; treat this residual as a structural decision point for the
eager ladder rather than a proof obligation to brute-force. -/
def Hyb23SaltErasureResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb3SaltedMemo T_H T_P δ Salt oImpl V P)
      (Hyb3 T_H T_P δ Salt oImpl V P) = 0

end StepResiduals

/-! ## The reduction theorem: the salted split discharges the Claim 5.23 step -/

section Assembly

/-- **The Claim 5.23 split skeleton (proven)**: the three finer residuals — query re-format
(A), memoization transparency (B), salt erasure (C) — assemble into the full
`KeyLemmaHybrids.Hyb23StepResidual` by the TV triangle inequality and nonnegativity.
Each hypothesis is strictly smaller than the parent residual: it isolates exactly one of
the three structural changes the rebuilt ladder bundles into the `Hyb₂ → Hyb₃` step. -/
theorem hyb23Step_of_saltedSplit [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hA : Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hB : Hyb23MemoTransparencyResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hC : Hyb23SaltErasureResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl := by
  intro V P
  have h1 := hA V P
  have h2 := hB V P
  have h3 := hC V P
  have t1 := SPMF.tvDist_triangle (Hyb2 T_H T_P δ oImpl V P)
    (Hyb3SaltedFresh T_H T_P δ Salt oImpl V P) (Hyb3 T_H T_P δ Salt oImpl V P)
  have t2 := SPMF.tvDist_triangle (Hyb3SaltedFresh T_H T_P δ Salt oImpl V P)
    (Hyb3SaltedMemo T_H T_P δ Salt oImpl V P) (Hyb3 T_H T_P δ Salt oImpl V P)
  have hnn := SPMF.tvDist_nonneg (Hyb2 T_H T_P δ oImpl V P)
    (Hyb3 T_H T_P δ Salt oImpl V P)
  linarith

end Assembly

/-! ## Per-query coupling bricks (the deterministic layer of steps A and B) -/

section CouplingBricks

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- Instantiate the decoded-challenge summand of the `Hyb₂` oracle surface with a fixed
eager table `e ← 𝒟_e`, leaving the auxiliary `(Unit →ₒ U) + unifSpec` sampling oracles
free (the `eSpec` twin of `VerifierReplay.fsTableAuxImpl`). -/
def eTableAuxImpl (e : OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl
      (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
      (OracleComp ((Unit →ₒ U) + unifSpec)) :=
  fun q =>
    match q with
    | .inl qe => pure (e qe)
    | .inr aux => query (spec := (Unit →ₒ U) + unifSpec) aux

/-- The `ψᵢ⁻¹` uniform-preimage sampler is **oblivious to the challenge-oracle summand**:
its only oracle interaction is the `unifSpec` index draw, so simulating it against the
`Hyb₂` table surface and against the salted basic-FS table surface yields the *same*
`(Unit →ₒ U) + unifSpec` computation. This is the `ψ⁻¹` half of the Claim 5.23 per-query
coupling. -/
lemma simulateQ_uniformDeserializePreimage_tableAux_eq
    (e : OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    {i : pSpec.ChallengeIdx} (ch : pSpec.Challenge i) :
    simulateQ (eTableAuxImpl (U := U) e)
        (uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := eSpec (U := U) StmtIn pSpec δ) ch)
      = simulateQ (fsTableAuxImpl (U := U) c)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch) := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- **The per-query content of CO25 Claim 5.23**: at any parse-successful `gᵢ` key, against
fixed tables that agree along the key map `(i, 𝕩, τ̂, α̂) ↦ (i, (𝕩, bin τ̂), φ⁻¹(α̂))`, the
`Hyb₂` realization (`ψ⁻¹` of the decoded-table read) and the **memoless** salted Eq. 16
bridge (`ψ⁻¹ ∘ f ∘ φ⁻¹`) are *equal* computations over the shared auxiliary sampling
oracles. The game-level lift of this equality (re-indexing the uniform table sample along
the key map) is exactly the open core of `Hyb23DecodedQueryResidual`. -/
theorem gImplDecodedChallenge_run_eq_bridgeSalted_run
    (e : OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (hagree : e gq = c (replayKey (Salt := Salt) gq msgs))
    (s : PUnit) :
    simulateQ (eTableAuxImpl (U := U) e)
        (((gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ) gq).run s).run)
      = simulateQ (fsTableAuxImpl (U := U) c)
          (((d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
              (δ := δ) (Salt := Salt) gq).run s).run) := by
  have hL : simulateQ (eTableAuxImpl (U := U) e)
      (((gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ) gq).run s).run)
      = (simulateQ (eTableAuxImpl (U := U) e)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := eSpec (U := U) StmtIn pSpec δ) (e gq))) >>= fun v =>
              pure (some (v, s)) := by
    unfold gImplDecodedChallenge
    simp only [StateT.run_bind, StateT.run_lift, OptionT.run_bind,
      simulateQ_bind, Option.elimM, Option.elim, bind_pure_comp]
    rfl
  have hR : simulateQ (fsTableAuxImpl (U := U) c)
      (((d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run s).run)
      = (simulateQ (fsTableAuxImpl (U := U) c)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
            (c (replayKey (Salt := Salt) gq msgs)))) >>= fun v =>
              pure (some (v, s)) := by
    rw [d2sCodecBridgeImplSalted_run]
    unfold d2sCodecBridgeImpl
    simp only [hparse]
    simp only [OptionT.run_bind, OptionT.run_lift, pure_bind, Option.elimM, Option.elim,
      simulateQ_bind, simulateQ_map, bind_pure_comp, bind_assoc]
    rfl
  rw [hL, hR, hagree, simulateQ_uniformDeserializePreimage_tableAux_eq e c]

/-- Memoization transparency, miss case: on a fresh (`tr_i`-miss) key, the **response**
process of the memoized salted bridge is exactly the memoless bridge — projecting away the
memo component recovers `d2sCodecBridgeImpl` on the nose. Together with the hit-purity and
replay bricks of `VerifierReplay`, this is the deterministic layer of
`Hyb23MemoTransparencyResidual`. -/
theorem d2sCodecBridgeImplMemo_fst_run_miss
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) memo gq.1 gq.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 = none) :
    (Option.map Prod.fst <$>
        ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run memo).run)
      = (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run := by
  rw [d2sCodecBridgeImplMemo_run_miss gq memo hl, map_bind]
  refine Eq.trans (bind_congr fun o => ?_) (bind_pure _)
  match o with
  | none => simp
  | some resp => simp

/-- Memoization transparency, hit case (the `ψ`-level coupling): on a `tr_i` hit at a
parse-successful key, the **replayed** response and **any** fresh response of the memoless
bridge against the same fixed table deserialize to the *same* challenge — the table value at
the replayed key. The memo/memoless asymmetry is therefore invisible through `ψ`: invisible
in the line-4 projected logs (which record decoded challenges) and in every challenge the
verifier derives. What it does **not** cover — honestly — is the raw encoded `ρ̂ᵢ`
re-exposed through fresh squeeze states on repeat keys (see the module header). -/
theorem deserialize_replay_eq_deserialize_fresh
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    {memo : D2SAlgoMemo StmtIn U δ Salt pSpec}
    (hcoh : MemoCoherentTable (U := U) (δ := δ) c memo)
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    {r : Vector U (challengeSize (pSpec := pSpec) gq.1)}
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) memo gq.1 gq.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 = some r)
    {r' : Vector U (challengeSize (pSpec := pSpec) gq.1)}
    (hr' : some r' ∈ support (simulateQ (fsTableAuxImpl (U := U) c)
      ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run))) :
    (Deserialize.deserialize r : pSpec.Challenge gq.1) = Deserialize.deserialize r' := by
  have h1 : (Deserialize.deserialize r : pSpec.Challenge gq.1)
      = c (replayKey (Salt := Salt) gq msgs) :=
    hcoh gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1)
      gq.2.2.2 r msgs hl hparse
  have h2 : (Deserialize.deserialize r' : pSpec.Challenge gq.1)
      = c (replayKey (Salt := Salt) gq msgs) :=
    deserialize_of_mem_support_bridge_table c gq msgs hparse r' hr'
  rw [h1, h2]

end CouplingBricks

#print axioms DuplexSpongeFS.Hyb23Step.eraseSaltLog_append
#print axioms DuplexSpongeFS.Hyb23Step.d2sCodecBridgeImplSalted_run
#print axioms DuplexSpongeFS.Hyb23Step.hyb23Step_of_saltedSplit
#print axioms DuplexSpongeFS.Hyb23Step.simulateQ_uniformDeserializePreimage_tableAux_eq
#print axioms DuplexSpongeFS.Hyb23Step.gImplDecodedChallenge_run_eq_bridgeSalted_run
#print axioms DuplexSpongeFS.Hyb23Step.d2sCodecBridgeImplMemo_fst_run_miss
#print axioms DuplexSpongeFS.Hyb23Step.deserialize_replay_eq_deserialize_fresh

end DuplexSpongeFS.Hyb23Step

end
