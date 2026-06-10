/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb01Step
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Step

/-!
# CO25 Claim 5.22 — the `θ★` bias-accounting pipeline for `Hyb12Mid → Hyb₂`

This module attacks `Hyb12Step.Hyb12BiasAccountingResidual` (the `Δ(Hyb12Mid, Hyb₂) ≤
claim5_22Bound` leg of CO25 Claim 5.22, Eq. 53): threading the per-derivation decoding-bias
coupling through the **actual** game pipeline (`hybGameEager`'s `d2fRaw`/`loggingOracle`
two-stage skeleton) with the `θ★` prover-side challenge-derivation budget and the
once-per-round verifier-side budget.

## Architecture: the lazily-memoized fresh pivot

`Hyb12Mid` and `Hyb₂` both sample their challenge oracle **eagerly** as one uniform table
(`OracleDistribution.uniform`), so repeated derivation keys are answered consistently. A
per-query accumulation argument, however, needs **per-query independent** implementations.
A naive i.i.d. fresh world would answer repeated keys independently — *distinguishable* from
the eager world by any prover that repeats a derivation, so a `Δ = 0` alignment to a
memoryless fresh world would be **false** in general. The pivot used here therefore
**memoizes**: a lazily-sampled challenge memo (`FreshChalMemoEntry` list) answers repeat
keys from the memo and pays the sampler only on fresh keys — the textbook lazy-sampling view
of the eager table, sound for adversarial repeat keys. Both pivot games are **one**
parametric game `hyb2GameFresh sampler` over the `Hyb₂` (`eSpec`) surface:

- `uniformChallengeSampler` (the `Hyb₂` side): fresh keys get `ρ ← 𝒰(ℳ_{V,i})`;
- `decodedChallengeSampler` (the `Hyb12Mid` side): fresh keys get `ψᵢ(ρ̂)`, `ρ̂ ← 𝒰(Σ^{ℓᵢ})`
  — the decoded view of `Hyb12Mid`'s encoded table (recall `gImplEncodedResampled` consumes
  its `gSpec` answer **only** through `ψᵢ` and the common fiber-resampling kernel, and the
  `Hyb₁` line-4 map records only `ψᵢ(ρ̂)`, so the decoded marginal is all that survives).

## Proven here (no `sorry`, axiom-clean)

1. **Stateful budgeted lifting bricks** (the round-indexed variants of
   `Hyb12Step.tvDist_evalDist_simulateQ_le_of_close`, needed because the memoizing pivot
   implementations are stateful):
   - `tvDist_bind_le_of_stages`: generic two-stage TV assembly for bind.
   - `tvDist_simulateQ_stateT_le_predBudget`: per-query TV cost `ε` on `p`-queries, budget
     `b`, gives `b · ε` (single-predicate / sup-cost form — the prover-side `θ★ · maxᵢ ε`).
   - `tvDist_simulateQ_stateT_le_classBudget`: **round-indexed** — classifier
     `f : ι → Option κ`, per-class costs `ε k` and budgets `b k`, gives `∑ k, b k · ε k`
     (the verifier-side `∑ᵢ ε_cdc,i` with one derivation per round).
2. **Per-step memoized coupling**: `freshChalImpl_step_tvDist_le` /
   `freshGameImpl_step_tvDist_le` — from any **common** memo, a memo hit is free, a fresh
   key costs the sampler distance (≤ `ε_cdc,i`), non-challenge oracles cost `0`.
3. **Per-derivation sampler coupling**: `tvDist_decodedChallengeSampler_uniform_le` —
   `Δ(ψᵢ(𝒰(Σ^ℓᵢ)), 𝒰(ℳᵢ)) ≤ ε_cdc,i` (`Codec.decode_isBiased` through
   `pmf_tvDist_le_l1`), the pushforward form of Eq. 53's per-derivation cost.
4. **`tvDist_hyb2GameFresh_le`** — *the `θ★` pipeline accounting*: for any two per-round
   samplers within `ε_cdc,i`, the two pivot games are within
   `θ★ · maxᵢ ε_cdc,i + ∑ᵢ ε_cdc,i = claim5_22Bound`, given the `θ★` prover-stage budget
   and the once-per-round verifier-stage budget on the **actual** `d2fRaw`-with-logging
   pipeline computations (`proverPipeline` / `verifierPipeline` — verbatim the stage
   computations of `hybGameEager` at the `Hyb₂` instantiation).
5. **`hyb12BiasAccounting_of_freshPipeline` (the proven reduction)**: the four finer
   residuals below assemble into the full `Hyb12BiasAccountingResidual`.

## Open core (named `*Residual : Prop`, NOT proven) — strictly finer than the target

- `Hyb2FreshAlignResidual` — `Δ(Hyb₂, hyb2GameFresh 𝒰) = 0`: the eager uniform `eSpec`
  table equals its lazily-memoized sampling view (the textbook eager↔lazy equivalence;
  *true* for adversarial repeat keys thanks to the memo — contrast the permutation-carrier
  subtlety that keeps `Hyb01Step.DDSFreshSwitchResidual` at an `ε` budget).
- `Hyb12MidFreshAlignResidual` — `Δ(Hyb12Mid, hyb2GameFresh (ψ ∘ 𝒰)) = 0`: same eager↔lazy
  step for the `gSpec` table **plus** the `gSpec → eSpec` world re-keying (encoded query
  log + `(φ⁻¹, ψ)` line-4 map versus decoded log + `φ⁻¹` line-4 map; per fresh derivation
  this is the already-proven `Hyb12Step.tvDist_gImplEncodedForward_gImplDecodedChallenge_le`
  coupling at distance 0 once the challenge marginal is fixed — the open content is the
  game-level lift).
- `Hyb12ProverPipelineBudgetResidual` — the prover-stage pipeline makes at most
  `θ★ = tₚ` challenge-oracle queries (CO25 §5.4: only forward-perm queries trigger
  derivations; F4/M1c genre — per-step dispatcher branch analysis plus `loggingOracle`
  budget transparency; the in-tree per-step cousin is `D2sQueryStepGSpecBudgetResidual`).
- `Hyb12VerifierPipelineBudgetResidual` — the verifier-stage pipeline derives each round's
  challenge at most once (honest-verifier single-derivation analysis; CO25 Eq. 53's
  "+ one per round" term).

## Accounting note (refinement headroom)

The accumulators charge the per-class cost on **every** challenge query, memo hits
included; hits actually cost `0`. A state-aware accumulator charging misses only would give
`min(θ★, #fresh keys) · maxᵢ ε`, strictly sharper than CO25's own Eq. 53 — not needed for
`claim5_22Bound`, so not built. The memo keys carry the full `(i, 𝕩, salt, α̂)` tuple, so
everything here is salt-uniform (works for every `δ`, no `δ = 0` specialization needed).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb12Accounting

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open Hyb01Step Hyb12Step
open scoped NNReal ENNReal

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## Generic stateful budgeted lifting bricks

`Hyb12Step.tvDist_evalDist_simulateQ_le_of_close` lifts per-query closeness through
*stateless* implementations. The lazily-memoized pivot implementations are stateful
(`StateT` over the challenge memo), and the verifier-side budget of CO25 Eq. 53 is
*round-indexed* (`∑ᵢ ε_cdc,i`, one derivation per round) rather than uniform. The two
accumulators below are the corresponding `StateT`-level carriers, companions of
`Hyb01Step.tvDist_simulateQ_stateT_le_sum_of_step` (which is size-indexed instead of
predicate- or class-budgeted). -/

section LiftingBricks

/-- Two-stage TV assembly: a bind moves total variation by at most the base distance plus a
uniform bound on the continuation distances. -/
lemma tvDist_bind_le_of_stages {γ β : Type} (a₁ a₂ : ProbComp γ) (k₁ k₂ : γ → ProbComp β)
    {c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (h₁ : tvDist a₁ a₂ ≤ c₁) (h₂ : ∀ x, tvDist (k₁ x) (k₂ x) ≤ c₂) :
    tvDist (a₁ >>= k₁) (a₂ >>= k₂) ≤ c₁ + c₂ := by
  have hA : tvDist (a₁ >>= k₁) (a₂ >>= k₁) ≤ c₁ :=
    le_trans (tvDist_bind_right_le _ _ _) h₁
  have hB : tvDist (a₂ >>= k₁) (a₂ >>= k₂) ≤ c₂ := by
    refine le_trans (tvDist_bind_left_le _ _ _) ?_
    exact tsum_probOutput_toReal_mul_tvDist_le _ _ _ hc₂ fun x _ => h₂ x
  have htri := tvDist_triangle (a₁ >>= k₁) (a₂ >>= k₁) (a₂ >>= k₂)
  linarith

/-- **Single-predicate stateful budget lifting** (the prover-side `θ★ · maxᵢ ε` carrier):
if two stateful implementations are, from every common state, within `ε` on `p`-queries and
identical in distribution elsewhere, then simulating a computation making at most `b`
`p`-queries moves total variation by at most `b · ε`. Stateful companion of
`Hyb12Step.tvDist_evalDist_simulateQ_le_of_close`. -/
theorem tvDist_simulateQ_stateT_le_predBudget
    {ι₁ : Type} {spec : OracleSpec ι₁} {α σ : Type}
    {impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)}
    {p : ι₁ → Prop} [DecidablePred p] {ε : ℝ} (hε : 0 ≤ ε)
    (hstep : ∀ t s, tvDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ if p t then ε else 0)
    {oa : OracleComp spec α} {b : ℕ}
    (hb : IsQueryBoundP oa p b) (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀) ≤ (b : ℝ) * ε := by
  induction oa using OracleComp.inductionOn generalizing b s₀ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      exact mul_nonneg (Nat.cast_nonneg b) hε
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      obtain ⟨hcan, hrest⟩ := hb
      have h₁ : tvDist
            ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
          ≤ if p t then ε else 0 :=
        le_trans (tvDist_bind_right_le _ _ _) (hstep t s₀)
      have h₂ : tvDist
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (mx us.1)).run us.2)
          ≤ ((if p t then b - 1 else b : ℕ) : ℝ) * ε := by
        refine le_trans (tvDist_bind_left_le _ _ _) ?_
        refine tsum_probOutput_toReal_mul_tvDist_le _ _ _
          (mul_nonneg (Nat.cast_nonneg _) hε) ?_
        intro us _
        exact ih us.1 (hrest us.1) us.2
      have htri := tvDist_triangle
        ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
        ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
        ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (mx us.1)).run us.2)
      -- establish the bound for the normalized bind form and close by defeq
      have hmain : tvDist
            ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (mx us.1)).run us.2)
          ≤ (b : ℝ) * ε := by
        by_cases hpt : p t
        · have hbpos : 0 < b := hcan.resolve_left (not_not_intro hpt)
          rw [if_pos hpt] at h₁ h₂
          have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
            rw [Nat.cast_sub hbpos]
            norm_num
          rw [hcast] at h₂
          have hring : ((b : ℝ) - 1) * ε + ε = (b : ℝ) * ε := by ring
          linarith
        · rw [if_neg hpt] at h₁ h₂
          linarith
      simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query,
        monadLift_self]
      exact hmain

/-- **Round-indexed stateful budget lifting** (the verifier-side `∑ᵢ ε_cdc,i` carrier): if a
classifier `f : ι₁ → Option κ` assigns each query a class (or none), the two stateful
implementations are within `ε k` on class-`k` queries from every common state (and identical
elsewhere), and the computation makes at most `b k` class-`k` queries, then the simulations
are within `∑ k, b k · ε k`. This is the round-indexed variant of the impl-closeness lifting
brick demanded by the `∑ᵢ ε_cdc,i` shape of `claim5_22Bound`. -/
theorem tvDist_simulateQ_stateT_le_classBudget
    {ι₁ : Type} {κ : Type} [Fintype κ] [DecidableEq κ]
    {spec : OracleSpec ι₁} {α σ : Type}
    {impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)}
    (f : ι₁ → Option κ) {ε : κ → ℝ} (hε : ∀ k, 0 ≤ ε k)
    (hstep : ∀ t s, tvDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ (f t).elim 0 ε)
    {oa : OracleComp spec α} {b : κ → ℕ}
    (hb : ∀ k, IsQueryBoundP oa (fun t => f t = some k) (b k)) (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀)
      ≤ ∑ k, (b k : ℝ) * ε k := by
  induction oa using OracleComp.inductionOn generalizing b s₀ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (hε k)
  | query_bind t mx ih =>
      have hb' : ∀ k, (¬ f t = some k ∨ 0 < b k) ∧
          ∀ u, IsQueryBoundP (mx u) (fun t' => f t' = some k)
            (if f t = some k then b k - 1 else b k) := fun k => by
        have h := hb k
        rwa [isQueryBoundP_query_bind_iff] at h
      have h₁ : tvDist
            ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
          ≤ (f t).elim 0 ε :=
        le_trans (tvDist_bind_right_le _ _ _) (hstep t s₀)
      have h₂ : tvDist
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (mx us.1)).run us.2)
          ≤ ∑ k, ((if f t = some k then b k - 1 else b k : ℕ) : ℝ) * ε k := by
        refine le_trans (tvDist_bind_left_le _ _ _) ?_
        refine tsum_probOutput_toReal_mul_tvDist_le _ _ _
          (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (hε k)) ?_
        intro us _
        exact ih us.1 (fun k => (hb' k).2 us.1) us.2
      have htri := tvDist_triangle
        ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
        ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
        ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (mx us.1)).run us.2)
      -- establish the bound for the normalized bind form and close by defeq
      have hmain : tvDist
            ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (mx us.1)).run us.2)
          ≤ ∑ k, (b k : ℝ) * ε k := by
        rcases hft : f t with _ | k₀
        · -- no class: zero step cost, budgets unchanged
          rw [hft, Option.elim_none] at h₁
          have hsum : (∑ k, ((if f t = some k then b k - 1 else b k : ℕ) : ℝ) * ε k)
              = ∑ k, (b k : ℝ) * ε k :=
            Finset.sum_congr rfl fun k _ => by rw [hft]; simp
          rw [hsum] at h₂
          linarith
        · -- class `k₀`: pay `ε k₀`, decrement the `k₀` budget
          have hpos : 0 < b k₀ := by
            rcases (hb' k₀).1 with hn | hp
            · exact absurd hft hn
            · exact hp
          rw [hft, Option.elim_some] at h₁
          have hsum : (∑ k, ((if f t = some k then b k - 1 else b k : ℕ) : ℝ) * ε k)
              = (∑ k, (b k : ℝ) * ε k) - ε k₀ := by
            have hterm : ∀ k ∈ Finset.univ,
                ((if f t = some k then b k - 1 else b k : ℕ) : ℝ) * ε k
                  = (b k : ℝ) * ε k - (if k = k₀ then ε k₀ else 0) := by
              intro k _
              by_cases hk : k = k₀
              · subst hk
                have hcast : ((b k - 1 : ℕ) : ℝ) = (b k : ℝ) - 1 := by
                  rw [Nat.cast_sub hpos]
                  norm_num
                rw [hft, if_pos rfl, if_pos rfl, hcast]
                ring
              · have hne : ¬ f t = some k := by
                  rw [hft]
                  exact fun hcon => hk (Option.some.inj hcon).symm
                rw [if_neg hne, if_neg hk, sub_zero]
            rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
              Finset.sum_ite_eq' Finset.univ k₀ (fun _ => ε k₀),
              if_pos (Finset.mem_univ k₀)]
          rw [hsum] at h₂
          linarith
      simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query,
        monadLift_self]
      exact hmain

end LiftingBricks

/-! ## DSFS context -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {δ : ℕ}

/-- `SpongeUnit` provides `Zero`; expose the canonical `Inhabited` locally. Not exported. -/
local instance : Inhabited U := ⟨0⟩

/-- Local `VCVCompatible U` (giving `Fintype (Vector U m)` via `Vector.instFintype`).
Not exported. -/
local instance : VCVCompatible U where
  type_decidableEq' := inferInstance

/-- Local `Inhabited` for encoded blocks. Not exported. -/
local instance {m : ℕ} : Inhabited (Vector U m) := ⟨Vector.replicate m default⟩

/-- Local uniform sampling for decoded challenges (from `VCVCompatible` finiteness).
Not exported. -/
local instance (i : pSpec.ChallengeIdx) : SampleableType (pSpec.Challenge i) :=
  SampleableType.ofFintype _

/-! ## The per-round challenge samplers and their Eq. 53 coupling -/

section Samplers

/-- The `Hyb₂`-side fresh-key sampler: a uniform decoded challenge `ρ ← 𝒰(ℳ_{V,i})`. -/
noncomputable def uniformChallengeSampler (i : pSpec.ChallengeIdx) :
    ProbComp (pSpec.Challenge i) :=
  $ᵗ (pSpec.Challenge i)

/-- The `Hyb12Mid`-side fresh-key sampler: the decoded view `ψᵢ(ρ̂)` of a uniform encoded
block `ρ̂ ← 𝒰(Σ^{ℓ_V(i)})` — the only datum `Hyb12Mid` extracts from its eager `gSpec`
table (both `gImplEncodedResampled` and the `Hyb₁` line-4 map factor through `ψᵢ`). -/
noncomputable def decodedChallengeSampler [SampleableType U] (i : pSpec.ChallengeIdx) :
    ProbComp (pSpec.Challenge i) :=
  ($ᵗ (Vector U (challengeSize (pSpec := pSpec) i)) : ProbComp _) >>= fun v =>
    pure (Deserialize.deserialize v : pSpec.Challenge i)

/-- Lifting a `PMF` and post-composing a pure map is the lift of the pushforward. -/
lemma spmf_liftM_bind_pure {α β : Type} (p : PMF α) (g : α → β) :
    ((liftM p : SPMF α) >>= fun a => (pure (g a) : SPMF β)) = (liftM (p.map g) : SPMF β) := by
  have h : ((liftM p : SPMF α) >>= fun a => (pure (g a) : SPMF β))
      = ((liftM p : SPMF α) >>= fun a => liftM (PMF.pure (g a))) := by
    simp only [SPMF.lift_pure]
  rw [h, spmf_liftM_bind]
  rfl

/-- **CO25 Eq. 53, per fresh derivation, sampler form**: the decoded view of a uniform
encoded block and a uniform decoded challenge are within the codec decoding bias
`ε_cdc,i` (`Codec.decode_isBiased` through `pmf_tvDist_le_l1`). -/
theorem tvDist_decodedChallengeSampler_uniform_le [SampleableType U]
    (i : pSpec.ChallengeIdx) :
    tvDist (decodedChallengeSampler (U := U) (pSpec := pSpec) i)
        (uniformChallengeSampler (pSpec := pSpec) i)
      ≤ (codec.decodingBias i : ℝ) := by
  unfold tvDist decodedChallengeSampler uniformChallengeSampler
  have h₁ : 𝒟[($ᵗ (Vector U (challengeSize (pSpec := pSpec) i)) : ProbComp _) >>= fun v =>
        pure (Deserialize.deserialize v : pSpec.Challenge i)]
      = (liftM ((PMF.uniformOfFintype (Vector U (challengeSize (pSpec := pSpec) i))).map
          (fun v => (Deserialize.deserialize v : pSpec.Challenge i))) : SPMF _) := by
    refine (evalDist_bind _ _).trans ?_
    rw [evalDist_uniformSample]
    refine (bind_congr fun v => evalDist_pure _).trans ?_
    exact spmf_liftM_bind_pure _ _
  have h₂ : 𝒟[($ᵗ (pSpec.Challenge i) : ProbComp _)]
      = (liftM (PMF.uniformOfFintype (pSpec.Challenge i)) : SPMF _) :=
    evalDist_uniformSample (pSpec.Challenge i)
  rw [h₁, h₂]
  refine le_trans (spmf_tvDist_liftM_le _ _) ?_
  rw [PMF.tvDist_comm]
  exact le_trans (pmf_tvDist_le_l1 _ _) (codec.decode_isBiased i)

end Samplers

/-! ## The lazily-memoized fresh challenge implementation

The eager `eSpec`/`gSpec` tables answer repeat keys consistently; a memoryless fresh
implementation would not, and the resulting alignment claim would be false for adversarial
repeat keys. The implementation below memoizes lazily: hits are answered from the memo
(deterministically — zero TV cost from a common memo), misses pay the sampler. -/

section MemoImpl

/-- One lazily-sampled challenge-table entry: the full `eSpec` derivation key
`(i, 𝕩, salt, α̂)` with its sampled decoded challenge. -/
structure FreshChalMemoEntry (StmtIn U : Type) (δ : ℕ) {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] where
  /-- The challenge round being derived. -/
  roundIdx : pSpec.ChallengeIdx
  /-- The queried statement. -/
  stmt : StmtIn
  /-- The queried on-sponge salt. -/
  salt : Vector U δ
  /-- The queried encoded prover-message prefix. -/
  encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc
  /-- The lazily sampled decoded challenge. -/
  response : pSpec.Challenge roundIdx

open Classical in
/-- Lookup in the lazy challenge memo (first match wins; mirrors `lookupD2SAlgoMemo`). -/
noncomputable def lookupFreshChalMemo
    (memo : List (FreshChalMemoEntry StmtIn U δ pSpec))
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    Option (pSpec.Challenge i) :=
  memo.foldl (init := none) fun acc e =>
    acc.orElse fun _ =>
      if hR : e.roundIdx = i then by
        subst hR
        exact if e.stmt = stmt ∧ e.salt = salt ∧ e.encodedMessages = em
          then some e.response else none
      else none

/-- The lazily-memoized fresh challenge implementation over the `Hyb₂` (`eSpec`) surface:
memo hits are answered deterministically, fresh keys pay the per-round `sampler` once and
are recorded. -/
noncomputable def freshChalImpl
    (sampler : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i)) :
    QueryImpl (eSpec (U := U) StmtIn pSpec δ)
      (StateT (List (FreshChalMemoEntry StmtIn U δ pSpec)) ProbComp) :=
  fun q memo =>
    (lookupFreshChalMemo memo q.1 q.2.1 q.2.2.1 q.2.2.2).elim
      (sampler q.1 >>= fun ch =>
        pure (ch, memo ++ [⟨q.1, q.2.1, q.2.2.1, q.2.2.2, ch⟩]))
      (fun r => pure (r, memo))

/-- Definitional unfolding of one `freshChalImpl` step (exposes the memo dispatch). -/
lemma freshChalImpl_run_eq
    (sampler : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i))
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : List (FreshChalMemoEntry StmtIn U δ pSpec)) :
    (freshChalImpl (δ := δ) sampler q).run memo
      = (lookupFreshChalMemo memo q.1 q.2.1 q.2.2.1 q.2.2.2).elim
          (sampler q.1 >>= fun ch =>
            pure (ch, memo ++ [⟨q.1, q.2.1, q.2.2.1, q.2.2.2, ch⟩]))
          (fun r => pure (r, memo)) := rfl

/-- **Per-step memoized coupling**: from any common memo, one `freshChalImpl` step under
two samplers is within the per-round sampler distance — free on a memo hit (both sides
answer deterministically from the same memo), at most `ε_cdc,i` on a fresh key. -/
lemma freshChalImpl_step_tvDist_le
    (sA sB : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i))
    (hclose : ∀ i, tvDist (sA i) (sB i) ≤ (codec.decodingBias i : ℝ))
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : List (FreshChalMemoEntry StmtIn U δ pSpec)) :
    tvDist ((freshChalImpl (δ := δ) sA q).run memo) ((freshChalImpl (δ := δ) sB q).run memo)
      ≤ (codec.decodingBias q.1 : ℝ) := by
  rw [freshChalImpl_run_eq, freshChalImpl_run_eq]
  cases hlook : lookupFreshChalMemo memo q.1 q.2.1 q.2.2.1 q.2.2.2 with
  | none =>
      simp only [Option.elim_none]
      exact le_trans (tvDist_bind_right_le _ _ _) (hclose q.1)
  | some r =>
      simp only [Option.elim_some, tvDist_self]
      exact (codec.decodingBias q.1).coe_nonneg

end MemoImpl

/-! ## The fresh game implementation and its per-step coupling -/

section GameImpl

/-- Classify a `Hyb₂`-world outer-spec query index by its challenge round (`none` for
shared-`oSpec` and auxiliary `(Unit →ₒ U) + unifSpec` sampling queries). -/
def challengeRoundOf
    (t : (oSpec + D2SChallengePlusUnitOracle (U := U)
      (eSpec (U := U) StmtIn pSpec δ)).Domain) :
    Option pSpec.ChallengeIdx :=
  match t with
  | .inr (.inl q) => some q.1
  | _ => none

/-- The full fresh-game implementation over the `Hyb₂` outer spec: shared `oSpec` queries
forwarded to `oImpl`, challenge queries through the lazily-memoized `freshChalImpl`,
auxiliary `𝒰(Σ)`/`unifSpec` sampling realized exactly as in `hybGameEager`. -/
noncomputable def freshGameImpl [SampleableType U]
    (sampler : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i))
    (oImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
      (StateT (List (FreshChalMemoEntry StmtIn U δ pSpec)) ProbComp) :=
  fun t => match t with
  | .inl qo => StateT.lift (oImpl qo)
  | .inr (.inl qe) => freshChalImpl (δ := δ) sampler qe
  | .inr (.inr (.inl qu)) => StateT.lift (d2sUnitSampleImpl (U := U) qu)
  | .inr (.inr (.inr m)) => StateT.lift (liftM (unifSpec.query m) : ProbComp _)

/-- Per-step coupling of the full fresh-game implementations: zero off the challenge
oracle, at most `ε_cdc,i` on a round-`i` challenge query (per `freshChalImpl_step`). -/
lemma freshGameImpl_step_tvDist_le [SampleableType U]
    (sA sB : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i))
    (oImpl : QueryImpl oSpec ProbComp)
    (hclose : ∀ i, tvDist (sA i) (sB i) ≤ (codec.decodingBias i : ℝ))
    (t : (oSpec + D2SChallengePlusUnitOracle (U := U)
      (eSpec (U := U) StmtIn pSpec δ)).Domain)
    (memo : List (FreshChalMemoEntry StmtIn U δ pSpec)) :
    tvDist ((freshGameImpl (δ := δ) sA oImpl t).run memo)
        ((freshGameImpl (δ := δ) sB oImpl t).run memo)
      ≤ (challengeRoundOf (oSpec := oSpec) (δ := δ) t).elim 0
          (fun i => (codec.decodingBias i : ℝ)) := by
  match t with
  | .inl qo => exact le_of_eq (tvDist_self _)
  | .inr (.inl qe) => exact freshChalImpl_step_tvDist_le sA sB hclose qe memo
  | .inr (.inr (.inl qu)) => exact le_of_eq (tvDist_self _)
  | .inr (.inr (.inr m)) => exact le_of_eq (tvDist_self _)

end GameImpl

/-! ## The fresh pivot game on the actual `hybGameEager` skeleton -/

section FreshGame

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The prover-stage pipeline computation of `hybGameEager` at the `Hyb₂` instantiation
(verbatim: `d2fRaw` with `gImplDecodedChallenge`, wrapped in the logging oracle), exposed
as a named computation over the `Hyb₂` outer spec so that the challenge-budget residuals
and the accounting theorem quantify over the *same* term. -/
noncomputable def proverPipeline (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (δ : ℕ)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :=
  (simulateQ loggingOracle
    ((d2fRaw (T_H := T_H) (T_P := T_P)
      (gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      P default).run)).run

/-- The verifier-stage pipeline computation of `hybGameEager` at the `Hyb₂` instantiation
(verbatim, sharing the prover's `tr_i` inner state — `PUnit` for `gImplDecodedChallenge`). -/
noncomputable def verifierPipeline (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (δ : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (messages : pSpec.Messages) (mm : PUnit) :=
  (simulateQ loggingOracle
    ((d2fRaw (T_H := T_H) (T_P := T_P)
      (gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      ((V.duplexSpongeFiatShamir.run
        stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)
      mm).run)).run

/-- **The fresh pivot game** (CO25 Figure 4 lines 2–4 at the `Hyb₂` instantiation, with the
eager challenge table replaced by the lazily-memoized per-round `sampler`): structurally
`hybGameEager (uniform eSpec) gImplDecodedChallenge hyb2Line4TraceEager` with the
one-table sampling step traded for the memo threading (prover memo handed to the verifier
stage, mirroring the one-table consistency of the eager game). At
`sampler := uniformChallengeSampler` this is the lazy view of `Hyb₂`; at
`sampler := decodedChallengeSampler` it is the lazy decoded view of `Hyb12Mid`. -/
noncomputable def hyb2GameFresh [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (sampler : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  (simulateQ (freshGameImpl (δ := δ) sampler oImpl)
      (proverPipeline (oSpec := oSpec) T_H T_P δ P)).run []
    >>= fun x =>
  match x.1.1 with
  | none => pure none
  | some r =>
      (simulateQ (freshGameImpl (δ := δ) sampler oImpl)
          (verifierPipeline (oSpec := oSpec) (StmtOut := StmtOut) (U := U) T_H T_P δ V
            r.1.1.1 r.1.1.2 r.2)).run x.2
        >>= fun y =>
      match y.1.1 with
      | none => pure none
      | some vr =>
          match vr.1.1 with
          | none => pure none
          | some stmtOut => do
              let pLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((hyb2Line4TraceEager (δ := δ)
                    (projectChallengePlusUnitQueryLog (U := U) x.1.2)).run)
              let vLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((hyb2Line4TraceEager (δ := δ)
                    (projectChallengePlusUnitQueryLog (U := U) y.1.2)).run)
              match pLog'?, vLog'? with
              | some pLog', some vLog' =>
                  pure (some ⟨r.1.1.1, stmtOut, r.1.1.2, pLog', vLog'⟩)
              | _, _ => pure none

/-- **The `θ★` pipeline accounting (CO25 Claim 5.22, fresh world — proven)**: two fresh
pivot games whose per-round samplers are within `ε_cdc,i` are within
`θ★ · maxᵢ ε_cdc,i + ∑ᵢ ε_cdc,i = claim5_22Bound`, provided the prover-stage pipeline
makes at most `θ★` challenge queries and the verifier-stage pipeline derives each round at
most once. The prover stage is paid through the single-predicate accumulator at the
sup-cost, the verifier stage through the round-indexed accumulator at one derivation per
round, and the line-4 tail is sampler-free (zero cost). -/
theorem tvDist_hyb2GameFresh_le [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (sA sB : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i))
    (hclose : ∀ i, tvDist (sA i) (sB i) ≤ (codec.decodingBias i : ℝ))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ)
    (hPB : IsQueryBoundP (proverPipeline (oSpec := oSpec) T_H T_P δ P)
      (fun t => (challengeRoundOf (oSpec := oSpec) (δ := δ) t).isSome = true)
      (θStar tₕ tₚ tₚᵢ))
    (hVB : ∀ (stmtIn : StmtIn) (messages : pSpec.Messages) (mm : PUnit)
      (i : pSpec.ChallengeIdx),
      IsQueryBoundP
        (verifierPipeline (oSpec := oSpec) (StmtOut := StmtOut) (U := U) T_H T_P δ V
          stmtIn messages mm)
        (fun t => challengeRoundOf (oSpec := oSpec) (δ := δ) t = some i) 1) :
    tvDist (hyb2GameFresh T_H T_P δ sA oImpl V P) (hyb2GameFresh T_H T_P δ sB oImpl V P)
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ codec.decodingBias := by
  have hεnonneg : ∀ i : pSpec.ChallengeIdx, (0 : ℝ) ≤ (codec.decodingBias i : ℝ) :=
    fun i => (codec.decodingBias i).coe_nonneg
  have hsupnonneg : (0 : ℝ) ≤ ((⨆ i, codec.decodingBias i : ℝ≥0) : ℝ) :=
    NNReal.coe_nonneg _
  have hSumNonneg : (0 : ℝ) ≤ ∑ i : pSpec.ChallengeIdx,
      ((1 : ℕ) : ℝ) * (codec.decodingBias i : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hεnonneg i)
  -- per-step bound in sup (if-) form, for the prover stage
  have hstepP : ∀ (t : (oSpec + D2SChallengePlusUnitOracle (U := U)
        (eSpec (U := U) StmtIn pSpec δ)).Domain)
      (memo : List (FreshChalMemoEntry StmtIn U δ pSpec)),
      tvDist ((freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sA oImpl t).run memo)
          ((freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sB oImpl t).run memo)
        ≤ if (challengeRoundOf (oSpec := oSpec) (δ := δ) t).isSome = true
            then ((⨆ i, codec.decodingBias i : ℝ≥0) : ℝ) else 0 := by
    intro t memo
    refine le_trans (freshGameImpl_step_tvDist_le sA sB oImpl hclose t memo) ?_
    cases ht : challengeRoundOf (oSpec := oSpec) (δ := δ) t with
    | none => simp
    | some i =>
        simp only [Option.elim_some, Option.isSome_some, if_pos]
        exact NNReal.coe_le_coe.mpr
          (le_ciSup (Set.Finite.bddAbove (Set.finite_range _)) i)
  -- per-step bound in class (elim-) form, for the verifier stage
  have hstepV : ∀ (t : (oSpec + D2SChallengePlusUnitOracle (U := U)
        (eSpec (U := U) StmtIn pSpec δ)).Domain)
      (memo : List (FreshChalMemoEntry StmtIn U δ pSpec)),
      tvDist ((freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sA oImpl t).run memo)
          ((freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sB oImpl t).run memo)
        ≤ (challengeRoundOf (oSpec := oSpec) (δ := δ) t).elim 0
            (fun i => (codec.decodingBias i : ℝ)) :=
    fun t memo => freshGameImpl_step_tvDist_le sA sB oImpl hclose t memo
  -- stage 1: the prover pipeline at the θ★ budget and the sup cost
  have hstage1 : tvDist
        ((simulateQ (freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sA oImpl)
          (proverPipeline (oSpec := oSpec) T_H T_P δ P)).run [])
        ((simulateQ (freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sB oImpl)
          (proverPipeline (oSpec := oSpec) T_H T_P δ P)).run [])
      ≤ ((θStar tₕ tₚ tₚᵢ : ℕ) : ℝ) * ((⨆ i, codec.decodingBias i : ℝ≥0) : ℝ) :=
    tvDist_simulateQ_stateT_le_predBudget hsupnonneg hstepP hPB []
  -- stage 2: the verifier pipeline at one derivation per round
  have hstage2 : ∀ (stmtIn : StmtIn) (messages : pSpec.Messages) (mm : PUnit)
      (memo : List (FreshChalMemoEntry StmtIn U δ pSpec)),
      tvDist
          ((simulateQ (freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sA oImpl)
            (verifierPipeline (oSpec := oSpec) (StmtOut := StmtOut) (U := U) T_H T_P δ V
              stmtIn messages mm)).run memo)
          ((simulateQ (freshGameImpl (StmtIn := StmtIn) (U := U) (δ := δ) sB oImpl)
            (verifierPipeline (oSpec := oSpec) (StmtOut := StmtOut) (U := U) T_H T_P δ V
              stmtIn messages mm)).run memo)
        ≤ ∑ i : pSpec.ChallengeIdx, ((1 : ℕ) : ℝ) * (codec.decodingBias i : ℝ) :=
    fun stmtIn messages mm memo =>
      tvDist_simulateQ_stateT_le_classBudget
        (challengeRoundOf (oSpec := oSpec) (δ := δ)) hεnonneg hstepV
        (hVB stmtIn messages mm) memo
  -- assemble the two stages through the actual game skeleton
  unfold hyb2GameFresh
  refine le_trans (tvDist_bind_le_of_stages _ _ _ _ hSumNonneg hstage1 ?_) ?_
  · -- continuation: free on prover abort; verifier stage + sampler-free tail otherwise
    intro x
    rcases hp : x.1.1 with _ | r
    · exact (le_of_eq (tvDist_self _)).trans hSumNonneg
    · refine le_trans
        (tvDist_bind_le_of_stages _ _ _ _ le_rfl
          (hstage2 r.1.1.1 r.1.1.2 r.2 x.2) (fun y => le_of_eq (tvDist_self _)))
        (le_of_eq (add_zero _))
  · -- numeric: `θ★ · sup + ∑ᵢ 1 · εᵢ = claim5_22Bound`
    unfold claim5_22Bound
    refine add_le_add le_rfl (le_of_eq ?_)
    rw [NNReal.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.cast_one, one_mul]

end FreshGame

/-! ## The finest residuals and the proven reduction -/

section Residuals

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Finer residual B1 — **`Hyb₂` eager↔lazy alignment** (`Δ(Hyb₂, hyb2GameFresh 𝒰) = 0`):
the once-sampled uniform `eSpec` table equals its lazily-memoized per-query sampling view.
This is the textbook lazy-sampling equivalence (sound for adversarial repeat keys thanks to
the memo); open content: commuting the table sampling with the `d2fRaw`/logging pipeline. -/
def Hyb2FreshAlignResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb2 T_H T_P δ oImpl V P)
      𝒟[hyb2GameFresh T_H T_P δ (uniformChallengeSampler (pSpec := pSpec)) oImpl V P] = 0

/-- Finer residual B2 — **`Hyb12Mid` decoded-lazy alignment**
(`Δ(Hyb12Mid, hyb2GameFresh (ψ ∘ 𝒰)) = 0`): the `Hyb12Mid` game (eager uniform `gSpec`
table, fiber-resampled answers, `(φ⁻¹, ψ)` line-4 map) equals the fresh pivot at the
decoded sampler. Contains (i) the same eager↔lazy step as B1 for the `gSpec` table and
(ii) the `gSpec → eSpec` re-keying: `gImplEncodedResampled` and the `Hyb₁` line-4 map
consume the encoded answer only through `ψᵢ` and the common `ψ⁻¹`-fiber kernel — per fresh
derivation this is exactly the (proven) coupling shape of
`Hyb12Step.tvDist_gImplEncodedForward_gImplDecodedChallenge_le` with the challenge marginal
fixed; the open content is the game-level lift through the pipeline. -/
def Hyb12MidFreshAlignResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb12Mid T_H T_P δ oImpl V P)
      𝒟[hyb2GameFresh T_H T_P δ (decodedChallengeSampler (U := U) (pSpec := pSpec))
          oImpl V P] = 0

/-- Finer residual B3 — **prover-stage `θ★` challenge budget**: the `d2fRaw`-with-logging
prover pipeline makes at most `θ★ = tₚ` challenge-oracle queries when the malicious prover
respects the `(tₕ, tₚ, tₚᵢ)` flavor budgets (CO25 §5.4: only forward-perm queries trigger
`gᵢ` derivations). F4/M1c genre: per-step dispatcher branch analysis
(`D2sQueryStepGSpecBudgetResidual`) + F3 stack transfer + logging budget transparency. -/
def Hyb12ProverPipelineBudgetResidual
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ) : Prop :=
  ∀ (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ),
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    IsQueryBoundP (proverPipeline (oSpec := oSpec) T_H T_P δ P)
      (fun t => (challengeRoundOf (oSpec := oSpec) (δ := δ) t).isSome = true)
      (θStar tₕ tₚ tₚᵢ)

/-- Finer residual B4 — **verifier-stage once-per-round budget**: the verifier pipeline
(`V.duplexSpongeFiatShamir` through `d2fRaw`) derives each round's challenge at most once
(CO25 Eq. 53's "+ one per round on the verifier side"; the honest verifier absorbs each
message and squeezes each challenge exactly once). -/
def Hyb12VerifierPipelineBudgetResidual
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (messages : pSpec.Messages) (mm : PUnit)
    (i : pSpec.ChallengeIdx),
    IsQueryBoundP
      (verifierPipeline (oSpec := oSpec) (StmtOut := StmtOut) (U := U) T_H T_P δ V
        stmtIn messages mm)
      (fun t => challengeRoundOf (oSpec := oSpec) (δ := δ) t = some i) 1

/-- **The proven reduction (CO25 Claim 5.22 bias accounting)**: the two eager↔lazy
alignment residuals and the two pipeline budget residuals assemble — through the proven
`θ★` fresh-world accounting `tvDist_hyb2GameFresh_le` and the TV triangle inequality —
into the full `Hyb12Step.Hyb12BiasAccountingResidual`. -/
theorem hyb12BiasAccounting_of_freshPipeline [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hB2 : Hyb12MidFreshAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hB1 : Hyb2FreshAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hB3 : Hyb12ProverPipelineBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) T_H T_P δ)
    (hB4 : Hyb12VerifierPipelineBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12BiasAccountingResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  -- the proven fresh-world core at claim5_22Bound
  have hcore : SPMF.tvDist
      𝒟[hyb2GameFresh T_H T_P δ (decodedChallengeSampler (U := U) (pSpec := pSpec))
          oImpl V P]
      𝒟[hyb2GameFresh T_H T_P δ (uniformChallengeSampler (pSpec := pSpec)) oImpl V P]
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ codec.decodingBias :=
    tvDist_hyb2GameFresh_le T_H T_P δ _ _
      (fun i => tvDist_decodedChallengeSampler_uniform_le (U := U) i) oImpl V P tₕ tₚ tₚᵢ
      (hB3 P tₕ tₚ tₚᵢ hHash hPerm hPermInv)
      (fun stmtIn messages mm i => hB4 V stmtIn messages mm i)
  -- alignment legs
  have hmid := hB2 V P
  have he := hB1 V P
  -- triangle: Hyb12Mid → freshMid → freshE → Hyb₂
  have htri₁ := SPMF.tvDist_triangle (Hyb12Mid T_H T_P δ oImpl V P)
    𝒟[hyb2GameFresh T_H T_P δ (decodedChallengeSampler (U := U) (pSpec := pSpec))
        oImpl V P]
    (Hyb2 T_H T_P δ oImpl V P)
  have htri₂ := SPMF.tvDist_triangle
    𝒟[hyb2GameFresh T_H T_P δ (decodedChallengeSampler (U := U) (pSpec := pSpec))
        oImpl V P]
    𝒟[hyb2GameFresh T_H T_P δ (uniformChallengeSampler (pSpec := pSpec)) oImpl V P]
    (Hyb2 T_H T_P δ oImpl V P)
  have hcomm := SPMF.tvDist_comm
    𝒟[hyb2GameFresh T_H T_P δ (uniformChallengeSampler (pSpec := pSpec)) oImpl V P]
    (Hyb2 T_H T_P δ oImpl V P)
  linarith

end Residuals

end DuplexSpongeFS.Hyb12Accounting

#print axioms DuplexSpongeFS.Hyb12Accounting.tvDist_bind_le_of_stages
#print axioms DuplexSpongeFS.Hyb12Accounting.tvDist_simulateQ_stateT_le_predBudget
#print axioms DuplexSpongeFS.Hyb12Accounting.tvDist_simulateQ_stateT_le_classBudget
#print axioms DuplexSpongeFS.Hyb12Accounting.spmf_liftM_bind_pure
#print axioms DuplexSpongeFS.Hyb12Accounting.tvDist_decodedChallengeSampler_uniform_le
#print axioms DuplexSpongeFS.Hyb12Accounting.freshChalImpl_run_eq
#print axioms DuplexSpongeFS.Hyb12Accounting.freshChalImpl_step_tvDist_le
#print axioms DuplexSpongeFS.Hyb12Accounting.freshGameImpl_step_tvDist_le
#print axioms DuplexSpongeFS.Hyb12Accounting.tvDist_hyb2GameFresh_le
#print axioms DuplexSpongeFS.Hyb12Accounting.hyb12BiasAccounting_of_freshPipeline

end
