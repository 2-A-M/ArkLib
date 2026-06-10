/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb34Step

/-!
# CO25 Claim 5.24, Eq. 55 legs — the abort-truncation reduction

This module attacks the two legs of the symmetric Eq. 55 split
(`Hyb34Step.Hyb34DivergenceResidual` and `Hyb34Step.Hyb34CollapseResidual`) through one
structural observation: **`Hyb3Strict` is an abort-truncation of both of its neighbours**.
The strict (hit-only) verifier bridge agrees with the real `Hyb₃` bridge on every `tr_i`
memo hit and *aborts* on every miss (`d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit` /
`..._run_miss`), and on the hit path it serves exactly the table values the `Hyb₄` basic-FS
verifier reads (`d2sCodecBridgeImplMemoEagerHitOnly_coherent_serve`). So in *both* legs the
strict game's successful outputs are a pointwise sub-distribution of the neighbour's, and
the entire TV distance is concentrated on the abort output.

## Proven here (no `sorry`, axiom-clean)

- **The abort-truncation TV identity** (`pmf_tvDist_eq_of_le_off_sink`,
  `spmf_tvDist_eq_abortGap`): if `Q ≤ P` everywhere except at a single sink point, then
  `tvDist(P, Q)` **equals** the sink-mass gap `Q(x₀) − P(x₀)`. For an `Option`-valued game
  whose successes are dominated and whose failure mass is dominated, the TV distance *is*
  the abort-output gap — no coupling argument, no triangle slack.
- **Domination bind-monotonicity bricks** (`probOutput_bind_mono_right`,
  `probFailure_bind_mono_right`, `probOutput_bind_mono_left_event`,
  `probFailure_bind_mono_left_event`): pointwise output-domination is preserved through
  the Figure-4 game skeleton — shared stages transport it on the right, dominated stages
  transport it on the left provided the continuation maps the bad (aborted) outcomes to
  abort. These are the generic carriers that reduce whole-game domination to
  per-stage domination.
- **Bridge-level domination seeds** (`probOutput_some_hitOnly_run_le_eager`,
  `probFailure_hitOnly_run_le_eager`): against any fixed eager table, the strict bridge's
  run is success-pointwise dominated by the real eager bridge's run, with dominated failure
  mass — the per-query content of the εA-leg domination, closed from the proven run-shape
  lemmas of `VerifierReplay`.
- **The leg reductions** (`hyb34Divergence_of_subRun_gap`, `hyb34Collapse_of_subRun_gap`,
  `hyb34Step_of_legs`, `keyLemmaEager_of_legs`): the four finer residuals below imply the
  two Eq. 55 legs, hence the full `Hyb34StepResidual`, hence (with Claims 5.21–5.23) the
  full eager key lemma. The TV-coupling obligations of the two legs are **replaced** by
  (i) deterministic-class pointwise domination claims (no probability bounds at all) and
  (ii) two scalar abort-gap masses (the genuine CO25 `E_𝒱` content).
- `strictAbortGap_nonneg_of_subRun`: under the domination, the εA abort gap is exactly the
  leg's TV distance, in particular nonnegative — the gap residual demands a bound on a
  genuinely nonnegative quantity (satisfiability guard).

## Open core (named `*Residual : Prop`, NOT proven)

- `Hyb34StrictSubRunResidual` (εA, structural): every successful `Hyb3Strict` output is at
  most as likely as in `Hyb₃`, and the strict game fails (in the SPMF sense) at most as
  often. Same deterministic bisimulation class as the proven step-C lift
  (`Hyb23Delta0Lift`), but in *inequality* form — strictly weaker than a coupling: per
  query the two bridges are **equal** on hits and the strict side is `pure none` on misses
  (`probOutput_some_hitOnly_run_le_eager` is the per-query seed).
- `Hyb34StrictAbortGapResidual` (εA, mass): the strict game's *extra* abort-output mass
  over `Hyb₃` is at most `claim5_24Bound/2`. By the truncation identity this **is** the εA
  leg; it is exactly the probability that the `Hyb₃` verifier's `D2SQuery` run leaves the
  committed replay path (CO25's `E_𝒱`), to be bounded by the §5.6 trace analysis
  (`BirthdayBound` accumulator + honest bad events + M2).
- `Hyb34CollapseSubRunResidual` (εB, structural): every successful `Hyb3Strict` output is
  at most as likely as in `Hyb₄` against the simulated prover — the game-skeleton
  threading of the proven per-query collapse
  (`d2sCodecBridgeImplMemoEagerHitOnly_coherent_serve` + `memoCoherentTableEager_keystone`
  + the ψ-roundtrip): on the hit path the strict verifier's re-derived transcript
  coincides pointwise with the `Hyb₄` verifier's, and off the hit path the strict game
  contributes nothing to successes.
- `Hyb34CollapseAbortGapResidual` (εB, mass): the strict game's extra abort-output mass
  over `Hyb₄` is at most `claim5_24Bound/2` — the same `E_𝒱` event measured in the
  `Hyb₄`-side experiment.

Neither leg keeps a TV-shaped obligation: `hyb34Step_of_legs` is the door, and the four
residuals are each strictly finer than the legs they replace.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb34Legs

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open VerifierReplay Hyb34Step
open scoped NNReal ENNReal

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## The abort-truncation TV identity

If `Q ≤ P` at every point except a designated sink `x₀`, then all the deficit mass of `Q`
off the sink reappears *at* the sink, and the total variation distance collapses to the
single-point gap `Q x₀ − P x₀`. This is the exact shape of both Eq. 55 legs: the strict
hybrid is a truncation of its neighbour, with all diverted mass landing on the abort
output. -/

section AbortTruncation

universe u

/-- Split an `ℝ≥0∞` sum at a designated sink point (instance-free: complement-subtype
form, avoiding the `ite`/`Decidable` route). -/
private lemma tsum_split_sink {X : Type u} (f : X → ℝ≥0∞) (x₀ : X) :
    ∑' x, f x = f x₀ + ∑' x : ({x₀}ᶜ : Set X), f x := by
  calc ∑' x, f x
      = (∑' x : ({x₀} : Set X), f x) + ∑' x : (({x₀} : Set X)ᶜ : Set X), f x :=
        (ENNReal.summable.tsum_add_tsum_compl ENNReal.summable).symm
    _ = f x₀ + ∑' x : ({x₀}ᶜ : Set X), f x := by rw [tsum_singleton]

/-- Off-sink domination forces sink domination the other way: the sink absorbs the
deficit. -/
lemma pmf_apply_le_at_sink {X : Type u} (P Q : PMF X) (x₀ : X)
    (h : ∀ x, x ≠ x₀ → Q x ≤ P x) : P x₀ ≤ Q x₀ := by
  have hPmass : P x₀ + (∑' x : ({x₀}ᶜ : Set X), P x) = 1 :=
    (tsum_split_sink (fun x => P x) x₀).symm.trans P.tsum_coe
  have hQmass : Q x₀ + (∑' x : ({x₀}ᶜ : Set X), Q x) = 1 :=
    (tsum_split_sink (fun x => Q x) x₀).symm.trans Q.tsum_coe
  have hSQ_le_SP : (∑' x : ({x₀}ᶜ : Set X), Q x) ≤ ∑' x : ({x₀}ᶜ : Set X), P x :=
    ENNReal.tsum_le_tsum fun x => h x (Set.mem_compl_singleton_iff.mp x.2)
  have hSQ_ne_top : (∑' x : ({x₀}ᶜ : Set X), Q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self (le_of_eq hQmass))
  have hle : P x₀ + (∑' x : ({x₀}ᶜ : Set X), Q x)
      ≤ Q x₀ + (∑' x : ({x₀}ᶜ : Set X), Q x) := by
    calc P x₀ + (∑' x : ({x₀}ᶜ : Set X), Q x)
        ≤ P x₀ + (∑' x : ({x₀}ᶜ : Set X), P x) := add_le_add le_rfl hSQ_le_SP
      _ = 1 := hPmass
      _ = Q x₀ + (∑' x : ({x₀}ᶜ : Set X), Q x) := hQmass.symm
  exact ENNReal.le_of_add_le_add_right hSQ_ne_top hle

/-- **Abort-truncation, `ℝ≥0∞` form**: off-sink domination collapses the extended TV
distance to the sink gap, *exactly*. -/
theorem pmf_etvDist_eq_of_le_off_sink {X : Type u} (P Q : PMF X) (x₀ : X)
    (h : ∀ x, x ≠ x₀ → Q x ≤ P x) :
    P.etvDist Q = Q x₀ - P x₀ := by
  have hsink : P x₀ ≤ Q x₀ := pmf_apply_le_at_sink P Q x₀ h
  have hPmass : P x₀ + (∑' x : ({x₀}ᶜ : Set X), P x) = 1 :=
    (tsum_split_sink (fun x => P x) x₀).symm.trans P.tsum_coe
  have hQmass : Q x₀ + (∑' x : ({x₀}ᶜ : Set X), Q x) = 1 :=
    (tsum_split_sink (fun x => Q x) x₀).symm.trans Q.tsum_coe
  have hSQ_ne_top : (∑' x : ({x₀}ᶜ : Set X), Q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self (le_of_eq hQmass))
  -- the head term is the sink gap
  have hhead : ENNReal.absDiff (P x₀) (Q x₀) = Q x₀ - P x₀ := by
    unfold ENNReal.absDiff
    rw [tsub_eq_zero_of_le hsink, zero_add]
  -- the tail sums to the complementary-mass gap
  have htailQ : (∑' x : ({x₀}ᶜ : Set X), ENNReal.absDiff (P x) (Q x))
      + (∑' x : ({x₀}ᶜ : Set X), Q x) = ∑' x : ({x₀}ᶜ : Set X), P x := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    have hx : (x : X) ≠ x₀ := Set.mem_compl_singleton_iff.mp x.2
    unfold ENNReal.absDiff
    rw [tsub_eq_zero_of_le (h x hx), add_zero, tsub_add_cancel_of_le (h x hx)]
  have htail : (∑' x : ({x₀}ᶜ : Set X), ENNReal.absDiff (P x) (Q x))
      = (∑' x : ({x₀}ᶜ : Set X), P x) - (∑' x : ({x₀}ᶜ : Set X), Q x) :=
    ENNReal.eq_sub_of_add_eq hSQ_ne_top htailQ
  -- complementary masses, and the complementary gap is again the sink gap
  have hSPeq : (∑' x : ({x₀}ᶜ : Set X), P x) = 1 - P x₀ :=
    ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top P x₀) (by rw [add_comm]; exact hPmass)
  have hSQeq : (∑' x : ({x₀}ᶜ : Set X), Q x) = 1 - Q x₀ :=
    ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top Q x₀) (by rw [add_comm]; exact hQmass)
  have hQ1 : Q x₀ ≤ 1 := PMF.coe_le_one Q x₀
  have hgap : (∑' x : ({x₀}ᶜ : Set X), P x) - (∑' x : ({x₀}ᶜ : Set X), Q x)
      = Q x₀ - P x₀ := by
    rw [hSPeq, hSQeq]
    have key : ((Q x₀ - P x₀) + (1 - Q x₀)) + P x₀ = 1 := by
      calc ((Q x₀ - P x₀) + (1 - Q x₀)) + P x₀
          = ((Q x₀ - P x₀) + P x₀) + (1 - Q x₀) := by ring
        _ = Q x₀ + (1 - Q x₀) := by rw [tsub_add_cancel_of_le hsink]
        _ = 1 := by rw [add_comm, tsub_add_cancel_of_le hQ1]
    have h1P : (1 : ℝ≥0∞) - P x₀ = (Q x₀ - P x₀) + (1 - Q x₀) :=
      (ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top P x₀) key).symm
    exact ENNReal.sub_eq_of_eq_add
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) h1P
  -- assemble
  have hfinal : (∑' x, ENNReal.absDiff (P x) (Q x)) = (Q x₀ - P x₀) + (Q x₀ - P x₀) := by
    calc ∑' x, ENNReal.absDiff (P x) (Q x)
        = ENNReal.absDiff (P x₀) (Q x₀)
            + ∑' x : ({x₀}ᶜ : Set X), ENNReal.absDiff (P x) (Q x) :=
          tsum_split_sink (fun x => ENNReal.absDiff (P x) (Q x)) x₀
      _ = (Q x₀ - P x₀) + (Q x₀ - P x₀) := by rw [hhead, htail, hgap]
  rw [PMF.etvDist, hfinal, ← two_mul, mul_comm, mul_div_assoc,
    ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-- **Abort-truncation, real form**: off-sink domination collapses the TV distance to the
real-valued sink gap. -/
theorem pmf_tvDist_eq_of_le_off_sink {X : Type u} (P Q : PMF X) (x₀ : X)
    (h : ∀ x, x ≠ x₀ → Q x ≤ P x) :
    P.tvDist Q = (Q x₀).toReal - (P x₀).toReal := by
  rw [PMF.tvDist, pmf_etvDist_eq_of_le_off_sink P Q x₀ h,
    ENNReal.toReal_sub_of_le (pmf_apply_le_at_sink P Q x₀ h) (PMF.apply_ne_top Q x₀)]

/-- **Abort-truncation on the `Option`-game surface**: if every *successful* output of `q`
is at most as likely as under `p`, and `q`'s missing (SPMF-failure) mass is at most `p`'s,
then the TV distance between the two games **is** the abort-output gap. The sink is the
in-game abort `some none`; the two hypotheses cover the remaining points `some (some o)`
and the SPMF failure layer `none`. -/
theorem spmf_tvDist_eq_abortGap {γ : Type u} (p q : SPMF (Option γ))
    (hsome : ∀ o : γ, q (some o) ≤ p (some o))
    (hfail : q.toPMF none ≤ p.toPMF none) :
    SPMF.tvDist p q
      = (q (none : Option γ)).toReal - (p (none : Option γ)).toReal := by
  have h : ∀ x, x ≠ (some (none : Option γ)) → q.toPMF x ≤ p.toPMF x := by
    intro x hx
    match x with
    | none => exact hfail
    | some none => exact absurd rfl hx
    | some (some o) => exact hsome o
  exact pmf_tvDist_eq_of_le_off_sink p.toPMF q.toPMF (some none) h

/-- The abort gap is the TV distance itself, hence nonnegative: the truncated game has *at
least* as much abort-output mass as the original. -/
theorem spmf_abortGap_nonneg {γ : Type u} (p q : SPMF (Option γ))
    (hsome : ∀ o : γ, q (some o) ≤ p (some o))
    (hfail : q.toPMF none ≤ p.toPMF none) :
    0 ≤ (q (none : Option γ)).toReal - (p (none : Option γ)).toReal := by
  rw [← spmf_tvDist_eq_abortGap p q hsome hfail]
  exact SPMF.tvDist_nonneg p q

end AbortTruncation

/-! ## Domination bind-monotonicity bricks

Pointwise output-domination is compositional through the monadic game skeleton: shared
stages transport it on the right (`*_mono_right`), and a dominated stage transports it on
the left provided the shared continuation sends every bad (aborted) stage outcome to an
output disjoint from the target (`*_mono_left_event`). These reduce whole-game domination
claims to per-stage domination claims. -/

section DominationBricks

universe u v

variable {m : Type u → Type v} [Monad m] [HasEvalSPMF m] {α β : Type u}

/-- Pointwise output-domination of continuations transports through a shared first
stage. -/
lemma probOutput_bind_mono_right (a : m α) (k₁ k₂ : α → m β) (y : β)
    (h : ∀ x, Pr[= y | k₂ x] ≤ Pr[= y | k₁ x]) :
    Pr[= y | a >>= k₂] ≤ Pr[= y | a >>= k₁] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)

/-- Pointwise failure-domination of continuations transports through a shared first
stage. -/
lemma probFailure_bind_mono_right (a : m α) (k₁ k₂ : α → m β)
    (h : ∀ x, Pr[⊥ | k₂ x] ≤ Pr[⊥ | k₁ x]) :
    Pr[⊥ | a >>= k₂] ≤ Pr[⊥ | a >>= k₁] := by
  rw [probFailure_bind_eq_add_tsum, probFailure_bind_eq_add_tsum]
  exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x))

/-- Output-domination of a first stage on its *good* outcomes transports through a shared
continuation, provided the continuation gives the target output zero mass from every bad
outcome (the Figure-4 skeleton sends every aborted stage to `pure none`). -/
lemma probOutput_bind_mono_left_event (a₁ a₂ : m α) (k : α → m β)
    (good : α → Prop) (y : β)
    (hdom : ∀ x, good x → Pr[= x | a₂] ≤ Pr[= x | a₁])
    (hbad : ∀ x, ¬ good x → Pr[= y | k x] = 0) :
    Pr[= y | a₂ >>= k] ≤ Pr[= y | a₁ >>= k] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : good x
  · exact mul_le_mul' (hdom x hx) le_rfl
  · simp [hbad x hx]

/-- Failure-domination analogue of `probOutput_bind_mono_left_event`: the dominated stage's
own failure mass is dominated, and the continuation never fails from a bad outcome. -/
lemma probFailure_bind_mono_left_event (a₁ a₂ : m α) (k : α → m β)
    (good : α → Prop)
    (hdom : ∀ x, good x → Pr[= x | a₂] ≤ Pr[= x | a₁])
    (hfail : Pr[⊥ | a₂] ≤ Pr[⊥ | a₁])
    (hbad : ∀ x, ¬ good x → Pr[⊥ | k x] = 0) :
    Pr[⊥ | a₂ >>= k] ≤ Pr[⊥ | a₁ >>= k] := by
  rw [probFailure_bind_eq_add_tsum, probFailure_bind_eq_add_tsum]
  refine add_le_add hfail (ENNReal.tsum_le_tsum fun x => ?_)
  by_cases hx : good x
  · exact mul_le_mul' (hdom x hx) le_rfl
  · simp [hbad x hx]

end DominationBricks

/-! ## DSFS context -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-! ## Bridge-level domination seeds (εA per-query content, proven)

Against any fixed eager table, the strict (hit-only) bridge's run is success-pointwise
dominated by the real eager bridge's run: on a `tr_i` memo hit the two runs are **equal**
(`d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit`), and on a miss the strict run is
`pure none` — contributing nothing to successes and nothing to failure. These are the
per-query seeds of `Hyb34StrictSubRunResidual`. -/

section BridgeSeeds

-- `Inhabited U` gives `((Unit →ₒ U) + unifSpec).Inhabited`, hence the uniform `evalDist`
-- semantics on the table-instantiated bridge runs (`HasEvalPMF (OracleComp _)`).
variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt] [Inhabited U]

/-- Per-query success domination: every successful outcome of the table-instantiated
strict bridge run is at most as likely as under the real eager bridge run. -/
theorem probOutput_some_hitOnly_run_le_eager
    (c : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (y : Vector U (challengeSize (pSpec := pSpec) gq.1)
      × D2SAlgoMemo StmtIn U δ Salt pSpec) :
    Pr[= some y | simulateQ (fsTableAuxImplEager (U := U) c)
        (((d2sCodecBridgeImplMemoEagerHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run)]
      ≤ Pr[= some y | simulateQ (fsTableAuxImplEager (U := U) c)
        (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run)] := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r₀ =>
      rw [d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit gq memo r₀ hl]
  | none =>
      rw [d2sCodecBridgeImplMemoEagerHitOnly_run_miss gq memo hl, simulateQ_pure]
      refine le_trans (le_of_eq (probOutput_eq_zero_of_not_mem_support ?_)) (zero_le _)
      simp

/-- Per-query failure domination: the strict bridge run never fails on a miss (it is
`pure none`), and equals the eager run on a hit. -/
theorem probFailure_hitOnly_run_le_eager
    (c : OracleFamily (fsChallengeOracle StmtIn pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    Pr[⊥ | simulateQ (fsTableAuxImplEager (U := U) c)
        (((d2sCodecBridgeImplMemoEagerHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run)]
      ≤ Pr[⊥ | simulateQ (fsTableAuxImplEager (U := U) c)
        (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run)] := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r₀ =>
      rw [d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit gq memo r₀ hl]
  | none =>
      rw [d2sCodecBridgeImplMemoEagerHitOnly_run_miss gq memo hl, simulateQ_pure]
      simp

end BridgeSeeds

/-! ## The four finer residuals (εA/εB, structural + mass) -/

section LegResiduals

/-- **εA structural core** (`Hyb3Strict` is a sub-run of `Hyb₃`): every successful output
of the strict game is at most as likely as in `Hyb₃`, and the strict game's SPMF-failure
mass is dominated. Deterministic bisimulation class (the per-query seeds
`probOutput_some_hitOnly_run_le_eager` / `probFailure_hitOnly_run_le_eager` are proven
above; open is the d2fRaw game-skeleton threading) — note this is an *inequality* claim,
strictly weaker than the equality-relation coupling of the proven step-C lift. -/
def Hyb34StrictSubRunResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    (∀ o : StmtIn × StmtOut × pSpec.Messages
        × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
        × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec),
      (Hyb3Strict T_H T_P δ Salt oImpl V P) (some o)
        ≤ (Hyb3 T_H T_P δ Salt oImpl V P) (some o))
    ∧ (Hyb3Strict T_H T_P δ Salt oImpl V P).toPMF none
        ≤ (Hyb3 T_H T_P δ Salt oImpl V P).toPMF none

/-- **εA mass core** (the genuine CO25 `E_𝒱` content of the divergence leg): the strict
game's *extra* abort-output mass over `Hyb₃` is at most half the Claim 5.24 budget. By the
abort-truncation identity this gap **is** `Δ(Hyb₃, Hyb3Strict)` (given the sub-run
residual); it is exactly the probability that the `Hyb₃` verifier's `D2SQuery` run leaves
the committed replay path. -/
def Hyb34StrictAbortGapResidual [SampleableType U]
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
    ((Hyb3Strict T_H T_P δ Salt oImpl V P) none).toReal
        - ((Hyb3 T_H T_P δ Salt oImpl V P) none).toReal
      ≤ hyb34SplitBudget U tₕ tₚ tₚᵢ L

/-- **εB structural core** (`Hyb3Strict` is a sub-run of `Hyb₄`): every successful output
of the strict game is at most as likely as in `Hyb₄` against the simulated prover. This is
the game-skeleton threading of the proven hit-path collapse: on the hit path the strict
verifier serves exactly the table values the `Hyb₄` basic-FS verifier reads
(`d2sCodecBridgeImplMemoEagerHitOnly_coherent_serve` + `memoCoherentTableEager_keystone` +
the ψ-roundtrip), and off the hit path the strict game aborts, contributing nothing to
successes. -/
def Hyb34CollapseSubRunResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    (∀ o : StmtIn × StmtOut × pSpec.Messages
        × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
        × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec),
      (Hyb3Strict T_H T_P δ Salt oImpl V P) (some o)
        ≤ (Hyb4 oImpl V
            (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
          (some o))
    ∧ (Hyb3Strict T_H T_P δ Salt oImpl V P).toPMF none
        ≤ (Hyb4 oImpl V
            (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P)).toPMF
          none

/-- **εB mass core**: the strict game's extra abort-output mass over `Hyb₄` is at most
half the Claim 5.24 budget — the same `E_𝒱` event, measured in the `Hyb₄`-side
experiment. -/
def Hyb34CollapseAbortGapResidual [SampleableType U]
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
    ((Hyb3Strict T_H T_P δ Salt oImpl V P) none).toReal
        - ((Hyb4 oImpl V
            (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
          none).toReal
      ≤ hyb34SplitBudget U tₕ tₚ tₚᵢ L

end LegResiduals

/-! ## The leg reductions (proven) -/

section LegReductions

/-- **εA leg from the finer residuals**: sub-run domination + the abort-gap mass bound
imply `Hyb34DivergenceResidual`, via the abort-truncation identity — the TV distance *is*
the gap, so the budget transfers with zero slack. -/
theorem hyb34Divergence_of_subRun_gap [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hsub : Hyb34StrictSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hgap : Hyb34StrictAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  rw [spmf_tvDist_eq_abortGap (Hyb3 T_H T_P δ Salt oImpl V P)
    (Hyb3Strict T_H T_P δ Salt oImpl V P) (hsub V P).1 (hsub V P).2]
  exact hgap V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv

/-- **εB leg from the finer residuals**: sub-run domination + the abort-gap mass bound
imply `Hyb34CollapseResidual`, via the abort-truncation identity (with the TV distance
flipped onto the dominating `Hyb₄` side). -/
theorem hyb34Collapse_of_subRun_gap [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hsub : Hyb34CollapseSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hgap : Hyb34CollapseAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  rw [SPMF.tvDist_comm,
    spmf_tvDist_eq_abortGap
      (Hyb4 oImpl V
        (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
      (Hyb3Strict T_H T_P δ Salt oImpl V P) (hsub V P).1 (hsub V P).2]
  exact hgap V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv

/-- Satisfiability guard for the εA gap: under the sub-run domination, the abort gap is
exactly the leg's TV distance, in particular nonnegative — the mass residual demands a
bound on a genuinely nonnegative quantity. -/
theorem strictAbortGap_nonneg_of_subRun [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hsub : Hyb34StrictSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    0 ≤ ((Hyb3Strict T_H T_P δ Salt oImpl V P) none).toReal
        - ((Hyb3 T_H T_P δ Salt oImpl V P) none).toReal :=
  spmf_abortGap_nonneg (Hyb3 T_H T_P δ Salt oImpl V P)
    (Hyb3Strict T_H T_P δ Salt oImpl V P) (hsub V P).1 (hsub V P).2

/-- **CO25 Claim 5.24 from the four finer residuals**: both legs' sub-run dominations and
abort-gap masses imply the full `Hyb34StepResidual` (via the symmetric Eq. 55 split of
`Hyb34Step`). No TV-shaped obligation remains. -/
theorem hyb34Step_of_legs [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hsubA : Hyb34StrictSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hgapA : Hyb34StrictAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hsubB : Hyb34CollapseSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hgapB : Hyb34CollapseAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl :=
  hyb34Step_of_divergence_collapse T_H T_P δ Salt oImpl
    (hyb34Divergence_of_subRun_gap T_H T_P δ Salt oImpl hsubA hgapA)
    (hyb34Collapse_of_subRun_gap T_H T_P δ Salt oImpl hsubB hgapB)

/-- **The eager key lemma from the legs**: Claims 5.21–5.23 plus the four finer Claim 5.24
residuals imply the full eager key lemma. -/
theorem keyLemmaEager_of_legs
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
    (hsubA : Hyb34StrictSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hgapA : Hyb34StrictAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hsubB : Hyb34CollapseSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hgapB : Hyb34CollapseAbortGapResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  keyLemmaEager_of_steps_divergenceCollapse T_H T_P δ Salt oImpl h01 h12 h23
    (hyb34Divergence_of_subRun_gap T_H T_P δ Salt oImpl hsubA hgapA)
    (hyb34Collapse_of_subRun_gap T_H T_P δ Salt oImpl hsubB hgapB)

end LegReductions

/-! ## Stage threading: whole-game domination from fixed-table verifier-stage domination

The εA sub-run residual quantifies over the whole `Hyb₃`/`Hyb3Strict` games. The two games
share the table sample, the prover stage, and every continuation — they differ **only** in
the verifier stage's `gᵢ` realization. The bind-monotonicity bricks therefore reduce the
whole-game domination to domination of the verifier stage at a *fixed* table carrier and
shared memo (`splitVerifierStage`), which is exactly the granularity at which the per-query
seeds (`probOutput_some_hitOnly_run_le_eager`) and the step-C-class d2fRaw induction
operate. -/

section StageThreading

-- The whole-game/stage defeq alignments below walk the full Figure-4 pipeline term.
set_option maxHeartbeats 1600000

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The verifier stage of the split Figure-4 skeleton (`hybGameEagerSplit` lines 3) at a
fixed challenge-oracle carrier `c` and shared `tr_i` memo: the `D2SQuery` run of the DSFS
verifier through the per-hybrid `gᵢ` realization, logged and pushed into `ProbComp`. -/
noncomputable def splitVerifierStage [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M] (δ : ℕ)
    (Dχ : OracleDistribution challengeSpec)
    (gImplV : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (c : Dχ.Carrier) (stmtIn : StmtIn) (messages : pSpec.Messages) (memo : M) :
    ProbComp ((Option ((Option StmtOut
        × D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U)) × M))
      × QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :=
  let coins : QueryImpl unifSpec ProbComp := fun m => (liftM (unifSpec.query m) : ProbComp _)
  let impl : QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) ProbComp :=
    oImpl + (Dχ.toImpl c + (d2sUnitSampleImpl (U := U) + coins))
  simulateQ impl
    ((simulateQ loggingOracle
      ((d2fRaw (T_H := T_H) (T_P := T_P) gImplV
        ((V.duplexSpongeFiatShamir.run
          stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)
        memo).run)).run)

/-- **Whole-game success domination from stage domination**: if the `gV₂` verifier stage
is success-pointwise dominated by the `gV₁` stage at every fixed carrier/statement/memo,
then every successful output of the `gV₂` split game is dominated by the `gV₁` game.
The shared sample/prover/line-4 stages transport the domination via the bind-mono bricks;
aborted verifier stages are sent to `pure none` by the skeleton, so they never contribute
to a success. -/
theorem hybGameEagerSplit_probOutput_some_mono [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M] (δ : ℕ)
    (Dχ : OracleDistribution challengeSpec)
    (gImplP gV₁ gV₂ : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (hstage : ∀ (c : Dχ.Carrier) (stmtIn : StmtIn) (messages : pSpec.Messages) (memo : M)
      (z : (Option ((Option StmtOut
          × D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U)) × M))
        × QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)),
      z.1.isSome = true →
      Pr[= z | splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₂ oImpl V
          c stmtIn messages memo]
        ≤ Pr[= z | splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₁ oImpl V
          c stmtIn messages memo])
    (o : StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    Pr[= some o | hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ Dχ gImplP gV₂ lineFour
        oImpl V P]
      ≤ Pr[= some o | hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ Dχ gImplP gV₁ lineFour
        oImpl V P] := by
  unfold hybGameEagerSplit
  refine probOutput_bind_mono_right _ _ _ _ fun c => ?_
  dsimp only
  refine probOutput_bind_mono_right _ _ _ _ fun pr => ?_
  obtain ⟨pRes?, pLog⟩ := pr
  rcases pRes? with _ | ⟨⟨⟨stmtIn, messages⟩, qst⟩, memo⟩
  · exact le_of_eq rfl
  · dsimp only
    refine probOutput_bind_mono_left_event
      (splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₁ oImpl V c stmtIn messages memo)
      (splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₂ oImpl V c stmtIn messages memo)
      _ (fun z => z.1.isSome = true) _
      (hstage c stmtIn messages memo) ?_
    intro z hz
    obtain ⟨vRes?, vLog⟩ := z
    rcases vRes? with _ | w
    · dsimp only
      exact probOutput_eq_zero_of_not_mem_support (by simp)
    · exact absurd rfl hz

/-- **Whole-game failure domination from stage domination**: the SPMF-failure analogue —
the strict stage's failure mass is dominated, and aborted stages never fail downstream
(`pure none`). -/
theorem hybGameEagerSplit_probFailure_mono [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M] (δ : ℕ)
    (Dχ : OracleDistribution challengeSpec)
    (gImplP gV₁ gV₂ : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (hstage : ∀ (c : Dχ.Carrier) (stmtIn : StmtIn) (messages : pSpec.Messages) (memo : M)
      (z : (Option ((Option StmtOut
          × D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U)) × M))
        × QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)),
      z.1.isSome = true →
      Pr[= z | splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₂ oImpl V
          c stmtIn messages memo]
        ≤ Pr[= z | splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₁ oImpl V
          c stmtIn messages memo])
    (hstageFail : ∀ (c : Dχ.Carrier) (stmtIn : StmtIn) (messages : pSpec.Messages)
      (memo : M),
      Pr[⊥ | splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₂ oImpl V
          c stmtIn messages memo]
        ≤ Pr[⊥ | splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₁ oImpl V
          c stmtIn messages memo]) :
    Pr[⊥ | hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ Dχ gImplP gV₂ lineFour
        oImpl V P]
      ≤ Pr[⊥ | hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ Dχ gImplP gV₁ lineFour
        oImpl V P] := by
  unfold hybGameEagerSplit
  refine probFailure_bind_mono_right _ _ _ fun c => ?_
  dsimp only
  refine probFailure_bind_mono_right _ _ _ fun pr => ?_
  obtain ⟨pRes?, pLog⟩ := pr
  rcases pRes? with _ | ⟨⟨⟨stmtIn, messages⟩, qst⟩, memo⟩
  · exact le_of_eq rfl
  · dsimp only
    refine probFailure_bind_mono_left_event
      (splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₁ oImpl V c stmtIn messages memo)
      (splitVerifierStage (T_H := T_H) (T_P := T_P) δ Dχ gV₂ oImpl V c stmtIn messages memo)
      _ (fun z => z.1.isSome = true)
      (hstage c stmtIn messages memo)
      (hstageFail c stmtIn messages memo) ?_
    intro z hz
    obtain ⟨vRes?, vLog⟩ := z
    rcases vRes? with _ | w
    · dsimp only
      simp
    · exact absurd rfl hz

/-- **The εA stage-domination residual** (the finest εA structural core): at every fixed
FS table `c` and shared memo, the strict verifier stage is success-pointwise dominated by
the real verifier stage, with dominated failure mass. This is the per-stage form of
`Hyb34StrictSubRunResidual`, at exactly the granularity of the per-query seeds
(`probOutput_some_hitOnly_run_le_eager` / `probFailure_hitOnly_run_le_eager`); open is the
d2fRaw dispatcher induction (the step-C bisimulation class, in inequality form). -/
def Hyb34VerifierStageDominationResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (c : (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec)).Carrier)
    (stmtIn : StmtIn) (messages : pSpec.Messages)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec),
    (∀ z, z.1.isSome = true →
      Pr[= z | splitVerifierStage (T_H := T_H) (T_P := T_P) δ
          (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
          (d2sCodecBridgeImplMemoEagerHitOnly (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
          oImpl V c stmtIn messages memo]
        ≤ Pr[= z | splitVerifierStage (T_H := T_H) (T_P := T_P) δ
          (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
          (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
          oImpl V c stmtIn messages memo])
    ∧ Pr[⊥ | splitVerifierStage (T_H := T_H) (T_P := T_P) δ
          (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
          (d2sCodecBridgeImplMemoEagerHitOnly (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
          oImpl V c stmtIn messages memo]
        ≤ Pr[⊥ | splitVerifierStage (T_H := T_H) (T_P := T_P) δ
          (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
          (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
          oImpl V c stmtIn messages memo]

/-- **The εA structural reduction, stage form** (proven): fixed-table verifier-stage
domination implies the whole-game sub-run residual — the εA leg's structural obligation is
now a *single-stage, fixed-table* domination claim, the exact surface on which the proven
per-query seeds and the step-C d2fRaw induction recipe operate. -/
theorem hyb34StrictSubRun_of_stageDomination [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (h : Hyb34VerifierStageDominationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    Hyb34StrictSubRunResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl := by
  intro V P
  refine ⟨fun o => ?_, ?_⟩
  · exact hybGameEagerSplit_probOutput_some_mono (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
      (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (d2sCodecBridgeImplMemoEagerHitOnly (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (fun log => pure log) oImpl V P
      (fun c stmtIn messages memo z hz => (h V c stmtIn messages memo).1 z hz) o
  · exact hybGameEagerSplit_probFailure_mono (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
      (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (d2sCodecBridgeImplMemoEager (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (d2sCodecBridgeImplMemoEagerHitOnly (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (fun log => pure log) oImpl V P
      (fun c stmtIn messages memo z hz => (h V c stmtIn messages memo).1 z hz)
      (fun c stmtIn messages memo => (h V c stmtIn messages memo).2)

end StageThreading

end DuplexSpongeFS.Hyb34Legs

#print axioms DuplexSpongeFS.Hyb34Legs.pmf_apply_le_at_sink
#print axioms DuplexSpongeFS.Hyb34Legs.pmf_etvDist_eq_of_le_off_sink
#print axioms DuplexSpongeFS.Hyb34Legs.pmf_tvDist_eq_of_le_off_sink
#print axioms DuplexSpongeFS.Hyb34Legs.spmf_tvDist_eq_abortGap
#print axioms DuplexSpongeFS.Hyb34Legs.spmf_abortGap_nonneg
#print axioms DuplexSpongeFS.Hyb34Legs.probOutput_bind_mono_right
#print axioms DuplexSpongeFS.Hyb34Legs.probFailure_bind_mono_right
#print axioms DuplexSpongeFS.Hyb34Legs.probOutput_bind_mono_left_event
#print axioms DuplexSpongeFS.Hyb34Legs.probFailure_bind_mono_left_event
#print axioms DuplexSpongeFS.Hyb34Legs.probOutput_some_hitOnly_run_le_eager
#print axioms DuplexSpongeFS.Hyb34Legs.probFailure_hitOnly_run_le_eager
#print axioms DuplexSpongeFS.Hyb34Legs.hyb34Divergence_of_subRun_gap
#print axioms DuplexSpongeFS.Hyb34Legs.hyb34Collapse_of_subRun_gap
#print axioms DuplexSpongeFS.Hyb34Legs.strictAbortGap_nonneg_of_subRun
#print axioms DuplexSpongeFS.Hyb34Legs.hyb34Step_of_legs
#print axioms DuplexSpongeFS.Hyb34Legs.keyLemmaEager_of_legs
#print axioms DuplexSpongeFS.Hyb34Legs.hybGameEagerSplit_probOutput_some_mono
#print axioms DuplexSpongeFS.Hyb34Legs.hybGameEagerSplit_probFailure_mono
#print axioms DuplexSpongeFS.Hyb34Legs.hyb34StrictSubRun_of_stageDomination

end
