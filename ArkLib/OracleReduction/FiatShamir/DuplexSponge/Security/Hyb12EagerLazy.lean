/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Align
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Accounting
import ArkLib.ToVCVio.OracleComp.RandomOracleEagerTableDep
import ArkLib.ToMathlib.OracleCompEvalDistBindComm

/-!
# CO25 Claim 5.22 — the eager↔lazy table alignment legs (`Hyb2FreshAlignResidual` & co.)

This module attacks the eager↔lazy alignment residuals of the Claim 5.22 round-3 split:

- `Hyb12Accounting.Hyb2FreshAlignResidual` (B1) — **CLOSED OUTRIGHT** here
  (`hyb2FreshAlign_holds`): `Hyb₂`'s once-sampled eager uniform `eSpec` table equals the
  lazily-memoized fresh-challenge sampling view `hyb2GameFresh uniformChallengeSampler`
  exactly (`Δ = 0`, an equality of `SPMF`s).
- `Hyb12Accounting.Hyb12MidFreshAlignResidual` (B2) — **proven reduction onto a strictly
  finer cross-spec residual**: the eager↔lazy half of B2 (the `gSpec` table of `Hyb12Mid`
  traded for a lazily-memoized table) is PROVEN (`hyb12Mid_eq_hyb12MidLazy`); what remains
  is `Hyb12MidCrossSpecAlignResidual`, the `gSpec → eSpec` re-keying between two *lazy*
  games (no eager table left on either side).
- `Hyb12Align.Hyb12LazyEagerResampleResidual` (A) — **proven reduction onto a strictly
  finer all-lazy residual**: both endpoints' eager `gSpec` tables are eliminated
  (`hyb1_eq_hyb1Lazy`, `hyb12MidMemo_eq_hyb12MidMemoLazy`), leaving
  `Hyb12LazyRedrawCouplingResidual`, the coupling of the forward realization against the
  memoized fiber-redraw realization with the common table sampled lazily on both sides.

## The engine: a generic lazy-memo-table ↔ eager-uniform-table master theorem

The template is `Reduction.evalDist_simulateQ_canonicalFSImpl_run_eq_eager`
(HVZKKernelInfra): the lazy random oracle from any cache equals eager uniform
dependent-table sampling, for ANY mixed computation. Here the template is re-built on the
DSFS §5.8 hybrid-game surface, with three generalizations:

1. **abstract memo carrier**: the lazy state is any type `Memo` with a `look`/`ext`
   interface satisfying first-read/extension laws (`hself`/`hne`), instantiated by the
   in-tree first-match list memos (`FreshChalMemoEntry` of `Hyb12Accounting` for `eSpec`,
   `ResampleMemoEntry` of `Hyb12Align` for `gSpec`);
2. **CPS form** (`evalDist_simulateQ_lazyGameImpl_run_bind_eq_eager`): the equality is
   proven against an arbitrary pair of continuations `Φl`/`Φe` linked by a re-sampling
   hypothesis `hΦ`, so that the memo can be *threaded across game stages* — the master
   applied to its own stage-2 instance discharges `hΦ` for the two-stage form
   (`evalDist_lazyGame_twoStage_eq_eager`), exactly matching the CO25 Figure-4 skeleton
   (prover stage, verifier stage sharing the prover's memo, sampler-free line-4 tail);
3. **abstract per-round sampler** `samp` with only a distributional uniformity hypothesis
   `hsamp`, so the in-tree `uniformChallengeSampler` (whose `SampleableType` instances are
   baked upstream) instantiates it without term-level instance surgery.

The marginalization workhorse is `OracleComp.evalDist_uniformSample_bind_update_dep`
(single-coordinate resample of a uniform dependent table is measure-preserving), lifted
locally to an `SPMF`-continuation form.

## Proven here (no `sorry`, axiom-clean)

- `evalDist_simulateQ_lazyGameImpl_run_bind_eq_eager` — the CPS master.
- `evalDist_lazyGame_twoStage_eq_eager` — the two-stage (memo-threaded) form.
- `evalDist_hybGameEager_uniform_eq_hybGameLazy` — `hybGameEager` at ANY uniform
  challenge-table distribution, ANY `gᵢ`-realization and ANY line-4 map equals its
  lazy-table form `hybGameLazy`.
- `hyb2_eq_hyb2GameFresh_uniform` / `hyb2FreshAlign_holds` — **B1 closed**.
- `hyb1_eq_hyb1Lazy`, `hyb12Mid_eq_hyb12MidLazy`, `hyb12MidMemo_eq_hyb12MidMemoLazy` —
  the three `gSpec`-side eager-table eliminations.
- `hyb12MidFreshAlign_of_crossSpecAlign`, `hyb12LazyEagerResample_of_redrawCoupling` —
  the proven reductions of B2 / A onto the finer residuals.
- `hyb12Step_of_lazyResiduals` — **the round-4 Claim 5.22 frontier**: with B1 closed and
  A/B2 at the all-lazy granularity, the full `Hyb12StepResidual` follows from five
  residuals (down from the round-3 six, with no eager table left in any alignment leg).

## Open core (named `*Residual : Prop`, NOT proven) — strictly finer than the targets

- `Hyb12MidCrossSpecAlignResidual` — `Δ(Hyb12MidLazy, hyb2GameFresh (ψ ∘ 𝒰)) = 0`: the
  `gSpec → eSpec` world re-keying between two lazily-memoized games. Per fresh derivation
  the content is the (proven) `Hyb12Step.tvDist_gImplEncodedForward_gImplDecodedChallenge_le`
  coupling shape with the challenge marginal fixed; the open content is the cross-spec
  game-level bisimulation (the two pipelines run `d2fRaw` with different `gᵢ`-realizations
  over different challenge-oracle worlds, so no common computation is available to induct
  on — a relation-carrying coupling induction through the `d2sQueryImpl` dispatcher is
  required). Plausibly TRUE: the raw logs differ only by per-entry decoding (`ψᵢ` of the
  encoded response vs the decoded response), which the line-4 maps collapse.
- `Hyb12LazyRedrawCouplingResidual` — `Δ(Hyb1Lazy, Hyb12MidMemoLazy) = 0`: forward
  realization vs memoized fiber-redraw realization against the *lazily sampled* common
  table. Plausibly TRUE: per fresh key, `(v, v)` vs `(v, r)` with `r ← 𝒰(ψ⁻¹(ψ v))` agree
  after the `ψ`-collapsing line-4 map and the redraw marginal is uniform
  (`Hyb12Align.evalDist_fiberResampleSampler`); repeats are served consistently by both
  memos. The open content is again a coupling induction inside the dispatcher (the two
  `gᵢ`-realizations differ *inside* `d2fRaw`, so the outer master does not apply).

Both finer residuals carry NO eager table: the once-sampled `OracleFamily` and its
product-marginalization arguments are fully discharged by this module.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb12EagerLazy

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open Hyb12Step
open scoped NNReal ENNReal

-- Sections below share wide variable blocks; several bricks use only a slice of them.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false

/-! ## Generic `Option`/`foldl` bricks for first-match memo lookups -/

section OptionBricks

/-- `Option.orElse` on a `none` head evaluates the fallback. -/
private lemma none_orElse_apply {γ : Type} (f : Unit → Option γ) :
    Option.orElse none f = f () := rfl

/-- An `Option.orElse` with a provably-`none` head evaluates the fallback (hypothesis
form, so the head slot may sit in any definitional presentation). -/
private lemma orElse_eq_of_none {γ : Type} {x : Option γ} (h : x = none)
    (f : Unit → Option γ) :
    Option.orElse x f = f () := by
  rw [h]
  rfl

/-- An `Option.orElse` with a provably-`none` fallback is its head (hypothesis form, so
the fallback slot may sit in any definitional presentation under the thunk binder). -/
private lemma orElse_eq_self_of_none {γ : Type} {x y : Option γ} (h : y = none) :
    (Option.orElse x fun _ => y) = x := by
  cases x with
  | none => rw [none_orElse_apply]; exact h
  | some a => rfl

/-- First-match folds ignore everything after a hit. The fallback may mention the
accumulator (as the elaborated dependent memo-match does). -/
private lemma foldl_orElse_some {β γ : Type} (g : Option γ → β → Option γ)
    (l : List β) (r : γ) :
    l.foldl (fun acc e => acc.orElse fun _ => g acc e) (some r) = some r := by
  induction l with
  | nil => rfl
  | cons e l ih => simpa only [List.foldl_cons] using ih

/-- First-match folds split across append as an `orElse`. -/
private lemma foldl_orElse_append {β γ : Type} (g : Option γ → β → Option γ)
    (l₁ l₂ : List β) :
    (l₁ ++ l₂).foldl (fun acc e => acc.orElse fun _ => g acc e) none
      = ((l₁.foldl (fun acc e => acc.orElse fun _ => g acc e) none).orElse
          fun _ => l₂.foldl (fun acc e => acc.orElse fun _ => g acc e) none) := by
  rw [List.foldl_append]
  cases h : l₁.foldl (fun acc e => acc.orElse fun _ => g acc e) none with
  | none => rfl
  | some r => exact foldl_orElse_some g l₂ r

end OptionBricks

/-! ## Generic distribution bricks -/

section DistBricks

/-- Sampling and discarding is invisible (`$ᵗ` never fails). -/
lemma evalDist_uniformSample_bind_const {T : Type} [SampleableType T] {β : Type}
    (z : ProbComp β) :
    𝒟[($ᵗ T : ProbComp T) >>= fun _ => z] = 𝒟[z] := by
  refine evalDist_ext fun b => ?_
  rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
    tsum_probOutput_eq_one' (probFailure_uniformSample T), one_mul]

/-- `SPMF` associativity, pinned to the standard instance (used as a rewriting brick on
`evalDist`-produced binds). -/
private lemma spmf_bind_assoc {α₁ α₂ α₃ : Type} (p : SPMF α₁) (q : α₁ → SPMF α₂)
    (k : α₂ → SPMF α₃) :
    (p >>= q) >>= k = p >>= fun a => q a >>= k :=
  bind_assoc p q k

/-- `SPMF` left unit, pinned to the standard instance. -/
private lemma spmf_pure_bind {α₁ α₂ : Type} (a : α₁) (k : α₁ → SPMF α₂) :
    (pure a : SPMF α₁) >>= k = k a :=
  pure_bind a k

/-- **Dependent marginalization, `SPMF`-continuation form**: post-binding an arbitrary
`SPMF`-valued continuation through a single-coordinate resample of a uniform dependent
table is invisible. Lifted from `OracleComp.evalDist_uniformSample_bind_update_dep`. -/
private lemma spmf_uniformSample_bind_update_bind_dep
    {ι' : Type} {R : ι' → Type} [Fintype ι'] [DecidableEq ι']
    [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] [∀ i, SampleableType (R i)]
    [SampleableType (∀ i, R i)] (t : ι') {β : Type} (K : (∀ i, R i) → SPMF β) :
    (𝒟[($ᵗ (R t) : ProbComp _)] >>= fun u => 𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g =>
        K (Function.update g t u))
      = 𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g => K g := by
  have h0 := OracleComp.evalDist_uniformSample_bind_update_dep (R := R) t
  have hsplit : 𝒟[do
        let u ← ($ᵗ (R t) : ProbComp _)
        let g ← ($ᵗ (∀ i, R i) : ProbComp _)
        pure (Function.update g t u)]
      = (𝒟[($ᵗ (R t) : ProbComp _)] >>= fun u =>
          𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g =>
            (pure (Function.update g t u) : SPMF _)) := by
    rw [evalDist_bind]
    refine congrArg _ (funext fun u => ?_)
    rw [evalDist_bind]
    refine congrArg _ (funext fun g => ?_)
    exact evalDist_pure _
  have h1 := hsplit.symm.trans h0
  calc (𝒟[($ᵗ (R t) : ProbComp _)] >>= fun u =>
          𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g => K (Function.update g t u))
      = 𝒟[($ᵗ (R t) : ProbComp _)] >>= fun u =>
          𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g =>
            (pure (Function.update g t u) : SPMF _) >>= K := by
        refine congrArg _ (funext fun u => congrArg _ (funext fun g => ?_))
        exact (spmf_pure_bind _ _).symm
    _ = 𝒟[($ᵗ (R t) : ProbComp _)] >>= fun u =>
          (𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g =>
            (pure (Function.update g t u) : SPMF _)) >>= K := by
        refine congrArg _ (funext fun u => ?_)
        exact (spmf_bind_assoc _ _ _).symm
    _ = (𝒟[($ᵗ (R t) : ProbComp _)] >>= fun u =>
          𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g =>
            (pure (Function.update g t u) : SPMF _)) >>= K :=
        (spmf_bind_assoc _ _ _).symm
    _ = 𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= K := by rw [h1]
    _ = 𝒟[($ᵗ (∀ i, R i) : ProbComp _)] >>= fun g => K g := rfl

end DistBricks

/-! ## The generic lazy-memo-table game implementation and the master theorem

The lazy side answers challenge-oracle queries from an abstract memo (`look`), paying an
abstract per-key sampler (`samp`) on first reads (`ext` records them); shared-`oSpec`,
`(Unit →ₒ U)` and `unifSpec` queries are forwarded statelessly. The eager side reads a
fixed table; the master theorem couples the two through the memo-overlay
`memoOverlay look m c := fun q => (look m q).getD (c q)`. -/

section GenericLazyTable

variable {ι : Type} {oSpec : OracleSpec ι} {U : Type} [SpongeUnit U] [SampleableType U]
  {κ : Type} {chSpec : OracleSpec κ} {Memo : Type}

variable (look : Memo → (q : κ) → Option (chSpec.Range q))
  (ext : Memo → (q : κ) → chSpec.Range q → Memo)
  (samp : (q : κ) → ProbComp (chSpec.Range q))

/-- The abstract lazily-memoized challenge implementation: memo hits answer
deterministically, fresh keys pay `samp` once and are recorded by `ext`. -/
noncomputable def lazyChalImpl : QueryImpl chSpec (StateT Memo ProbComp) :=
  fun q => fun m =>
    (look m q).elim
      (samp q >>= fun u => pure (u, ext m q u))
      (fun r => pure (r, m))

/-- The full lazy-game implementation over the §5.4 outer spec: shared `oSpec` queries
forwarded, challenge queries through the lazy memo, auxiliary `(Unit →ₒ U)`/`unifSpec`
sampling realized exactly as in `hybGameEager`. -/
noncomputable def lazyGameImpl (oImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec)
      (StateT Memo ProbComp) :=
  fun t => match t with
  | .inl qo => StateT.lift (oImpl qo)
  | .inr (.inl qc) => lazyChalImpl look ext samp qc
  | .inr (.inr (.inl qu)) => StateT.lift (d2sUnitSampleImpl (U := U) qu)
  | .inr (.inr (.inr mi)) => StateT.lift (liftM (unifSpec.query mi) : ProbComp _)

/-- The eager-table game implementation (verbatim the `impl` of `hybGameEager` at a
function-table realization). -/
noncomputable def eagerGameImpl (oImpl : QueryImpl oSpec ProbComp)
    (c : OracleFamily chSpec) :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec) ProbComp :=
  oImpl + (tableQueryImpl c + (d2sUnitSampleImpl (U := U) +
    (fun mi => (liftM (unifSpec.query mi) : ProbComp _))))

/-- The deterministic overlay of a lazy memo over an eager table. -/
noncomputable def memoOverlay (m : Memo) (c : OracleFamily chSpec) : OracleFamily chSpec :=
  fun q => (look m q).getD (c q)

/-! ### Run shapes (all definitional) -/

/-! The `pure`s below are ascribed at the sum-spec range type so that the downstream
`evalDist_bind`/`spmf_pure_bind` rewrites match the `simulateQ`-generated type arguments
syntactically (same convention as `Reduction.canonicalFSImpl_run_inl`). -/

lemma lazyGameImpl_run_inl (oImpl : QueryImpl oSpec ProbComp) (qo : ι) (m : Memo) :
    (lazyGameImpl (U := U) look ext samp oImpl (Sum.inl qo)).run m
      = oImpl qo >>= fun a =>
          (pure (a, m) : ProbComp
            ((oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range (Sum.inl qo)
              × Memo)) := rfl

lemma lazyGameImpl_run_chal (oImpl : QueryImpl oSpec ProbComp) (qc : κ) (m : Memo) :
    (lazyGameImpl (U := U) look ext samp oImpl (Sum.inr (Sum.inl qc))).run m
      = (look m qc).elim
          (samp qc >>= fun u =>
            (pure (u, ext m qc u) : ProbComp
              ((oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
                  (Sum.inr (Sum.inl qc)) × Memo)))
          (fun r =>
            (pure (r, m) : ProbComp
              ((oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
                  (Sum.inr (Sum.inl qc)) × Memo))) := rfl

lemma lazyGameImpl_run_unit (oImpl : QueryImpl oSpec ProbComp) (qu : Unit) (m : Memo) :
    (lazyGameImpl (U := U) look ext samp oImpl (Sum.inr (Sum.inr (Sum.inl qu)))).run m
      = d2sUnitSampleImpl (U := U) qu >>= fun a =>
          (pure (a, m) : ProbComp
            ((oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
                (Sum.inr (Sum.inr (Sum.inl qu))) × Memo)) := rfl

lemma lazyGameImpl_run_coin (oImpl : QueryImpl oSpec ProbComp) (mi : ℕ) (m : Memo) :
    (lazyGameImpl (U := U) look ext samp oImpl (Sum.inr (Sum.inr (Sum.inr mi)))).run m
      = (liftM (unifSpec.query mi) : ProbComp _) >>= fun a =>
          (pure (a, m) : ProbComp
            ((oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
                (Sum.inr (Sum.inr (Sum.inr mi))) × Memo)) := rfl

lemma eagerGameImpl_inl (oImpl : QueryImpl oSpec ProbComp) (c : OracleFamily chSpec)
    (qo : ι) :
    eagerGameImpl (U := U) oImpl c (Sum.inl qo) = oImpl qo := rfl

lemma eagerGameImpl_chal (oImpl : QueryImpl oSpec ProbComp) (c : OracleFamily chSpec)
    (qc : κ) :
    eagerGameImpl (U := U) oImpl c (Sum.inr (Sum.inl qc))
      = (pure (c qc) : ProbComp
          ((oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
            (Sum.inr (Sum.inl qc)))) := rfl

lemma eagerGameImpl_unit (oImpl : QueryImpl oSpec ProbComp) (c : OracleFamily chSpec)
    (qu : Unit) :
    eagerGameImpl (U := U) oImpl c (Sum.inr (Sum.inr (Sum.inl qu)))
      = d2sUnitSampleImpl (U := U) qu := rfl

lemma eagerGameImpl_coin (oImpl : QueryImpl oSpec ProbComp) (c : OracleFamily chSpec)
    (mi : ℕ) :
    eagerGameImpl (U := U) oImpl c (Sum.inr (Sum.inr (Sum.inr mi)))
      = (liftM (unifSpec.query mi) : ProbComp _) := rfl

/-! ### Composite distribution shapes of single steps (the `𝒟`-split forms consumed by the
master induction; each collapses one oracle step against an arbitrary `SPMF` continuation,
so no rewriting of freshly-produced subterms is ever needed). -/

private lemma evalDist_lazyGameImpl_run_inl_bind {β' : Type}
    (oImpl : QueryImpl oSpec ProbComp) (qo : ι) (m : Memo)
    (K : (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range (Sum.inl qo) × Memo →
      SPMF β') :
    (𝒟[(lazyGameImpl (U := U) look ext samp oImpl (Sum.inl qo)).run m] >>= K)
      = 𝒟[oImpl qo] >>= fun a => K (a, m) := by
  rw [lazyGameImpl_run_inl, evalDist_bind, spmf_bind_assoc]
  refine congrArg _ (funext fun a => ?_)
  rw [evalDist_pure, spmf_pure_bind]

private lemma evalDist_lazyGameImpl_run_unit_bind {β' : Type}
    (oImpl : QueryImpl oSpec ProbComp) (qu : Unit) (m : Memo)
    (K : (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
        (Sum.inr (Sum.inr (Sum.inl qu))) × Memo → SPMF β') :
    (𝒟[(lazyGameImpl (U := U) look ext samp oImpl
        (Sum.inr (Sum.inr (Sum.inl qu)))).run m] >>= K)
      = 𝒟[d2sUnitSampleImpl (U := U) qu] >>= fun a => K (a, m) := by
  rw [lazyGameImpl_run_unit, evalDist_bind, spmf_bind_assoc]
  refine congrArg _ (funext fun a => ?_)
  rw [evalDist_pure, spmf_pure_bind]

private lemma evalDist_lazyGameImpl_run_coin_bind {β' : Type}
    (oImpl : QueryImpl oSpec ProbComp) (mi : ℕ) (m : Memo)
    (K : (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
        (Sum.inr (Sum.inr (Sum.inr mi))) × Memo → SPMF β') :
    (𝒟[(lazyGameImpl (U := U) look ext samp oImpl
        (Sum.inr (Sum.inr (Sum.inr mi)))).run m] >>= K)
      = 𝒟[(liftM (unifSpec.query mi) : ProbComp _)] >>= fun a => K (a, m) := by
  rw [lazyGameImpl_run_coin, evalDist_bind, spmf_bind_assoc]
  refine congrArg _ (funext fun a => ?_)
  rw [evalDist_pure, spmf_pure_bind]

private lemma evalDist_lazyGameImpl_run_chal_bind {β' : Type}
    (oImpl : QueryImpl oSpec ProbComp) (qc : κ) (m : Memo)
    (K : (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
        (Sum.inr (Sum.inl qc)) × Memo → SPMF β') :
    (𝒟[(lazyGameImpl (U := U) look ext samp oImpl (Sum.inr (Sum.inl qc))).run m] >>= K)
      = (look m qc).elim
          (𝒟[samp qc] >>= fun u => K (u, ext m qc u))
          (fun r => K (r, m)) := by
  rw [lazyGameImpl_run_chal]
  cases hl : look m qc with
  | none =>
      simp only [Option.elim_none]
      rw [evalDist_bind, spmf_bind_assoc]
      refine congrArg _ (funext fun u => ?_)
      rw [evalDist_pure, spmf_pure_bind]
  | some r =>
      simp only [Option.elim_some]
      rw [evalDist_pure, spmf_pure_bind]

private lemma evalDist_eagerGameImpl_chal_bind {β' : Type}
    (oImpl : QueryImpl oSpec ProbComp) (c' : OracleFamily chSpec) (qc : κ)
    (K : (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range
        (Sum.inr (Sum.inl qc)) → SPMF β') :
    (𝒟[eagerGameImpl (U := U) oImpl c' (Sum.inr (Sum.inl qc))] >>= K)
      = K (c' qc) := by
  rw [eagerGameImpl_chal, evalDist_pure, spmf_pure_bind]

/-! ### Overlay algebra -/

variable [DecidableEq κ]

/-- Extending the memo at a fresh key is overlaying the updated table. -/
lemma memoOverlay_ext_of_none
    (hself : ∀ m q u, look m q = none → look (ext m q u) q = some u)
    (hne : ∀ m q u q', q ≠ q' → look (ext m q u) q' = look m q')
    {m : Memo} {q : κ} (hmiss : look m q = none) (u : chSpec.Range q)
    (c : OracleFamily chSpec) :
    memoOverlay look (ext m q u) c = memoOverlay look m (Function.update c q u) := by
  funext q'
  by_cases h : q = q'
  · subst h
    simp only [memoOverlay, hself m q u hmiss, hmiss, Option.getD_some, Option.getD_none,
      Function.update_self]
  · simp only [memoOverlay, hne m q u q' h, Function.update_of_ne (Ne.symm h)]

/-- Reading the overlay of an updated table at the (memo-fresh) updated key. -/
lemma memoOverlay_update_read {m : Memo} {q : κ} (hmiss : look m q = none)
    (u : chSpec.Range q) (c : OracleFamily chSpec) :
    memoOverlay look m (Function.update c q u) q = u := by
  simp only [memoOverlay, hmiss, Option.getD_none, Function.update_self]

/-- The overlay of an everywhere-missing memo is the table itself. -/
lemma memoOverlay_of_forall_none {m₀ : Memo} (hm₀ : ∀ q, look m₀ q = none)
    (c : OracleFamily chSpec) :
    memoOverlay look m₀ c = c := by
  funext q
  simp only [memoOverlay, hm₀ q, Option.getD_none]

/-! ### The master theorem (CPS form) -/

variable [Fintype κ]
  [∀ q : κ, Fintype (chSpec.Range q)] [∀ q : κ, Nonempty (chSpec.Range q)]
  [∀ q : κ, SampleableType (chSpec.Range q)] [SampleableType (OracleFamily chSpec)]

set_option maxHeartbeats 2000000 in
-- the induction normalizes full game-step trees per oracle arm
/-- **The eager↔lazy master theorem (CPS form).** Simulating any computation over the
§5.4 outer spec through the lazy-memo-table implementation from memo `m`, then running a
memo-consuming continuation `Φl`, is distributionally equal to: eagerly sample a uniform
challenge table `c`, simulate against the overlay `memoOverlay look m c`, then run the
table-consuming continuation `Φe` at the same overlay — provided `Φl`/`Φe` are themselves
linked by the same re-sampling identity (`hΦ`), the sampler is distributionally uniform
per key (`hsamp`), and the memo satisfies the first-read laws (`hself`/`hne`).

This is `Reduction.evalDist_simulateQ_canonicalFSImpl_run_eq_eager` rebuilt on the DSFS
hybrid-game surface; the CPS continuation is what lets the memo thread across the
prover/verifier stages of the Figure-4 skeleton. -/
theorem evalDist_simulateQ_lazyGameImpl_run_bind_eq_eager
    (hsamp : ∀ q, 𝒟[samp q] = 𝒟[($ᵗ (chSpec.Range q) : ProbComp _)])
    (hself : ∀ m q u, look m q = none → look (ext m q u) q = some u)
    (hne : ∀ m q u q', q ≠ q' → look (ext m q u) q' = look m q')
    (oImpl : QueryImpl oSpec ProbComp) {α β : Type}
    (Φl : α → Memo → ProbComp β) (Φe : α → OracleFamily chSpec → ProbComp β)
    (hΦ : ∀ x m, 𝒟[Φl x m]
      = 𝒟[($ᵗ (OracleFamily chSpec) : ProbComp _) >>= fun c =>
          Φe x (memoOverlay look m c)])
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec) α) (m : Memo) :
    𝒟[(simulateQ (lazyGameImpl (U := U) look ext samp oImpl) oa).run m >>= fun p =>
        Φl p.1 p.2]
      = 𝒟[($ᵗ (OracleFamily chSpec) : ProbComp _) >>= fun c =>
          simulateQ (eagerGameImpl (U := U) oImpl (memoOverlay look m c)) oa >>= fun x =>
            Φe x (memoOverlay look m c)] := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure x =>
      rw [simulateQ_pure, StateT.run_pure, pure_bind]
      simp only [simulateQ_pure, pure_bind]
      exact hΦ x m
  | query_bind t mx ih =>
      -- the induction hypothesis, in the fully-split SPMF normal form
      have ih' : ∀ (u : (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec).Range t)
          (m' : Memo),
          (𝒟[(simulateQ (lazyGameImpl (U := U) look ext samp oImpl) (mx u)).run m']
              >>= fun p => 𝒟[Φl p.1 p.2])
            = 𝒟[($ᵗ (OracleFamily chSpec) : ProbComp _)] >>= fun c =>
                𝒟[simulateQ (eagerGameImpl (U := U) oImpl (memoOverlay look m' c)) (mx u)]
                  >>= fun x => 𝒟[Φe x (memoOverlay look m' c)] := by
        intro u m'
        have h := ih u m'
        simp only [evalDist_bind] at h
        exact h
      rcases t with qo | qc | qu | mi
      · -- shared `oSpec` query: stateless on both sides; commute the table sampling
        simp only [simulateQ_query_bind, OracleQuery.cont_query, OracleQuery.snd_query,
          id_eq, OracleQuery.input_query, monadLift_self, StateT.run_bind,
          evalDist_bind, spmf_bind_assoc]
        rw [evalDist_lazyGameImpl_run_inl_bind]
        exact Eq.trans
          (congrArg (𝒟[oImpl qo] >>= ·) (funext fun a => ih' a m))
          (SPMF.bind_comm _ _ _)
      · -- challenge query: split on memo hit/miss
        rcases hlook : look m qc with _ | r
        · -- miss: fresh sample + memo write; marginalize the coordinate resample away
          simp only [simulateQ_query_bind, OracleQuery.cont_query, OracleQuery.snd_query,
            id_eq, OracleQuery.input_query, monadLift_self, StateT.run_bind,
            evalDist_bind, spmf_bind_assoc]
          rw [evalDist_lazyGameImpl_run_chal_bind, hlook, Option.elim_none]
          simp only [evalDist_eagerGameImpl_chal_bind]
          set ψ : OracleFamily chSpec → SPMF β := fun c' =>
            𝒟[simulateQ (eagerGameImpl (U := U) oImpl (memoOverlay look m c'))
                (mx (memoOverlay look m c' qc))] >>= fun x =>
              𝒟[Φe x (memoOverlay look m c')] with hψ
          have hfun : ∀ u : chSpec.Range qc,
              (fun c => 𝒟[simulateQ (eagerGameImpl (U := U) oImpl
                    (memoOverlay look (ext m qc u) c)) (mx u)] >>= fun x =>
                  𝒟[Φe x (memoOverlay look (ext m qc u) c)])
                = fun c => ψ (Function.update c qc u) := by
            intro u
            funext c
            simp only [hψ]
            rw [memoOverlay_ext_of_none look ext hself hne hlook u c,
              memoOverlay_update_read look hlook u c]
          refine Eq.trans (congrArg (𝒟[samp qc] >>= ·) (funext fun u =>
            Eq.trans (ih' u (ext m qc u))
              (congrArg (𝒟[($ᵗ (OracleFamily chSpec) : ProbComp _)] >>= ·)
                (hfun u)))) ?_
          refine Eq.trans ?_
            (spmf_uniformSample_bind_update_bind_dep (R := chSpec.Range) qc ψ)
          exact congrArg
            (· >>= fun u => 𝒟[($ᵗ (OracleFamily chSpec) : ProbComp _)] >>= fun c =>
              ψ (Function.update c qc u))
            (hsamp qc)
        · -- hit: both sides answer deterministically from the memo/overlay
          simp only [simulateQ_query_bind, OracleQuery.cont_query, OracleQuery.snd_query,
            id_eq, OracleQuery.input_query, monadLift_self, StateT.run_bind,
            evalDist_bind, spmf_bind_assoc]
          rw [evalDist_lazyGameImpl_run_chal_bind, hlook, Option.elim_some]
          simp only [evalDist_eagerGameImpl_chal_bind]
          have hread : ∀ c, memoOverlay look m c qc = r := fun c => by
            simp only [memoOverlay, hlook, Option.getD_some]
          refine Eq.trans (ih' r m)
            (congrArg (𝒟[($ᵗ (OracleFamily chSpec) : ProbComp _)] >>= ·)
              (funext fun c => ?_))
          rw [hread c]
          try rfl
      · -- auxiliary `(Unit →ₒ U)` sampling: stateless on both sides
        simp only [simulateQ_query_bind, OracleQuery.cont_query, OracleQuery.snd_query,
          id_eq, OracleQuery.input_query, monadLift_self, StateT.run_bind,
          evalDist_bind, spmf_bind_assoc]
        rw [evalDist_lazyGameImpl_run_unit_bind]
        exact Eq.trans
          (congrArg (𝒟[d2sUnitSampleImpl (U := U) qu] >>= ·) (funext fun a => ih' a m))
          (SPMF.bind_comm _ _ _)
      · -- auxiliary `unifSpec` coins: stateless on both sides
        simp only [simulateQ_query_bind, OracleQuery.cont_query, OracleQuery.snd_query,
          id_eq, OracleQuery.input_query, monadLift_self, StateT.run_bind,
          evalDist_bind, spmf_bind_assoc]
        rw [evalDist_lazyGameImpl_run_coin_bind]
        exact Eq.trans
          (congrArg (𝒟[(liftM (unifSpec.query mi) : ProbComp _)] >>= ·)
            (funext fun a => ih' a m))
          (SPMF.bind_comm _ _ _)

/-- **The two-stage (memo-threaded) eager↔lazy theorem.** The CO25 Figure-4 game shape —
a prover-stage computation, an abort decision on its value, a verifier-stage computation
*sharing the prover's memo* (lazy) resp. the same table (eager), and a sampler-free tail —
is eager↔lazy aligned. Obtained by applying the CPS master to itself (the inner instance
discharges the continuation hypothesis of the outer one). -/
theorem evalDist_lazyGame_twoStage_eq_eager
    (hsamp : ∀ q, 𝒟[samp q] = 𝒟[($ᵗ (chSpec.Range q) : ProbComp _)])
    (hself : ∀ m q u, look m q = none → look (ext m q u) q = some u)
    (hne : ∀ m q u q', q ≠ q' → look (ext m q u) q' = look m q')
    (oImpl : QueryImpl oSpec ProbComp)
    {m₀ : Memo} (hm₀ : ∀ q, look m₀ q = none)
    {α₁ σ₂ α₂ γ : Type}
    (oa₁ : OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec) α₁)
    (sel : α₁ → Option σ₂) (failv : ProbComp γ)
    (oa₂ : σ₂ → OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) chSpec) α₂)
    (tail : α₁ → σ₂ → α₂ → ProbComp γ) :
    𝒟[(simulateQ (lazyGameImpl (U := U) look ext samp oImpl) oa₁).run m₀ >>= fun x =>
        (sel x.1).elim failv fun s =>
          (simulateQ (lazyGameImpl (U := U) look ext samp oImpl) (oa₂ s)).run x.2
            >>= fun y => tail x.1 s y.1]
      = 𝒟[($ᵗ (OracleFamily chSpec) : ProbComp _) >>= fun c =>
          simulateQ (eagerGameImpl (U := U) oImpl c) oa₁ >>= fun x =>
            (sel x).elim failv fun s =>
              simulateQ (eagerGameImpl (U := U) oImpl c) (oa₂ s) >>= fun y =>
                tail x s y] := by
  have h := evalDist_simulateQ_lazyGameImpl_run_bind_eq_eager look ext samp
    hsamp hself hne oImpl
    (Φl := fun x mm => (sel x).elim failv fun s =>
      (simulateQ (lazyGameImpl (U := U) look ext samp oImpl) (oa₂ s)).run mm
        >>= fun y => tail x s y.1)
    (Φe := fun x c => (sel x).elim failv fun s =>
      simulateQ (eagerGameImpl (U := U) oImpl c) (oa₂ s) >>= fun y => tail x s y)
    (hΦ := by
      intro x mm
      rcases hsel : sel x with _ | s
      · simp only [hsel, Option.elim_none]
        exact (evalDist_uniformSample_bind_const failv).symm
      · simp only [hsel, Option.elim_some]
        exact evalDist_simulateQ_lazyGameImpl_run_bind_eq_eager look ext samp
          hsamp hself hne oImpl
          (Φl := fun y _ => tail x s y) (Φe := fun y _ => tail x s y)
          (fun y mm' => (evalDist_uniformSample_bind_const (tail x s y)).symm)
          (oa₂ s) mm)
    oa₁ m₀
  simp only [memoOverlay_of_forall_none look hm₀] at h
  exact h

end GenericLazyTable

/-! ## The DSFS context -/

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

/-- Local `VCVCompatible U` (giving `Fintype (Vector U m)`). Not exported. -/
local instance : VCVCompatible U where
  type_decidableEq' := inferInstance

/-- Local `Inhabited` for encoded blocks. Not exported. -/
local instance {m : ℕ} : Inhabited (Vector U m) := ⟨Vector.replicate m default⟩

/-- Local uniform sampling for decoded challenges. Not exported. -/
local instance (i : pSpec.ChallengeIdx) : SampleableType (pSpec.Challenge i) :=
  SampleableType.ofFintype _

/-- Local uniform sampling for encoded blocks. Not exported. -/
local instance {m : ℕ} : SampleableType (Vector U m) :=
  SampleableType.ofFintype _

/-! Local instances on the §5.8 challenge-oracle domains and ranges (synthesis cannot see
through `OracleInterface`-built specs, so they are provided through the concrete sigma
shape). Not exported. -/

local instance : Fintype ((eSpec (U := U) StmtIn pSpec δ).Domain) :=
  inferInstanceAs (Fintype ((i : pSpec.ChallengeIdx) ×
    (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)))

local instance : DecidableEq ((eSpec (U := U) StmtIn pSpec δ).Domain) :=
  inferInstanceAs (DecidableEq ((i : pSpec.ChallengeIdx) ×
    (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)))

local instance (q : (eSpec (U := U) StmtIn pSpec δ).Domain) :
    Fintype ((eSpec (U := U) StmtIn pSpec δ).Range q) :=
  inferInstanceAs (Fintype (pSpec.Challenge q.1))

local instance (q : (eSpec (U := U) StmtIn pSpec δ).Domain) :
    Nonempty ((eSpec (U := U) StmtIn pSpec δ).Range q) :=
  inferInstanceAs (Nonempty (pSpec.Challenge q.1))

local instance (q : (eSpec (U := U) StmtIn pSpec δ).Domain) :
    SampleableType ((eSpec (U := U) StmtIn pSpec δ).Range q) :=
  inferInstanceAs (SampleableType (pSpec.Challenge q.1))

local instance : Fintype ((gSpec (U := U) StmtIn pSpec δ).Domain) :=
  inferInstanceAs (Fintype ((i : pSpec.ChallengeIdx) ×
    (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)))

local instance : DecidableEq ((gSpec (U := U) StmtIn pSpec δ).Domain) :=
  inferInstanceAs (DecidableEq ((i : pSpec.ChallengeIdx) ×
    (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)))

local instance (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    Fintype ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
  inferInstanceAs (Fintype (Vector U (challengeSize (pSpec := pSpec) q.1)))

local instance (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    Nonempty ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
  inferInstanceAs (Nonempty (Vector U (challengeSize (pSpec := pSpec) q.1)))

local instance (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    SampleableType ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
  inferInstanceAs (SampleableType (Vector U (challengeSize (pSpec := pSpec) q.1)))

/-! ## The generic lazy-table hybrid game and the eager↔lazy game theorem -/

section LazyGame

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The lazy-table form of `hybGameEager` (CO25 Figure 4 lines 2–4 with the eager line-1
table sampling traded for the lazily-memoized implementation, the prover-stage memo handed
to the verifier stage exactly as the eager game holds its one table fixed). Generic over
the challenge-oracle world, the memo interface, the `gᵢ`-realization and the line-4 map. -/
noncomputable def hybGameLazy [SampleableType U]
    {κ : Type} {chSpec : OracleSpec κ} {Memo : Type}
    (look : Memo → (q : κ) → Option (chSpec.Range q))
    (ext : Memo → (q : κ) → chSpec.Range q → Memo)
    (samp : (q : κ) → ProbComp (chSpec.Range q))
    (m₀ : Memo)
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M] (δ : ℕ)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) chSpec M)
    (lineFour : QueryLog (oSpec + chSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  (simulateQ (lazyGameImpl (U := U) look ext samp oImpl)
      ((simulateQ loggingOracle
        ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl P default).run)).run)).run m₀
    >>= fun x =>
  (x.1.1).elim (pure none) fun r =>
    (simulateQ (lazyGameImpl (U := U) look ext samp oImpl)
        ((simulateQ loggingOracle
          ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl
            ((V.duplexSpongeFiatShamir.run
              r.1.1.1 (fun i => match i with | ⟨0, _⟩ => r.1.1.2)).run)
            r.2).run)).run)).run x.2
      >>= fun y =>
    match y.1.1 with
    | none => pure none
    | some vr =>
        match vr.1.1 with
        | none => pure none
        | some stmtOut => do
            let pLog'? ←
              simulateQ (d2sUnitSampleImpl (U := U))
                ((lineFour (projectChallengePlusUnitQueryLog (U := U) x.1.2)).run)
            let vLog'? ←
              simulateQ (d2sUnitSampleImpl (U := U))
                ((lineFour (projectChallengePlusUnitQueryLog (U := U) y.1.2)).run)
            match pLog'?, vLog'? with
            | some pLog', some vLog' =>
                pure (some ⟨r.1.1.1, stmtOut, r.1.1.2, pLog', vLog'⟩)
            | _, _ => pure none

set_option maxHeartbeats 2000000 in
-- the congruence decomposition compares full hybrid-game skeletons leafwise
/-- **The eager↔lazy game theorem (generic).** `hybGameEager` at a uniform function-table
challenge distribution equals its lazy-table form, for ANY `gᵢ`-realization, ANY line-4
map and ANY memo interface satisfying the first-read laws with a per-key uniform sampler.
This is the eager table of CO25 Figure 4 line 1 traded for lazy sampling, wholesale. -/
theorem evalDist_hybGameEager_uniform_eq_hybGameLazy [SampleableType U]
    {κ : Type} {chSpec : OracleSpec κ} {Memo : Type}
    [Fintype κ] [DecidableEq κ]
    [∀ q : κ, Fintype (chSpec.Range q)] [∀ q : κ, Nonempty (chSpec.Range q)]
    [∀ q : κ, SampleableType (chSpec.Range q)] [SampleableType (OracleFamily chSpec)]
    (look : Memo → (q : κ) → Option (chSpec.Range q))
    (ext : Memo → (q : κ) → chSpec.Range q → Memo)
    (samp : (q : κ) → ProbComp (chSpec.Range q))
    (hsamp : ∀ q, 𝒟[samp q] = 𝒟[($ᵗ (chSpec.Range q) : ProbComp _)])
    (hself : ∀ m q u, look m q = none → look (ext m q u) q = some u)
    (hne : ∀ m q u q', q ≠ q' → look (ext m q u) q' = look m q')
    {m₀ : Memo} (hm₀ : ∀ q, look m₀ q = none)
    {M : Type} [Inhabited M] (δ : ℕ)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) chSpec M)
    (lineFour : QueryLog (oSpec + chSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
        (OracleDistribution.uniform chSpec) gImpl lineFour oImpl V P]
      = 𝒟[hybGameLazy (oSpec := oSpec) (StmtOut := StmtOut)
          look ext samp m₀ T_H T_P δ gImpl lineFour oImpl V P] := by
  have h := evalDist_lazyGame_twoStage_eq_eager look ext samp hsamp hself hne oImpl hm₀
    (oa₁ := (simulateQ loggingOracle
      ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl P default).run)).run)
    (sel := fun x => x.1)
    (failv := (pure none : ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))))
    (oa₂ := fun r => (simulateQ loggingOracle
      ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl
        ((V.duplexSpongeFiatShamir.run
          r.1.1.1 (fun i => match i with | ⟨0, _⟩ => r.1.1.2)).run)
        r.2).run)).run)
    (tail := fun x r y =>
      match y.1 with
      | none => pure none
      | some vr =>
          match vr.1.1 with
          | none => pure none
          | some stmtOut => do
              let pLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) x.2)).run)
              let vLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) y.2)).run)
              match pLog'?, vLog'? with
              | some pLog', some vLog' =>
                  pure (some ⟨r.1.1.1, stmtOut, r.1.1.2, pLog', vLog'⟩)
              | _, _ => pure none)
  refine Eq.trans ?_ (Eq.trans h.symm ?_)
  · -- `hybGameEager` is the eager two-stage form (congruence decomposition; every leaf
    -- compares matcher applications at constructor-headed scrutinees)
    refine congrArg (fun z => 𝒟[z]) ?_
    simp only [hybGameEager, OracleDistribution.uniform, OracleDistribution.functionTable,
      eagerGameImpl]
    refine bind_congr fun c => ?_
    refine bind_congr fun x => ?_
    rcases x with ⟨pRes?, pLogRaw⟩
    rcases pRes? with _ | r
    · rfl
    · rcases r with ⟨⟨⟨stmtIn, messages⟩, st⟩, memo⟩
      refine bind_congr fun y => ?_
      rcases y with ⟨vRes?, vLogRaw⟩
      rcases vRes? with _ | vr
      · rfl
      · rcases vr with ⟨⟨stmtOut?, st2⟩, st3⟩
        rcases stmtOut? with _ | stmtOut
        · rfl
        · refine bind_congr fun pLog'? => ?_
          refine bind_congr fun vLog'? => ?_
          rcases pLog'? with _ | pLog' <;> rcases vLog'? with _ | vLog' <;> rfl
  · -- the lazy two-stage form is `hybGameLazy` on the nose
    refine congrArg (fun z => 𝒟[z]) ?_
    simp only [hybGameLazy]

end LazyGame

/-! ## Memo-law instantiations for the in-tree first-match list memos -/

section MemoLaws

open Hyb12Accounting in
/-- Hit on the matching singleton entry (`eSpec` memo). -/
private lemma lookupFreshChalMemo_singleton_self
    (i : pSpec.ChallengeIdx) (s : StmtIn) (τ : Vector U δ)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc) (u : pSpec.Challenge i) :
    lookupFreshChalMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      [⟨i, s, τ, em, u⟩] i s τ em = some u := by
  unfold lookupFreshChalMemo
  simp only [List.foldl_cons, List.foldl_nil]
  rw [none_orElse_apply]
  simp

open Hyb12Accounting in
/-- Miss on a non-matching singleton entry (`eSpec` memo). -/
private lemma lookupFreshChalMemo_singleton_ne
    (i i' : pSpec.ChallengeIdx) (s s' : StmtIn) (τ τ' : Vector U δ)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (em' : pSpec.EncodedMessagesBefore U i'.1.castSucc) (u : pSpec.Challenge i)
    (hq : (⟨i, s, τ, em⟩ : (eSpec (U := U) StmtIn pSpec δ).Domain) ≠ ⟨i', s', τ', em'⟩) :
    lookupFreshChalMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      [⟨i, s, τ, em, u⟩] i' s' τ' em' = none := by
  unfold lookupFreshChalMemo
  simp only [List.foldl_cons, List.foldl_nil]
  rw [none_orElse_apply]
  by_cases hi : i = i'
  · subst hi
    rw [dif_pos (show (⟨i, s, τ, em, u⟩ :
      Hyb12Accounting.FreshChalMemoEntry StmtIn U δ pSpec).roundIdx = i from rfl)]
    change (if s = s' ∧ τ = τ' ∧ em = em' then some u else none) = none
    refine if_neg fun hcon => hq ?_
    obtain ⟨h1, h2, h3⟩ := hcon
    subst h1; subst h2; subst h3; rfl
  · exact dif_neg hi

open Hyb12Accounting in
/-- First-match append split for the `eSpec` memo lookup. -/
private lemma lookupFreshChalMemo_append
    (m₁ m₂ : List (FreshChalMemoEntry StmtIn U δ pSpec))
    (i : pSpec.ChallengeIdx) (s : StmtIn) (τ : Vector U δ)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    lookupFreshChalMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
        (m₁ ++ m₂) i s τ em
      = Option.orElse
          (lookupFreshChalMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
            m₁ i s τ em)
          (fun _ => lookupFreshChalMemo (StmtIn := StmtIn) (U := U) (δ := δ)
            (pSpec := pSpec) m₂ i s τ em) := by
  unfold lookupFreshChalMemo
  exact foldl_orElse_append _ _ _

open Hyb12Align in
/-- Hit on the matching singleton entry (`gSpec` memo). -/
private lemma lookupResampleMemo_singleton_self
    (i : pSpec.ChallengeIdx) (s : StmtIn) (τ : Vector U δ)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (u : Vector U (challengeSize (pSpec := pSpec) i)) :
    lookupResampleMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      [⟨i, s, τ, em, u⟩] i s τ em = some u := by
  unfold lookupResampleMemo
  simp only [List.foldl_cons, List.foldl_nil]
  rw [none_orElse_apply]
  simp

open Hyb12Align in
/-- Miss on a non-matching singleton entry (`gSpec` memo). -/
private lemma lookupResampleMemo_singleton_ne
    (i i' : pSpec.ChallengeIdx) (s s' : StmtIn) (τ τ' : Vector U δ)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (em' : pSpec.EncodedMessagesBefore U i'.1.castSucc)
    (u : Vector U (challengeSize (pSpec := pSpec) i))
    (hq : (⟨i, s, τ, em⟩ : (gSpec (U := U) StmtIn pSpec δ).Domain) ≠ ⟨i', s', τ', em'⟩) :
    lookupResampleMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      [⟨i, s, τ, em, u⟩] i' s' τ' em' = none := by
  unfold lookupResampleMemo
  simp only [List.foldl_cons, List.foldl_nil]
  rw [none_orElse_apply]
  by_cases hi : i = i'
  · subst hi
    rw [dif_pos (show (⟨i, s, τ, em, u⟩ :
      Hyb12Align.ResampleMemoEntry StmtIn U δ pSpec).roundIdx = i from rfl)]
    change (if s = s' ∧ τ = τ' ∧ em = em' then some u else none) = none
    refine if_neg fun hcon => hq ?_
    obtain ⟨h1, h2, h3⟩ := hcon
    subst h1; subst h2; subst h3; rfl
  · exact dif_neg hi

open Hyb12Align in
/-- First-match append split for the `gSpec` memo lookup. -/
private lemma lookupResampleMemo_append
    (m₁ m₂ : ResampleMemo StmtIn U δ pSpec)
    (i : pSpec.ChallengeIdx) (s : StmtIn) (τ : Vector U δ)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    lookupResampleMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
        (m₁ ++ m₂) i s τ em
      = Option.orElse
          (lookupResampleMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
            m₁ i s τ em)
          (fun _ => lookupResampleMemo (StmtIn := StmtIn) (U := U) (δ := δ)
            (pSpec := pSpec) m₂ i s τ em) := by
  unfold lookupResampleMemo
  exact foldl_orElse_append _ _ _

/-- The `eSpec`-keyed memo lookup, bundled to the sigma domain. -/
noncomputable def eLook (m : List (Hyb12Accounting.FreshChalMemoEntry StmtIn U δ pSpec))
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain) :
    Option ((eSpec (U := U) StmtIn pSpec δ).Range q) :=
  Hyb12Accounting.lookupFreshChalMemo m q.1 q.2.1 q.2.2.1 q.2.2.2

/-- The `eSpec`-keyed memo extension, bundled to the sigma domain. -/
def eExt (m : List (Hyb12Accounting.FreshChalMemoEntry StmtIn U δ pSpec))
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain)
    (u : (eSpec (U := U) StmtIn pSpec δ).Range q) :
    List (Hyb12Accounting.FreshChalMemoEntry StmtIn U δ pSpec) :=
  m ++ [⟨q.1, q.2.1, q.2.2.1, q.2.2.2, u⟩]

/-- The `gSpec`-keyed memo lookup, bundled to the sigma domain. -/
noncomputable def gLook (m : Hyb12Align.ResampleMemo StmtIn U δ pSpec)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    Option ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
  Hyb12Align.lookupResampleMemo m q.1 q.2.1 q.2.2.1 q.2.2.2

/-- The `gSpec`-keyed memo extension, bundled to the sigma domain. -/
def gExt (m : Hyb12Align.ResampleMemo StmtIn U δ pSpec)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (u : (gSpec (U := U) StmtIn pSpec δ).Range q) :
    Hyb12Align.ResampleMemo StmtIn U δ pSpec :=
  m ++ [⟨q.1, q.2.1, q.2.2.1, q.2.2.2, u⟩]

/-- First-read law for the `eSpec` memo: extending at a fresh key makes it a hit. -/
lemma eLook_eExt_self (m : List (Hyb12Accounting.FreshChalMemoEntry StmtIn U δ pSpec))
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain)
    (u : (eSpec (U := U) StmtIn pSpec δ).Range q)
    (hmiss : eLook (δ := δ) m q = none) :
    eLook (δ := δ) (eExt (δ := δ) m q u) q = some u := by
  unfold eLook at hmiss ⊢
  unfold eExt
  rw [lookupFreshChalMemo_append]
  refine Eq.trans (orElse_eq_of_none hmiss _) ?_
  exact lookupFreshChalMemo_singleton_self (δ := δ) q.1 q.2.1 q.2.2.1 q.2.2.2 u

/-- Extension law for the `eSpec` memo: other keys are unaffected. -/
lemma eLook_eExt_ne (m : List (Hyb12Accounting.FreshChalMemoEntry StmtIn U δ pSpec))
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain)
    (u : (eSpec (U := U) StmtIn pSpec δ).Range q)
    (q' : (eSpec (U := U) StmtIn pSpec δ).Domain) (hq : q ≠ q') :
    eLook (δ := δ) (eExt (δ := δ) m q u) q' = eLook (δ := δ) m q' := by
  unfold eLook eExt
  rw [lookupFreshChalMemo_append]
  exact Eq.trans
    (orElse_eq_self_of_none
      (lookupFreshChalMemo_singleton_ne (δ := δ) q.1 q'.1 q.2.1 q'.2.1 q.2.2.1 q'.2.2.1
        q.2.2.2 q'.2.2.2 u hq))
    rfl

/-- First-read law for the `gSpec` memo. -/
lemma gLook_gExt_self (m : Hyb12Align.ResampleMemo StmtIn U δ pSpec)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (u : (gSpec (U := U) StmtIn pSpec δ).Range q)
    (hmiss : gLook (δ := δ) m q = none) :
    gLook (δ := δ) (gExt (δ := δ) m q u) q = some u := by
  unfold gLook at hmiss ⊢
  unfold gExt
  rw [lookupResampleMemo_append]
  refine Eq.trans (orElse_eq_of_none hmiss _) ?_
  exact lookupResampleMemo_singleton_self (δ := δ) q.1 q.2.1 q.2.2.1 q.2.2.2 u

/-- Extension law for the `gSpec` memo. -/
lemma gLook_gExt_ne (m : Hyb12Align.ResampleMemo StmtIn U δ pSpec)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (u : (gSpec (U := U) StmtIn pSpec δ).Range q)
    (q' : (gSpec (U := U) StmtIn pSpec δ).Domain) (hq : q ≠ q') :
    gLook (δ := δ) (gExt (δ := δ) m q u) q' = gLook (δ := δ) m q' := by
  unfold gLook gExt
  rw [lookupResampleMemo_append]
  exact Eq.trans
    (orElse_eq_self_of_none
      (lookupResampleMemo_singleton_ne (δ := δ) q.1 q'.1 q.2.1 q'.2.1 q.2.2.1 q'.2.2.1
        q.2.2.2 q'.2.2.2 u hq))
    rfl

/-- The empty `eSpec` memo misses everywhere. -/
lemma eLook_nil (q : (eSpec (U := U) StmtIn pSpec δ).Domain) :
    eLook (δ := δ) (StmtIn := StmtIn) (U := U) (pSpec := pSpec) [] q = none := rfl

/-- The empty `gSpec` memo misses everywhere. -/
lemma gLook_nil (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    gLook (δ := δ) (StmtIn := StmtIn) (U := U) (pSpec := pSpec) [] q = none := rfl

end MemoLaws

/-! ## Sampler uniformity bridges -/

section Samplers

/-- Two `SampleableType` carriers of the same finite type sample identically. -/
private lemma evalDist_uniformSample_congr {T : Type} [Fintype T]
    (h1 h2 : SampleableType T) :
    𝒟[(@uniformSample T h1)] = 𝒟[(@uniformSample T h2)] := by
  refine evalDist_ext fun x => ?_
  rw [probOutput_uniformSample, probOutput_uniformSample]

/-- `uniformChallengeSampler` is the uniform per-key sampler of the `eSpec` ranges. -/
lemma hsampE (q : (eSpec (U := U) StmtIn pSpec δ).Domain) :
    𝒟[Hyb12Accounting.uniformChallengeSampler (pSpec := pSpec) q.1]
      = 𝒟[($ᵗ ((eSpec (U := U) StmtIn pSpec δ).Range q) : ProbComp _)] := by
  unfold Hyb12Accounting.uniformChallengeSampler
  exact evalDist_uniformSample_congr _ _

/-- The encoded-block sampler is the uniform per-key sampler of the `gSpec` ranges. -/
lemma hsampG (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    𝒟[($ᵗ (Vector U (challengeSize (pSpec := pSpec) q.1)) : ProbComp _)]
      = 𝒟[($ᵗ ((gSpec (U := U) StmtIn pSpec δ).Range q) : ProbComp _)] :=
  evalDist_uniformSample_congr _ _

end Samplers

/-! ## B1 — `Hyb2FreshAlignResidual` closed outright -/

section Hyb2Align

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The instantiated lazy implementation over the `eSpec` world **is** the fresh-game
implementation of `Hyb12Accounting` at the uniform sampler. -/
lemma lazyGameImpl_eSpec_eq_freshGameImpl [SampleableType U]
    (oImpl : QueryImpl oSpec ProbComp) :
    lazyGameImpl (U := U) (eLook (StmtIn := StmtIn) (U := U) (pSpec := pSpec) (δ := δ))
        (eExt (δ := δ))
        (fun q => Hyb12Accounting.uniformChallengeSampler (pSpec := pSpec) q.1) oImpl
      = Hyb12Accounting.freshGameImpl (δ := δ)
          (Hyb12Accounting.uniformChallengeSampler (pSpec := pSpec)) oImpl := by
  funext t
  match t with
  | .inl qo => rfl
  | .inr (.inl qe) => rfl
  | .inr (.inr (.inl qu)) => rfl
  | .inr (.inr (.inr mi)) => rfl

set_option maxHeartbeats 1600000 in
-- the congruence decomposition compares full hybrid-game skeletons leafwise
/-- **B1, equality form**: `Hyb₂` (eager uniform `eSpec` table) IS the fresh pivot game at
the uniform sampler (lazily-memoized table). -/
theorem hyb2_eq_hyb2GameFresh_uniform [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Hyb2 T_H T_P δ oImpl V P
      = 𝒟[Hyb12Accounting.hyb2GameFresh T_H T_P δ
          (Hyb12Accounting.uniformChallengeSampler (pSpec := pSpec)) oImpl V P] := by
  refine Eq.trans
    (evalDist_hybGameEager_uniform_eq_hybGameLazy (T_H := T_H) (T_P := T_P)
      (chSpec := eSpec (U := U) StmtIn pSpec δ)
      (eLook (δ := δ)) (eExt (δ := δ))
      (fun q => Hyb12Accounting.uniformChallengeSampler (pSpec := pSpec) q.1)
      (fun q => hsampE q) (eLook_eExt_self (δ := δ)) (eLook_eExt_ne (δ := δ))
      (m₀ := ([] : List (Hyb12Accounting.FreshChalMemoEntry StmtIn U δ pSpec)))
      (fun q => eLook_nil q) δ
      (gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ))
      (hyb2Line4TraceEager (δ := δ)) oImpl V P) ?_
  refine congrArg (fun z => 𝒟[z]) ?_
  unfold hybGameLazy Hyb12Accounting.hyb2GameFresh
    Hyb12Accounting.proverPipeline Hyb12Accounting.verifierPipeline
  simp only [lazyGameImpl_eSpec_eq_freshGameImpl]
  refine bind_congr fun x => ?_
  rcases x with ⟨⟨pRes?, pLog⟩, mm⟩
  rcases pRes? with _ | r
  · rfl
  · refine bind_congr fun y => ?_
    rcases y with ⟨⟨vRes?, vLog⟩, mm2⟩
    rcases vRes? with _ | vr
    · rfl
    · rcases vr with ⟨⟨stmtOut?, st2⟩, st3⟩
      rcases stmtOut? with _ | stmtOut
      · rfl
      · refine bind_congr fun pLog'? => ?_
        refine bind_congr fun vLog'? => ?_
        rcases pLog'? with _ | pLog' <;> rcases vLog'? with _ | vLog' <;> rfl

/-- **B1 (CO25 Claim 5.22 eager↔lazy alignment leg, CLOSED)**: the once-sampled eager
uniform `eSpec` table of `Hyb₂` equals its lazily-memoized per-query sampling view —
`Hyb12Accounting.Hyb2FreshAlignResidual` holds unconditionally. -/
theorem hyb2FreshAlign_holds [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) :
    Hyb12Accounting.Hyb2FreshAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P
  rw [hyb2_eq_hyb2GameFresh_uniform T_H T_P δ oImpl V P]
  exact SPMF.tvDist_self _

end Hyb2Align

/-! ## The `gSpec`-side lazy-table forms (eager tables eliminated from legs A/B2) -/

section GSpecLazy

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The per-key encoded-block sampler for the lazy `gSpec` table. -/
noncomputable def gSamp (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    ProbComp ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
  ($ᵗ (Vector U (challengeSize (pSpec := pSpec) q.1)) : ProbComp _)

/-- The lazy-table form of `Hyb₁` (forward realization, `Hyb₁` line-4 map, `gSpec` table
sampled lazily). -/
noncomputable def Hyb1Lazy [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameLazy (oSpec := oSpec) (StmtOut := StmtOut)
      (gLook (δ := δ)) (gExt (δ := δ)) (gSamp (δ := δ))
      ([] : Hyb12Align.ResampleMemo StmtIn U δ pSpec) T_H T_P δ
      (gImplEncodedForward (StmtIn := StmtIn) (δ := δ))
      (hyb1Line4TraceEager (δ := δ)) oImpl V P]

/-- The lazy-table form of `Hyb12Mid` (per-query fiber resampler, `Hyb₁` line-4 map,
`gSpec` table sampled lazily). -/
noncomputable def Hyb12MidLazy [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameLazy (oSpec := oSpec) (StmtOut := StmtOut)
      (gLook (δ := δ)) (gExt (δ := δ)) (gSamp (δ := δ))
      ([] : Hyb12Align.ResampleMemo StmtIn U δ pSpec) T_H T_P δ
      (gImplEncodedResampled (StmtIn := StmtIn) (δ := δ))
      (hyb1Line4TraceEager (δ := δ)) oImpl V P]

/-- The lazy-table form of `Hyb12MidMemo` (memoized fiber redraws, `Hyb₁` line-4 map,
`gSpec` table sampled lazily). -/
noncomputable def Hyb12MidMemoLazy [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameLazy (oSpec := oSpec) (StmtOut := StmtOut)
      (gLook (δ := δ)) (gExt (δ := δ)) (gSamp (δ := δ))
      ([] : Hyb12Align.ResampleMemo StmtIn U δ pSpec) T_H T_P δ
      (Hyb12Align.gImplEncodedResampledMemo (StmtIn := StmtIn) (δ := δ))
      (hyb1Line4TraceEager (δ := δ)) oImpl V P]

/-- `Hyb₁`'s eager `gSpec` table eliminated (PROVEN). -/
theorem hyb1_eq_hyb1Lazy [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Hyb1 T_H T_P δ oImpl V P = Hyb1Lazy T_H T_P δ oImpl V P :=
  evalDist_hybGameEager_uniform_eq_hybGameLazy (T_H := T_H) (T_P := T_P)
    (chSpec := gSpec (U := U) StmtIn pSpec δ)
    (gLook (δ := δ)) (gExt (δ := δ)) (gSamp (δ := δ))
    (fun q => hsampG q) (gLook_gExt_self (δ := δ)) (gLook_gExt_ne (δ := δ))
    (fun q => gLook_nil q) δ
    (gImplEncodedForward (StmtIn := StmtIn) (δ := δ))
    (hyb1Line4TraceEager (δ := δ)) oImpl V P

/-- `Hyb12Mid`'s eager `gSpec` table eliminated (PROVEN) — the eager↔lazy half of the B2
alignment leg. -/
theorem hyb12Mid_eq_hyb12MidLazy [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Hyb12Mid T_H T_P δ oImpl V P = Hyb12MidLazy T_H T_P δ oImpl V P :=
  evalDist_hybGameEager_uniform_eq_hybGameLazy (T_H := T_H) (T_P := T_P)
    (chSpec := gSpec (U := U) StmtIn pSpec δ)
    (gLook (δ := δ)) (gExt (δ := δ)) (gSamp (δ := δ))
    (fun q => hsampG q) (gLook_gExt_self (δ := δ)) (gLook_gExt_ne (δ := δ))
    (fun q => gLook_nil q) δ
    (gImplEncodedResampled (StmtIn := StmtIn) (δ := δ))
    (hyb1Line4TraceEager (δ := δ)) oImpl V P

/-- `Hyb12MidMemo`'s eager `gSpec` table eliminated (PROVEN). -/
theorem hyb12MidMemo_eq_hyb12MidMemoLazy [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Hyb12Align.Hyb12MidMemo T_H T_P δ oImpl V P
      = Hyb12MidMemoLazy T_H T_P δ oImpl V P :=
  evalDist_hybGameEager_uniform_eq_hybGameLazy (T_H := T_H) (T_P := T_P)
    (chSpec := gSpec (U := U) StmtIn pSpec δ)
    (gLook (δ := δ)) (gExt (δ := δ)) (gSamp (δ := δ))
    (fun q => hsampG q) (gLook_gExt_self (δ := δ)) (gLook_gExt_ne (δ := δ))
    (fun q => gLook_nil q) δ
    (Hyb12Align.gImplEncodedResampledMemo (StmtIn := StmtIn) (δ := δ))
    (hyb1Line4TraceEager (δ := δ)) oImpl V P

end GSpecLazy

/-! ## The finer residuals and the proven reductions for B2 / A -/

section Residuals

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Finer residual (B2 core) — **cross-spec re-keying between lazy games**
(`Δ(Hyb12MidLazy, hyb2GameFresh (ψ ∘ 𝒰)) = 0`): the lazily-tabled `Hyb12Mid` (lazy `gSpec`
table, per-query `ψ⁻¹`-fiber resampler, `(φ⁻¹, ψ)` line-4 map) equals the fresh pivot at
the decoded sampler (lazy decoded memo, `ψ⁻¹`-fiber sampling realization, `φ⁻¹` line-4
map). Strictly finer than `Hyb12MidFreshAlignResidual`: **no eager table remains on either
side** — the open content is purely the `gSpec → eSpec` world re-keying coupling through
the `d2sQueryImpl` dispatcher (per fresh derivation this is the proven
`Hyb12Step.tvDist_gImplEncodedForward_gImplDecodedChallenge_le` coupling shape with the
challenge marginal fixed). -/
def Hyb12MidCrossSpecAlignResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb12MidLazy T_H T_P δ oImpl V P)
      𝒟[Hyb12Accounting.hyb2GameFresh T_H T_P δ
          (Hyb12Accounting.decodedChallengeSampler (U := U) (pSpec := pSpec))
          oImpl V P] = 0

/-- **Proven reduction (B2)**: the cross-spec lazy coupling residual implies the full
`Hyb12MidFreshAlignResidual` — the eager↔lazy half is discharged by
`hyb12Mid_eq_hyb12MidLazy`. -/
theorem hyb12MidFreshAlign_of_crossSpecAlign [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hX : Hyb12MidCrossSpecAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl) :
    Hyb12Accounting.Hyb12MidFreshAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P
  rw [hyb12Mid_eq_hyb12MidLazy T_H T_P δ oImpl V P]
  exact hX V P

/-- Finer residual (A core) — **all-lazy fiber-redraw coupling**
(`Δ(Hyb1Lazy, Hyb12MidMemoLazy) = 0`): against the *lazily sampled* common `gSpec` table,
the forward realization equals the memoized fiber-redraw realization. Strictly finer than
`Hyb12LazyEagerResampleResidual`: **both eager tables are eliminated** — what remains is
the coupling of the two `gᵢ`-realizations inside the dispatcher (per fresh key the laws
match by `Hyb12Align.evalDist_fiberResampleSampler` and `ψ`-invariance of the line-4 map;
repeats are served consistently by both memos). -/
def Hyb12LazyRedrawCouplingResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb1Lazy T_H T_P δ oImpl V P)
      (Hyb12MidMemoLazy T_H T_P δ oImpl V P) = 0

/-- **Proven reduction (A)**: the all-lazy redraw coupling residual implies the full
`Hyb12LazyEagerResampleResidual` — both eager tables are discharged by
`hyb1_eq_hyb1Lazy` and `hyb12MidMemo_eq_hyb12MidMemoLazy`. -/
theorem hyb12LazyEagerResample_of_redrawCoupling [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hX : Hyb12LazyRedrawCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl) :
    Hyb12Align.Hyb12LazyEagerResampleResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P
  rw [hyb1_eq_hyb1Lazy T_H T_P δ oImpl V P,
    hyb12MidMemo_eq_hyb12MidMemoLazy T_H T_P δ oImpl V P]
  exact hX V P

/-- **The round-4 Claim 5.22 frontier (PROVEN assembly)**: with B1 closed outright
(`hyb2FreshAlign_holds`) and the A/B2 alignment legs reduced to their all-lazy cores, the
full `Hyb12StepResidual` (CO25 Claim 5.22, Eq. 53) follows from **five** residuals — the
all-lazy redraw coupling, the repeat-derivation memo transparency, the cross-spec lazy
re-keying, and the two pipeline budgets. Strictly finer than the round-3 six-residual
frontier (`KeyLemmaFrontierRound3.hyb12Step_of_finestResiduals`): one residual fewer and
no eager table left in any alignment leg. -/
theorem hyb12Step_of_lazyResiduals [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hRedraw : Hyb12LazyRedrawCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hRepeat : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hCross : Hyb12MidCrossSpecAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hProv : Hyb12Accounting.Hyb12ProverPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) T_H T_P δ)
    (hVerif : Hyb12Accounting.Hyb12VerifierPipelineBudgetResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  Hyb12Step.hyb12Step_of_resampleSplit T_H T_P δ oImpl
    (Hyb12Align.hyb12ResampleAlign_of_lazySplit T_H T_P δ oImpl
      (hyb12LazyEagerResample_of_redrawCoupling T_H T_P δ oImpl hRedraw) hRepeat)
    (Hyb12Accounting.hyb12BiasAccounting_of_freshPipeline T_H T_P δ oImpl
      (hyb12MidFreshAlign_of_crossSpecAlign T_H T_P δ oImpl hCross)
      (hyb2FreshAlign_holds T_H T_P δ oImpl) hProv hVerif)

end Residuals

end DuplexSpongeFS.Hyb12EagerLazy

#print axioms DuplexSpongeFS.Hyb12EagerLazy.evalDist_uniformSample_bind_const
#print axioms DuplexSpongeFS.Hyb12EagerLazy.memoOverlay_ext_of_none
#print axioms DuplexSpongeFS.Hyb12EagerLazy.memoOverlay_update_read
#print axioms DuplexSpongeFS.Hyb12EagerLazy.memoOverlay_of_forall_none
#print axioms DuplexSpongeFS.Hyb12EagerLazy.evalDist_simulateQ_lazyGameImpl_run_bind_eq_eager
#print axioms DuplexSpongeFS.Hyb12EagerLazy.evalDist_lazyGame_twoStage_eq_eager
#print axioms DuplexSpongeFS.Hyb12EagerLazy.evalDist_hybGameEager_uniform_eq_hybGameLazy
#print axioms DuplexSpongeFS.Hyb12EagerLazy.eLook_eExt_self
#print axioms DuplexSpongeFS.Hyb12EagerLazy.eLook_eExt_ne
#print axioms DuplexSpongeFS.Hyb12EagerLazy.gLook_gExt_self
#print axioms DuplexSpongeFS.Hyb12EagerLazy.gLook_gExt_ne
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hsampE
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hsampG
#print axioms DuplexSpongeFS.Hyb12EagerLazy.lazyGameImpl_eSpec_eq_freshGameImpl
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb2_eq_hyb2GameFresh_uniform
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb2FreshAlign_holds
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb1_eq_hyb1Lazy
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb12Mid_eq_hyb12MidLazy
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb12MidMemo_eq_hyb12MidMemoLazy
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb12MidFreshAlign_of_crossSpecAlign
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb12LazyEagerResample_of_redrawCoupling
#print axioms DuplexSpongeFS.Hyb12EagerLazy.hyb12Step_of_lazyResiduals

end
