/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaHybrids

/-!
# CO25 Claim 5.22 — codec decoding bias for `Hyb₁ → Hyb₂`: per-query coupling + lifting

This module attacks `KeyLemmaHybrids.Hyb12StepResidual` (CO25 Claim 5.22, Eq. 53), the
`Hyb₁ → Hyb₂` step of the §5.8 ladder: switching the encoded challenge functions
`g = (gᵢ)ᵢ ← 𝒟_Σ` (uniform encoded blocks, `Hyb₁`'s `gImplEncodedForward`) for the decoded
challenge functions with `ψ⁻¹`-preimage sampling (`e ← 𝒟_e` + `uniformDeserializePreimage`,
`Hyb₂`'s `gImplDecodedChallenge`) costs the codec decoding bias `ε_cdc,i` once per challenge
derivation.

## Proven here (no `sorry`, axiom-clean)

Two reusable generic layers and their DSFS instantiations:

1. **Impl-closeness lifting** (the reusable accumulation brick):
   - `pmf_tvDist_bind_left_le_of_forall` / `spmf_tvDist_bind_left_le_of_forall`: binding
     pointwise-`c`-close continuation kernels over a common base moves total variation by at
     most `c` (the `PMF`/`SPMF` bind-left counterpart of VCVio's `tvDist_bind_right_le`).
   - `tvDist_evalDist_simulateQ_le_of_close`: **if two query implementations (into possibly
     different target oracle monads) answer every `p`-query within TV distance `ε` and agree
     in distribution elsewhere, then simulating any computation with at most `b` `p`-queries
     (`IsQueryBoundP`) moves total variation by at most `b · ε`.** This is the per-query →
     whole-game accumulation step of CO25 Claim 5.22. It is the **cross-monad,
     predicate-budgeted** complement of `Hyb01Step.tvDist_simulateQ_stateT_le_sum_of_step`
     (same-monad, stateful, size-indexed costs): the `Hyb₁`/`Hyb₂` worlds live over
     *different* challenge-oracle specs (`gSpec` vs `eSpec`), so the comparison must happen
     on the common `SPMF` output surface, and the bias is paid only on the `θ★`-budgeted
     derivation queries.

2. **Per-derivation coupling** (the analytic content of Eq. 53):
   - `map_bind_uniformFiber_eq_uniform`: resampling a uniform value inside its own
     `ψ`-fiber is the identity — `ψ(v), v ← 𝒰(V); v' ← 𝒰(ψ⁻¹(ψ(v)))` returns exactly
     `𝒰(V)` (the reason CO25 Claim 5.23's step is free, and the pivot for 5.22).
   - `tvDist_uniform_bind_uniformFiber_le`: data processing through the common
     `ψ⁻¹`-fiber-sampling kernel — `Δ(𝒰(V), ρ ← ν; 𝒰(ψ⁻¹(ρ))) ≤ Δ(ψ(𝒰(V)), ν)`.
   - `tvDist_uniformEncoded_decodedFiber_le_decodingBias`: instantiated at `ψ = ψᵢ` (the
     codec decoder) and `ν = 𝒰(ℳᵢ)`: **one fresh `Hyb₁` derivation (uniform encoded block)
     and one fresh `Hyb₂` derivation (uniform challenge, then uniform `ψᵢ⁻¹` preimage) are
     within `ε_cdc,i`** (`Codec.decode_isBiased` + `Codec.decode_surjective`).

3. **In-tree sampler semantics + the per-query coupling in `GImpl` shape**:
   - `probOutput_sampleFromList` / `evalDist_sampleFromList_toFinset` /
     `evalDist_uniformDeserializePreimage`: the §5.4 `ψ⁻¹` sampler is distributed exactly
     uniformly on the preimage finset (`𝒟[uniformDeserializePreimage ch] =
     𝒰(deserializePreimageFinset ch)`).
   - `tvDist_gImplEncodedForward_gImplDecodedChallenge_le`: the `Hyb₁` and `Hyb₂`
     `gᵢ`-realizations of `KeyLemmaHybrids`, run on a **single** query under the canonical
     i.i.d.-uniform oracle semantics, are within `ε_cdc,i` — CO25 Eq. 53, per derivation, in
     the exact in-tree shape.

## Open core (named `*Residual : Prop`, NOT proven) and the proven reduction

The remaining gap between the per-derivation coupling and the full `Hyb12StepResidual` is
instrumented through the pivot hybrid `Hyb12Mid` (`Hyb₁`'s game with the `gᵢ` answer
resampled inside its own `ψᵢ`-fiber, `gImplEncodedResampled`):

- `Hyb12ResampleAlignResidual` — `Δ(Hyb₁, Hyb12Mid) = 0`: fiber-resampling is invisible
  (per *fresh* derivation this is exactly `map_bind_uniformFiber_eq_uniform`; the residual
  content is the eager-table/no-repeated-derivation argument of CO25 §5.4, the same
  freshness analysis the `tr_i` memo exists for).
- `Hyb12BiasAccountingResidual` — `Δ(Hyb12Mid, Hyb₂) ≤ claim5_22Bound`: both sides now
  derive challenges by (challenge distribution, then the *same* `ψ⁻¹`-fiber kernel); they
  differ per derivation only in the challenge distribution (`ψᵢ(𝒰(Σ^ℓᵢ))` vs `𝒰(ℳᵢ)`),
  which `tvDist_uniformEncoded_decodedFiber_le_decodingBias` bounds by `ε_cdc,i` and
  `tvDist_evalDist_simulateQ_le_of_close` accumulates over the `θ★` prover-side derivations
  plus one per round on the verifier side (CO25 Eq. 53).
- **`hyb12Step_of_resampleSplit` (proven)**: the two residuals (in `εA + εB ≤ bound`
  generality, mirroring `VerifierReplay.hyb34Step_of_strictSplit`) assemble into the full
  `Hyb12StepResidual` by the TV triangle inequality.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb12Step

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open scoped NNReal ENNReal

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

universe u

/-! ## Generic `PMF`/`SPMF` bind-left closeness bricks

VCVio proves `tvDist_bind_right_le` (same continuation, different bases) and, for
`HasEvalPMF` monads only, a weighted bind-left bound. The bricks below give the *uniform*
bind-left bound on the `PMF`/`SPMF` surfaces directly, which is what the cross-monad
simulation lifting needs (the two hybrid worlds live over different oracle specs, so the
monadic `tvDist` API does not apply). -/

section BindLeftClose

/-- `etvDist` form of a real `tvDist` bound (the `ℝ≥0∞`-level carrier). -/
private lemma etvDist_le_ofReal_of_tvDist_le {α : Type u} {p q : PMF α} {c : ℝ}
    (h : p.tvDist q ≤ c) : p.etvDist q ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_toReal (PMF.etvDist_ne_top p q)]
  exact ENNReal.ofReal_le_ofReal h

/-- **Bind-left closeness for `PMF`**: binding two pointwise-`c`-close kernels over a common
base distribution moves total variation by at most `c`. -/
theorem pmf_tvDist_bind_left_le_of_forall {α β : Type u} (μ : PMF α) (F G : α → PMF β)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ a, PMF.tvDist (F a) (G a) ≤ c) :
    PMF.tvDist (μ.bind F) (μ.bind G) ≤ c := by
  have hETV : (μ.bind F).etvDist (μ.bind G) ≤ ENNReal.ofReal c := by
    rw [PMF.etvDist]
    have hpoint : ∀ b, ENNReal.absDiff ((μ.bind F) b) ((μ.bind G) b)
        ≤ ∑' a, ENNReal.absDiff ((F a) b) ((G a) b) * μ a := fun b => by
      rw [PMF.bind_apply, PMF.bind_apply]
      refine le_trans (ENNReal.absDiff_tsum_le _ _) (ENNReal.tsum_le_tsum fun a => ?_)
      calc ENNReal.absDiff (μ a * (F a) b) (μ a * (G a) b)
          = ENNReal.absDiff ((F a) b * μ a) ((G a) b * μ a) := by
            rw [mul_comm (μ a), mul_comm (μ a)]
        _ ≤ ENNReal.absDiff ((F a) b) ((G a) b) * μ a :=
            ENNReal.absDiff_mul_right_le _ _ _
    calc (∑' b, ENNReal.absDiff ((μ.bind F) b) ((μ.bind G) b)) / 2
        ≤ (∑' b, ∑' a, ENNReal.absDiff ((F a) b) ((G a) b) * μ a) / 2 :=
          ENNReal.div_le_div_right (ENNReal.tsum_le_tsum hpoint) 2
      _ = (∑' a, (∑' b, ENNReal.absDiff ((F a) b) ((G a) b)) * μ a) / 2 := by
          rw [ENNReal.tsum_comm]
          congr 1
          exact tsum_congr fun a => ENNReal.tsum_mul_right
      _ = ∑' a, ((F a).etvDist (G a)) * μ a := by
          rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun a => ?_
          rw [PMF.etvDist, div_eq_mul_inv]
          ring
      _ ≤ ∑' a, ENNReal.ofReal c * μ a :=
          ENNReal.tsum_le_tsum fun a =>
            mul_le_mul' (etvDist_le_ofReal_of_tvDist_le (h a)) le_rfl
      _ = ENNReal.ofReal c := by
          rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  calc PMF.tvDist (μ.bind F) (μ.bind G) = ((μ.bind F).etvDist (μ.bind G)).toReal :=
        PMF.tvDist_def _ _
    _ ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hETV
    _ = c := ENNReal.toReal_ofReal hc

/-- **Bind-left closeness for `SPMF`**: as `pmf_tvDist_bind_left_le_of_forall`, on the
sub-probability surface (failure mass is carried identically through both sides). -/
theorem spmf_tvDist_bind_left_le_of_forall {α β : Type u} (μ : SPMF α) (F G : α → SPMF β)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ a, SPMF.tvDist (F a) (G a) ≤ c) :
    SPMF.tvDist (μ >>= F) (μ >>= G) ≤ c := by
  unfold SPMF.tvDist
  rw [SPMF.toPMF_bind, SPMF.toPMF_bind]
  unfold Option.elimM
  rw [PMF.monad_bind_eq_bind, PMF.monad_bind_eq_bind]
  refine pmf_tvDist_bind_left_le_of_forall _ _ _ hc fun o => ?_
  cases o with
  | none => simpa using hc
  | some a => exact h a

/-- TV distance between `PMF`s lifted into `SPMF` is bounded by the `PMF` TV distance
(data processing along `Option.some`). -/
theorem spmf_tvDist_liftM_le {α : Type u} (p q : PMF α) :
    SPMF.tvDist (liftM p) (liftM q) ≤ PMF.tvDist p q := by
  unfold SPMF.tvDist
  rw [SPMF.liftM_eq_map, SPMF.liftM_eq_map, SPMF.toPMF_mk, SPMF.toPMF_mk,
    ← PMF.monad_map_eq_map, ← PMF.monad_map_eq_map]
  exact PMF.tvDist_map_le some p q

/-- Binding lifted kernels over a lifted base is the lift of the `PMF` bind. -/
lemma spmf_liftM_bind {α β : Type u} (p : PMF α) (k : α → PMF β) :
    ((liftM p : SPMF α) >>= fun a => liftM (k a)) = (liftM (p.bind k) : SPMF β) := by
  refine SPMF.ext fun b => ?_
  rw [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, PMF.bind_apply]
  exact tsum_congr fun a => by rw [SPMF.liftM_apply, SPMF.liftM_apply]

end BindLeftClose

/-! ## The impl-closeness lifting brick (per-query → whole-computation accumulation)

The CO25 §5.8 steps repeatedly replace one per-query answering process by another that is
close per query; the cost accumulates over the query budget. This is the generic carrier:
the two implementations may land in **different** oracle monads (here: the `Hyb₁` world over
`gSpec` and the `Hyb₂` world over `eSpec`), so the bound is stated on the common `SPMF`
output surface via `𝒟[·]`. -/

section LiftingBrick

/-- **Impl-closeness lifting**: if `impl₁`/`impl₂` answer every query at a `p`-index within
total variation `ε` (and are distributionally identical at `¬p`-indices), then simulating
any computation that makes at most `b` `p`-queries moves the output distribution by at most
`b · ε`. The two implementations may target different oracle specs. -/
theorem tvDist_evalDist_simulateQ_le_of_close
    {ι₁ ι₂ ι₃ : Type u} {spec : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec₃ : OracleSpec ι₃}
    [spec₂.Fintype] [spec₂.Inhabited] [spec₃.Fintype] [spec₃.Inhabited]
    {impl₁ : QueryImpl spec (OracleComp spec₂)} {impl₂ : QueryImpl spec (OracleComp spec₃)}
    {p : ι₁ → Prop} [DecidablePred p] {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ t, SPMF.tvDist 𝒟[impl₁ t] 𝒟[impl₂ t] ≤ if p t then ε else 0)
    {α : Type u} {oa : OracleComp spec α} {b : ℕ}
    (h : IsQueryBoundP oa p b) :
    SPMF.tvDist 𝒟[simulateQ impl₁ oa] 𝒟[simulateQ impl₂ oa] ≤ b * ε := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure x =>
      simp only [simulateQ_pure, evalDist_pure]
      rw [SPMF.tvDist_self]
      exact mul_nonneg (Nat.cast_nonneg b) hε
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      obtain ⟨hcan, hrest⟩ := h
      rw [simulateQ_query_bind, simulateQ_query_bind]
      -- `liftM`/`(query t).cont` are definitional no-ops; establish the bound for the
      -- normalized form and close by defeq
      have hmain : SPMF.tvDist
          𝒟[(impl₁ t) >>= fun u => simulateQ impl₁ (mx u)]
          𝒟[(impl₂ t) >>= fun u => simulateQ impl₂ (mx u)] ≤ (b : ℝ) * ε := by
        rw [evalDist_bind, evalDist_bind]
        have h₁ : SPMF.tvDist
            (𝒟[impl₁ t] >>= fun u => 𝒟[simulateQ impl₁ (mx u)])
            (𝒟[impl₂ t] >>= fun u => 𝒟[simulateQ impl₁ (mx u)])
            ≤ if p t then ε else 0 :=
          le_trans (SPMF.tvDist_bind_right_le _ _ _) (hclose t)
        have h₂ : SPMF.tvDist
            (𝒟[impl₂ t] >>= fun u => 𝒟[simulateQ impl₁ (mx u)])
            (𝒟[impl₂ t] >>= fun u => 𝒟[simulateQ impl₂ (mx u)])
            ≤ ((if p t then b - 1 else b : ℕ) : ℝ) * ε :=
          spmf_tvDist_bind_left_le_of_forall _ _ _
            (mul_nonneg (Nat.cast_nonneg _) hε) fun u => ih u (hrest u)
        have htri := SPMF.tvDist_triangle
          (𝒟[impl₁ t] >>= fun u => 𝒟[simulateQ impl₁ (mx u)])
          (𝒟[impl₂ t] >>= fun u => 𝒟[simulateQ impl₁ (mx u)])
          (𝒟[impl₂ t] >>= fun u => 𝒟[simulateQ impl₂ (mx u)])
        by_cases hpt : p t
        · have hb : 0 < b := hcan.resolve_left (not_not_intro hpt)
          rw [if_pos hpt] at h₁ h₂
          have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
            rw [Nat.cast_sub hb]
            norm_num
          rw [hcast] at h₂
          have hring : ((b : ℝ) - 1) * ε + ε = (b : ℝ) * ε := by ring
          linarith
        · rw [if_neg hpt] at h₁ h₂
          linarith
      exact hmain

end LiftingBrick

/-! ## Per-derivation coupling: uniform fiber resampling and the decoding-bias bound

The analytic core of CO25 Eq. 53: for a surjection `ψ : V → M` (the codec decoder
`ψᵢ : Σ^{ℓ_V(i)} → ℳ_{V,i}`), sampling `ρ ← ν` and then a uniform `ψ`-preimage of `ρ`
deviates from `𝒰(V)` by at most `Δ(ψ(𝒰(V)), ν)` — and at `ν = 𝒰(ℳ)` that distance is the
codec decoding bias (`Codec.decode_isBiased`). -/

section FiberResampling

variable {V M : Type u} [Fintype V] [Nonempty V] [DecidableEq M]

/-- Fibers of a surjection are nonempty finsets. (Fiber orientation `ρ = ψ v`, matching the
classical `if`-orientation of `PMF.map_apply`.) -/
lemma fiber_nonempty {ψ : V → M} (hψ : Function.Surjective ψ) (ρ : M) :
    (Finset.univ.filter fun v => ρ = ψ v).Nonempty := by
  obtain ⟨v, hv⟩ := hψ ρ
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv.symm⟩⟩

/-- **Fiber resampling is invisible on uniform**: pushing `𝒰(V)` through `ψ` and then
sampling a uniform `ψ`-preimage returns exactly `𝒰(V)`. (The pivot identity of the
`Hyb₁ → Hyb₂` analysis, and the reason the Claim 5.23 step is exactly `0`.) -/
theorem map_bind_uniformFiber_eq_uniform {ψ : V → M} (hψ : Function.Surjective ψ) :
    (((PMF.uniformOfFintype V).map ψ).bind fun ρ =>
        PMF.uniformOfFinset (Finset.univ.filter fun v => ρ = ψ v) (fiber_nonempty hψ ρ))
      = PMF.uniformOfFintype V := by
  ext v
  rw [PMF.bind_apply]
  have hzero : ∀ ρ, ρ ≠ ψ v →
      ((PMF.uniformOfFintype V).map ψ) ρ *
        PMF.uniformOfFinset (Finset.univ.filter fun w => ρ = ψ w)
          (fiber_nonempty hψ ρ) v = 0 := by
    intro ρ hρ
    have hv : v ∉ Finset.univ.filter fun w => ρ = ψ w := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hvv => hρ hvv
    rw [PMF.uniformOfFinset_apply_of_notMem _ hv, mul_zero]
  have hvmem : v ∈ Finset.univ.filter fun w => ψ v = ψ w :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, rfl⟩
  rw [tsum_eq_single (ψ v) hzero, PMF.map_apply,
    PMF.uniformOfFinset_apply_of_mem _ hvmem]
  simp only [PMF.uniformOfFintype_apply]
  rw [tsum_fintype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hn0 : (((Finset.univ.filter fun w => ψ v = ψ w).card : ℝ≥0∞)) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    exact ⟨v, hvmem⟩
  rw [mul_right_comm, ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top _), one_mul]

/-- **Data processing through the fiber-sampling kernel**: the distance between `𝒰(V)` and
"`ρ ← ν`, then a uniform `ψ`-preimage of `ρ`" is at most the distance between the
pushforward `ψ(𝒰(V))` and `ν`. -/
theorem tvDist_uniform_bind_uniformFiber_le {ψ : V → M} (hψ : Function.Surjective ψ)
    (ν : PMF M) :
    PMF.tvDist (PMF.uniformOfFintype V)
      (ν.bind fun ρ =>
        PMF.uniformOfFinset (Finset.univ.filter fun v => ρ = ψ v) (fiber_nonempty hψ ρ))
    ≤ PMF.tvDist ((PMF.uniformOfFintype V).map ψ) ν := by
  nth_rewrite 1 [← map_bind_uniformFiber_eq_uniform hψ]
  exact PMF.tvDist_bind_right_le _ _ _

/-- TV distance is at most the `L¹` distance on finite `PMF`s (the `Dist (PMF ·)` instance
of `Serde.lean`, against which `Codec.decode_isBiased` is stated): `tvDist = L¹/2 ≤ L¹`. -/
lemma pmf_tvDist_le_l1 {α : Type u} [Fintype α] (p q : PMF α) :
    PMF.tvDist p q ≤ ∑ x, |(p x).toReal - (q x).toReal| := by
  have hne : ∀ x, ENNReal.absDiff (p x) (q x) ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top p x, PMF.apply_ne_top q x⟩)
      (ENNReal.absDiff_le_add _ _)
  rw [PMF.tvDist_def, PMF.etvDist, tsum_fintype, ENNReal.toReal_div]
  have hsum : (∑ x, ENNReal.absDiff (p x) (q x)).toReal
      = ∑ x, |(p x).toReal - (q x).toReal| := by
    rw [ENNReal.toReal_sum fun x _ => hne x]
    exact Finset.sum_congr rfl fun x _ =>
      ENNReal.absDiff_toReal (PMF.apply_ne_top p x) (PMF.apply_ne_top q x)
  rw [hsum]
  have hnonneg : (0 : ℝ) ≤ ∑ x, |(p x).toReal - (q x).toReal| :=
    Finset.sum_nonneg fun x _ => abs_nonneg _
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [h2]
  linarith

end FiberResampling

/-! ## DSFS context -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {δ : ℕ}

/-- `SpongeUnit` provides `Zero`; expose the canonical `Inhabited` locally (needed for the
`OracleSpec.Inhabited` instances of the `gSpec`/`eSpec` sum specs). Not exported. -/
local instance : Inhabited U := ⟨0⟩

/-- Local `VCVCompatible U` (from `Fintype`/`Inhabited`/`DecidableEq` in context), giving
`Fintype (Vector U n)` via `Vector.instFintype`. Not exported. -/
local instance : VCVCompatible U where
  type_decidableEq' := inferInstance

/-- Local `Inhabited` for encoded blocks (needed for the `OracleSpec.Inhabited` instance of
the `gSpec` sum spec). Not exported. -/
local instance {m : ℕ} : Inhabited (Vector U m) := ⟨Vector.replicate m default⟩

/-! Local oracle-spec instances for the §5.8 challenge-oracle families: synthesis cannot see
through `OracleInterface.Response` (a plain `def`), so the per-range instances are provided
field-by-field. Not exported (the public hybrid games take `SampleableType` hypotheses
instead, following the `KeyLemmaHybrids` convention). -/

local instance : (gSpec (U := U) StmtIn pSpec δ).Fintype where
  fintype_B := fun q =>
    inferInstanceAs (Fintype (Vector U (challengeSize (pSpec := pSpec) q.1)))

local instance : (gSpec (U := U) StmtIn pSpec δ).Inhabited where
  inhabited_B := fun q =>
    inferInstanceAs (Inhabited (Vector U (challengeSize (pSpec := pSpec) q.1)))

local instance : (eSpec (U := U) StmtIn pSpec δ).Fintype where
  fintype_B := fun q => inferInstanceAs (Fintype (pSpec.Challenge q.1))

local instance : (eSpec (U := U) StmtIn pSpec δ).Inhabited where
  inhabited_B := fun q => inferInstanceAs (Inhabited (pSpec.Challenge q.1))

section CodecCoupling

/-- **CO25 Eq. 53, per derivation**: one fresh `Hyb₁` challenge derivation (a uniform
encoded block `ρ̂ ← 𝒰(Σ^{ℓ_V(i)})`) and one fresh `Hyb₂` derivation (a uniform challenge
`ρ ← 𝒰(ℳ_{V,i})` followed by a uniform `ψᵢ⁻¹`-preimage) are within the codec decoding bias
`ε_cdc,i` in total variation. -/
theorem tvDist_uniformEncoded_decodedFiber_le_decodingBias (i : pSpec.ChallengeIdx) :
    PMF.tvDist
      (PMF.uniformOfFintype (Vector U (challengeSize (pSpec := pSpec) i)))
      ((PMF.uniformOfFintype (pSpec.Challenge i)).bind fun ch =>
        PMF.uniformOfFinset (Finset.univ.filter fun v => ch = codec.decode i v)
          (fiber_nonempty (codec.decode_surjective i) ch))
    ≤ (codec.decodingBias i : ℝ) := by
  refine le_trans
    (tvDist_uniform_bind_uniformFiber_le (codec.decode_surjective i)
      (PMF.uniformOfFintype (pSpec.Challenge i))) ?_
  rw [PMF.tvDist_comm]
  -- `Codec.decode_isBiased` bounds the (larger) `L¹` distance of `Serde.lean`'s `Dist`
  -- instance; `dist`/`<$>` unfold definitionally to the `L¹` sum/`PMF.map`
  refine le_trans (pmf_tvDist_le_l1 _ _) ?_
  exact codec.decode_isBiased i

end CodecCoupling

/-! ## In-tree sampler semantics: `sampleFromList` / `uniformDeserializePreimage`

The §5.4 `ψ⁻¹` sampler draws a uniform index into the preimage list through the `unifSpec`
summand; under the canonical i.i.d.-uniform semantics `𝒟[·]` it is exactly the uniform
distribution on the preimage finset. -/

section SamplerSemantics

variable {κ : Type} {challengeSpec : OracleSpec κ}
  [challengeSpec.Fintype] [challengeSpec.Inhabited]

/-- The probability that the uniform list sampler returns `x` is `1/|l|` for `x ∈ l` (and
`0` otherwise), provided `l` has no duplicates. -/
theorem probOutput_sampleFromList {α : Type} [DecidableEq α]
    (l : List α) (hl : l ≠ []) (hnd : l.Nodup) (x : α) :
    Pr[= x | sampleFromList (U := U) (challengeSpec := challengeSpec) l hl]
      = if x ∈ l then ((l.length : ℝ≥0∞))⁻¹ else 0 := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr hl
  unfold sampleFromList
  rw [probOutput_bind_eq_tsum]
  by_cases hx : x ∈ l
  · obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hx
    refine Eq.trans (tsum_eq_single (L := SummationFilter.unconditional _)
      (⟨i₀.1, by have := i₀.2; omega⟩ :
        (D2SChallengePlusUnitOracle (U := U) challengeSpec).Range
          (Sum.inr (Sum.inr (l.length - 1))))
      fun u hu => ?_) ?_
    · -- off-index terms vanish: `nodup` makes the matching index unique
      have hne : x ≠ l.get ⟨u.1, by have := u.2; omega⟩ := by
        intro hxe
        refine hu (Fin.ext ?_)
        have hgg : l.get ⟨u.1, by have := u.2; omega⟩ = l.get i₀ := by rw [← hxe, hi₀]
        simpa using congrArg Fin.val ((List.nodup_iff_injective_get.mp hnd) hgg)
      simp only [probOutput_pure]
      rw [if_neg hne, mul_zero]
    · -- the matching index contributes `1/|Fin (l.length - 1 + 1)| = 1/|l|`
      have hget : x = l.get ⟨i₀.1, by have := i₀.2; omega⟩ := by rw [← hi₀]
      simp only [probOutput_pure]
      rw [if_pos hget, mul_one]
      simp only [HasQuery.instOfMonadLift_query, probOutput_query]
      rw [if_pos hx]
      have hcard : Fintype.card
          ((D2SChallengePlusUnitOracle (U := U) challengeSpec).Range
            (.inr (.inr (l.length - 1)))) = l.length := by
        change Fintype.card (Fin (l.length - 1 + 1)) = l.length
        simp only [Fintype.card_fin]
        omega
      exact congrArg (fun m : ℕ => ((m : ℝ≥0∞))⁻¹) hcard
  · rw [if_neg hx]
    refine ENNReal.tsum_eq_zero.mpr fun u => ?_
    have hne : x ≠ l.get ⟨u.1, by have := u.2; omega⟩ := by
      intro hxe
      refine hx ?_
      rw [hxe]
      exact List.get_mem l _
    simp only [probOutput_pure]
    rw [if_neg hne, mul_zero]

/-- `𝒟`-semantics of the uniform list sampler on a duplicate-free list, finset form. -/
theorem evalDist_sampleFromList_toFinset {α : Type} [DecidableEq α]
    (l : List α) (hl : l ≠ []) (hnd : l.Nodup) :
    𝒟[sampleFromList (U := U) (challengeSpec := challengeSpec) l hl]
      = liftM (PMF.uniformOfFinset l.toFinset
          (by simpa [List.toFinset_nonempty_iff] using hl)) := by
  refine SPMF.ext fun x => ?_
  rw [SPMF.liftM_apply, PMF.uniformOfFinset_apply]
  have := probOutput_sampleFromList (U := U) (challengeSpec := challengeSpec) l hl hnd x
  rw [probOutput_def] at this
  rw [this, List.toFinset_card_of_nodup hnd]
  simp [List.mem_toFinset]

/-- `uniformOfFinset` congruence in the finset argument (the nonemptiness proofs are
irrelevant). -/
lemma uniformOfFinset_congr {α : Type u} {s t : Finset α} (h : s = t)
    {hs : s.Nonempty} {ht : t.Nonempty} :
    PMF.uniformOfFinset s hs = PMF.uniformOfFinset t ht := by
  subst h
  rfl

/-- The §5.4 preimage finset is nonempty (`Codec.decode_surjective`). -/
lemma deserializePreimageFinset_nonempty {i : pSpec.ChallengeIdx}
    (ch : pSpec.Challenge i) :
    (deserializePreimageFinset (pSpec := pSpec) (U := U) ch).Nonempty := by
  obtain ⟨v, hv⟩ := codec.decode_surjective i ch
  refine ⟨v, ?_⟩
  unfold deserializePreimageFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hv

/-- The §5.4 preimage finset is the `ψᵢ`-fiber (decoder form). -/
lemma deserializePreimageFinset_eq_fiber {i : pSpec.ChallengeIdx}
    (ch : pSpec.Challenge i) :
    deserializePreimageFinset (pSpec := pSpec) (U := U) ch
      = Finset.univ.filter fun v => ch = codec.decode i v := by
  ext v
  unfold deserializePreimageFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **`𝒟`-semantics of the §5.4 `ψ⁻¹` sampler**: `uniformDeserializePreimage ch` is exactly
uniform on the preimage finset `ψᵢ⁻¹(ch)`. -/
theorem evalDist_uniformDeserializePreimage {i : pSpec.ChallengeIdx}
    (ch : pSpec.Challenge i) :
    𝒟[uniformDeserializePreimage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) ch]
      = liftM (PMF.uniformOfFinset
          (deserializePreimageFinset (pSpec := pSpec) (U := U) ch)
          (deserializePreimageFinset_nonempty ch)) := by
  unfold uniformDeserializePreimage
  rw [evalDist_sampleFromList_toFinset (U := U) (challengeSpec := challengeSpec) _ _
    (Finset.nodup_toList _)]
  exact congrArg _ (uniformOfFinset_congr (Finset.toList_toFinset _))

end SamplerSemantics

/-! ## The per-query coupling in the exact in-tree `GImpl` shape -/

section GImplCoupling

/-- The `Hyb₁` `gᵢ`-realization at a single query is the uniform-range query with the
success/state plumbing attached. -/
lemma gImplEncodedForward_run_eq (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    ((gImplEncodedForward (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) q).run
        PUnit.unit).run
      = (query (spec := D2SChallengePlusUnitOracle (U := U)
            (gSpec (U := U) StmtIn pSpec δ)) (.inl q) :
              OracleComp _ (Vector U (challengeSize (pSpec := pSpec) q.1))) >>= fun v =>
          pure (some (v, PUnit.unit)) := rfl

/-- The `Hyb₂` `gᵢ`-realization at a single query is the decoded-challenge query followed by
the `ψ⁻¹` preimage sampler, with the success/state plumbing attached. -/
lemma gImplDecodedChallenge_run_eq (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    ((gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) q).run
        PUnit.unit).run
      = (query (spec := D2SChallengePlusUnitOracle (U := U)
            (eSpec (U := U) StmtIn pSpec δ)) (.inl q) :
              OracleComp _ (pSpec.Challenge q.1)) >>= fun ch =>
          uniformDeserializePreimage (pSpec := pSpec) (U := U)
              (challengeSpec := eSpec (U := U) StmtIn pSpec δ) ch >>= fun v =>
            pure (some (v, PUnit.unit)) := rfl

/-- **CO25 Eq. 53, per query, in-tree shape**: at any single `gSpec` query, the `Hyb₁`
realization (`gImplEncodedForward`, uniform encoded block) and the `Hyb₂` realization
(`gImplDecodedChallenge`, uniform challenge + uniform `ψᵢ⁻¹` preimage) — each run under the
canonical i.i.d.-uniform semantics of its own oracle world — are within the codec decoding
bias `ε_cdc,i` of the queried round. -/
theorem tvDist_gImplEncodedForward_gImplDecodedChallenge_le
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    SPMF.tvDist
      𝒟[((gImplEncodedForward (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) q).run
          PUnit.unit).run]
      𝒟[((gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) q).run
          PUnit.unit).run]
      ≤ (codec.decodingBias q.1 : ℝ) := by
  -- closed form of the `Hyb₁`-side distribution
  have hA : 𝒟[((gImplEncodedForward (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        q).run PUnit.unit).run]
      = (fun v => some (v, PUnit.unit)) <$>
          (liftM (PMF.uniformOfFintype (Vector U (challengeSize (pSpec := pSpec) q.1))) :
            SPMF _) := by
    refine (congrArg _ (gImplEncodedForward_run_eq (U := U) (StmtIn := StmtIn)
      (pSpec := pSpec) (δ := δ) q)).trans ?_
    refine (evalDist_bind _ _).trans ?_
    have hq : 𝒟[(query (spec := D2SChallengePlusUnitOracle (U := U)
          (gSpec (U := U) StmtIn pSpec δ)) (.inl q) :
            OracleComp (D2SChallengePlusUnitOracle (U := U)
              (gSpec (U := U) StmtIn pSpec δ))
              (Vector U (challengeSize (pSpec := pSpec) q.1)))]
        = (liftM (PMF.uniformOfFintype (Vector U (challengeSize (pSpec := pSpec) q.1))) :
            SPMF _) := by
      simp only [HasQuery.instOfMonadLift_query, evalDist_query]
      rfl
    rw [hq]
    refine (bind_congr fun v => evalDist_pure _).trans ?_
    exact bind_pure_comp _ _
  -- closed form of the `Hyb₂`-side distribution
  have hInner : ∀ ch : pSpec.Challenge q.1,
      𝒟[uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := eSpec (U := U) StmtIn pSpec δ) ch >>= fun v =>
        pure (some (v, PUnit.unit))]
      = (fun v => some (v, PUnit.unit)) <$>
          (liftM (PMF.uniformOfFinset
            (deserializePreimageFinset (pSpec := pSpec) (U := U) ch)
            (deserializePreimageFinset_nonempty ch)) : SPMF _) := fun ch => by
    refine (evalDist_bind _ _).trans ?_
    rw [evalDist_uniformDeserializePreimage (U := U)
      (challengeSpec := eSpec (U := U) StmtIn pSpec δ) ch]
    refine (bind_congr fun v => evalDist_pure _).trans ?_
    exact bind_pure_comp _ _
  have hB : 𝒟[((gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        q).run PUnit.unit).run]
      = (liftM (PMF.uniformOfFintype (pSpec.Challenge q.1)) : SPMF _) >>= fun ch =>
          (fun v => some (v, PUnit.unit)) <$>
            (liftM (PMF.uniformOfFinset
              (deserializePreimageFinset (pSpec := pSpec) (U := U) ch)
              (deserializePreimageFinset_nonempty ch)) : SPMF _) := by
    refine (congrArg _ (gImplDecodedChallenge_run_eq (U := U) (StmtIn := StmtIn)
      (pSpec := pSpec) (δ := δ) q)).trans ?_
    refine (evalDist_bind _ _).trans ?_
    have hq : 𝒟[(query (spec := D2SChallengePlusUnitOracle (U := U)
          (eSpec (U := U) StmtIn pSpec δ)) (.inl q) :
            OracleComp (D2SChallengePlusUnitOracle (U := U)
              (eSpec (U := U) StmtIn pSpec δ)) (pSpec.Challenge q.1))]
        = (liftM (PMF.uniformOfFintype (pSpec.Challenge q.1)) : SPMF _) := by
      simp only [HasQuery.instOfMonadLift_query, evalDist_query]
      rfl
    rw [hq]
    exact bind_congr fun ch => hInner ch
  rw [hA, hB, ← map_bind]
  refine le_trans (SPMF.tvDist_map_le _ _ _) ?_
  rw [spmf_liftM_bind]
  refine le_trans (spmf_tvDist_liftM_le _ _) ?_
  have hker : ((PMF.uniformOfFintype (pSpec.Challenge q.1)).bind fun ch =>
        PMF.uniformOfFinset (deserializePreimageFinset (pSpec := pSpec) (U := U) ch)
          (deserializePreimageFinset_nonempty ch))
      = ((PMF.uniformOfFintype (pSpec.Challenge q.1)).bind fun ch =>
        PMF.uniformOfFinset (Finset.univ.filter fun v => ch = codec.decode q.1 v)
          (fiber_nonempty (codec.decode_surjective q.1) ch)) := by
    refine congrArg _ (funext fun ch => ?_)
    exact uniformOfFinset_congr (deserializePreimageFinset_eq_fiber ch)
  rw [hker]
  exact tvDist_uniformEncoded_decodedFiber_le_decodingBias (U := U) q.1

end GImplCoupling

/-! ## The pivot hybrid `Hyb12Mid` and the finer residual split

`Hyb12Mid` is `Hyb₁`'s game with the `gᵢ` answer resampled inside its own `ψᵢ`-fiber
(`gImplEncodedResampled`). Per *fresh* derivation the resampling is invisible
(`map_bind_uniformFiber_eq_uniform`), and against `Hyb₂` the only per-derivation difference
left is the challenge distribution (`ψᵢ(𝒰(Σ^ℓᵢ))` vs `𝒰(ℳᵢ)`), whose cost is exactly the
decoding bias. The two named residuals below capture the remaining (genuinely open)
freshness/accounting analysis; `hyb12Step_of_resampleSplit` (proven) assembles them into
`Hyb12StepResidual`. -/

section MidHybrid

/-- The fiber-resampled `Hyb₁` `gᵢ`-realization: query the encoded oracle `gᵢ`, decode the
answer (`ψᵢ`), then resample a uniform `ψᵢ⁻¹`-preimage. Distributionally invisible per fresh
derivation (`map_bind_uniformFiber_eq_uniform`), and per-derivation `ε_cdc,i`-close to
`gImplDecodedChallenge` (data processing through the common fiber kernel). -/
noncomputable def gImplEncodedResampled :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) PUnit :=
  fun q => do
    let v ←
      StateT.lift <|
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
              (Vector U (challengeSize (pSpec := pSpec) q.1)) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
              (.inl q))
    StateT.lift <|
      OptionT.lift <|
        uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
          (Deserialize.deserialize v : pSpec.Challenge q.1)

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The pivot hybrid: `Hyb₁`'s game (uniform `gSpec` table, `Hyb₁` line-4 map) with the
`gᵢ` answers resampled inside their own `ψᵢ`-fibers. -/
noncomputable def Hyb12Mid [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (gSpec (U := U) StmtIn pSpec δ))
      (gImplEncodedResampled (StmtIn := StmtIn) (δ := δ))
      (hyb1Line4TraceEager (δ := δ)) oImpl V P]

/-- Finer residual A — **fiber-resample alignment** (`Δ(Hyb₁, Hyb12Mid) = 0`): resampling
each `gᵢ` answer inside its own `ψᵢ`-fiber does not change the game distribution. Per fresh
derivation this is exactly `map_bind_uniformFiber_eq_uniform`; the open content is the CO25
§5.4 freshness analysis (derivation keys do not repeat against the eager table, the same
argument the `tr_i` memo encodes). Strictly smaller than `Hyb12StepResidual`: it is a
`= 0` alignment claim with the bias paid nowhere. -/
def Hyb12ResampleAlignResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb1 T_H T_P δ oImpl V P) (Hyb12Mid T_H T_P δ oImpl V P) = 0

/-- Finer residual B — **bias accounting** (`Δ(Hyb12Mid, Hyb₂) ≤ claim5_22Bound`): both
sides derive each challenge by (challenge distribution, then the same `ψᵢ⁻¹`-fiber kernel);
per derivation they differ only in the challenge distribution, bounded by `ε_cdc,i`
(`tvDist_uniformEncoded_decodedFiber_le_decodingBias`), accumulated over `θ★` prover-side
derivations plus one per round on the verifier side via
`tvDist_evalDist_simulateQ_le_of_close`. Strictly smaller than `Hyb12StepResidual`: the
encoded-vs-resampled alignment is no longer part of the claim. -/
def Hyb12BiasAccountingResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb12Mid T_H T_P δ oImpl V P) (Hyb2 T_H T_P δ oImpl V P)
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ codec.decodingBias

/-- **CO25 Claim 5.22 proof skeleton (proven)**: the fiber-resample alignment and the bias
accounting residuals assemble into the full `Hyb12StepResidual` by the TV triangle
inequality through the pivot `Hyb12Mid`. -/
theorem hyb12Step_of_resampleSplit [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hA : Hyb12ResampleAlignResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hB : Hyb12BiasAccountingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl) :
    Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have h1 := hA V P
  have h2 := hB V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have htri := SPMF.tvDist_triangle (Hyb1 T_H T_P δ oImpl V P)
    (Hyb12Mid T_H T_P δ oImpl V P) (Hyb2 T_H T_P δ oImpl V P)
  linarith

end MidHybrid

end DuplexSpongeFS.Hyb12Step

#print axioms DuplexSpongeFS.Hyb12Step.pmf_tvDist_bind_left_le_of_forall
#print axioms DuplexSpongeFS.Hyb12Step.spmf_tvDist_bind_left_le_of_forall
#print axioms DuplexSpongeFS.Hyb12Step.spmf_tvDist_liftM_le
#print axioms DuplexSpongeFS.Hyb12Step.spmf_liftM_bind
#print axioms DuplexSpongeFS.Hyb12Step.tvDist_evalDist_simulateQ_le_of_close
#print axioms DuplexSpongeFS.Hyb12Step.fiber_nonempty
#print axioms DuplexSpongeFS.Hyb12Step.map_bind_uniformFiber_eq_uniform
#print axioms DuplexSpongeFS.Hyb12Step.tvDist_uniform_bind_uniformFiber_le
#print axioms DuplexSpongeFS.Hyb12Step.tvDist_uniformEncoded_decodedFiber_le_decodingBias
#print axioms DuplexSpongeFS.Hyb12Step.probOutput_sampleFromList
#print axioms DuplexSpongeFS.Hyb12Step.evalDist_sampleFromList_toFinset
#print axioms DuplexSpongeFS.Hyb12Step.deserializePreimageFinset_nonempty
#print axioms DuplexSpongeFS.Hyb12Step.deserializePreimageFinset_eq_fiber
#print axioms DuplexSpongeFS.Hyb12Step.evalDist_uniformDeserializePreimage
#print axioms DuplexSpongeFS.Hyb12Step.gImplEncodedForward_run_eq
#print axioms DuplexSpongeFS.Hyb12Step.gImplDecodedChallenge_run_eq
#print axioms DuplexSpongeFS.Hyb12Step.tvDist_gImplEncodedForward_gImplDecodedChallenge_le
#print axioms DuplexSpongeFS.Hyb12Step.hyb12Step_of_resampleSplit

end
