/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Delta0Lift
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Decoded
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Budgets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12EagerLazy

/-!
# Honest repairs of the three doubt-flagged round-4 residuals

The round-4 frontier (`KeyLemmaFrontierRound4`) carries three residuals under explicit
honest doubt flags. This module executes their **honest repairs**: machine-checked falsity
where constructible at bounded cost, budget-relaxed repaired surfaces with **proven**
re-routed reductions back into the key-lemma frontier, and machine-checked numeric
verdicts on what the proven absorption capacity can and cannot pay for.

## 1. `Hyb12Align.Hyb12RepeatDerivationResidual` (exact-`0`, doubtful for non-injective
   decoders)

* **Kernel falsity, machine-checked** (`repeatDerivationKernelTransparency_not_universal`):
  the sampler-level claim implicit in the exact-`0` residual — replaying a memoized
  `ψ⁻¹`-fiber redraw on a repeated derivation key is distribution-invisible against a
  fresh redraw — is **FALSE** for non-injective `ψ`. Concrete instance `V = Bool`,
  `M = Unit`, `ψ = const`: the memoized two-draw law is supported on the diagonal while
  the fresh law reaches `(true, false)`; the TV distance is provably positive
  (`repeatDerivationKernel_tvDist_pos`). The matching positive result
  (`repeatDerivationKernel_transparent_of_injective`) machine-checks the rescue claimed in
  the `Hyb12Align` docstring: for **injective** `ψ` (singleton fibers) the two kernels are
  equal in distribution, exactly `0`.
  Honest scope note: this refutes the *kernel* of the residual, not the full-game `Prop`
  itself — the full-game counterexample additionally needs a reachability construction (a
  concrete DSFS instance in which the same encoded key is derived twice through two
  table-missing sponge states with positive probability, and the raw fiber pair survives
  to the output). That is precisely the §5.4 channel of `Hyb12Align` point 4 and remains
  open; what is settled here is that *if* such a path is reachable, the exposed kernel is
  visibly non-invisible — there is no distribution-level miracle to hope for.
* **Birthday-budgeted repair** (`Hyb12RepeatDerivationEpsFunResidual`, instantiated at the
  Lemma 5.8 shape as `Hyb12RepeatDerivationBirthdayResidual`): the repaired surface
  charges the repeat-derivation divergence to a budget-dependent `ε₁₂(T)` at the
  `Hyb₀/Hyb₁` trace length `T = tₕ + 1 + tₚ + L + tₚᵢ` (the CO25 §5.6 attribution: the
  divergence channel only opens on capacity collisions among sampled states).
* **Proven re-routed reduction** (`hyb12StepEpsFun_of_coreResiduals` →
  `keyLemmaEager_of_steps_epsFun1223` → `keyLemmaEagerDelta0_of_coreResidualsEpsFun1223`):
  the repaired form still feeds Claim 5.22 and the full `δ = 0` eager key lemma at the
  **unchanged** `ηStarPaper` bound, for any `ε₁₂ + ε₂₃` within the proven F1b claimSum
  slack `(14t + 7)/(2|Σ|^c)` (constant-budget corollary
  `keyLemmaEagerDelta0_of_coreResidualsEps1223` at `ε₁₂ + ε₂₃ ≤ 7/(2|Σ|^c)`).
* **Machine-checked absorption verdict** (`claimSlack_lt_lemma5_8Bound`,
  `birthdayRepair_not_absorbable`): the birthday-shaped `ε₁₂ = lemma5_8Bound U T` strictly
  **overflows** the claimSum slack for every non-trivial budget (`1 ≤ tₕ+tₚ+tₚᵢ+L`), so the
  birthday repair canNOT ride the absorption route — the honest general route is the
  documented re-statement of the Claim 5.21/5.24 budgets (CO25 itself charges these paths
  inside the *existing* §5.6 birthday terms rather than adding a new additive ε).

## 2. `Hyb12Budgets.Hyb12VerifierOncePerRoundResidual` (support-path doubt flag)

* **The Dead-certificate reduction, proven** (`hyb12VerifierOncePerRound_of_noRefire`):
  the round-4 header said B4's open core "is exactly a `Dead` certificate away" — this
  module makes that literal. `Hyb12OncePerRoundNoRefireResidual` is the certificate for
  the **canonical** Dead predicate `Dead_i s := ∀ t, d2fStepRoundFires i t s = 0` (no
  query can fire round `i` from `s`): (a) every state reached by a round-`i` fire is dead,
  and (b) dead states stay dead. The proven reduction converts it into the full
  once-per-round budget via the fire-once carrier and the round-indexed F4 toolkit
  (`d2fStepRoundFires_le_one` is the new 0/1-valuedness brick). After this module the open
  content of B4 is *purely* the backtrack no-refire state analysis — no `IsQueryBoundP`
  induction remains.
* **Honest analysis (documented, not proven)**: the certificate is state-global, which is
  what the fire-once carrier consumes (it quantifies over all computations, hence over all
  reachable states). On the dedup surface, `BacktrackLemmas.backtrackSequence_unique`
  gives per-state uniqueness of the backtrack family on redundancy-free traces; the
  remaining content is *temporal*: a fired round-`i` derivation extends the dispatcher
  trace so that no later `backTrack` re-succeeds at round `i`. The raw-trace mirror of the
  Lemma 5.12 corner (a redundant entry re-enabling a round-`i` parse) is the suspected
  falsity channel; constructing the machine-checked refire witness needs a concrete
  dispatcher state with two chained `backTrack` round-`i` successes — out of bounded reach
  here, left documented rather than claimed either way.

## 3. `Hyb23Delta0.Hyb23MemoTransparencyEpsResidual` (ε estimation via the §5.6 toolkit)

* **The §5.6 classification, proven bricks**: the repeat-key raw-`ρ̂ᵢ` re-exposure event is
  a capacity-collision event — `E_of_capacitySegmentDup` (it is a *sub-event of `E`* by
  definition of the §5.6 combined event) and `probEvent_capacityDup_le_lemma5_8Bound` (any
  game event that factors through `capacitySegmentDup` of the logged `D_𝔖`-carrier trace
  is bounded by `lemma5_8Bound U T`, modulo only the named `Lemma5_8EagerBirthdayResidual`).
  The estimate for the memo-transparency ε is therefore the birthday shape
  `ε₂₃(T) = lemma5_8Bound U T` — quadratic in the trace length.
* **Machine-checked fit/overflow verdict**: the estimated bound fits the proven
  budget-uniform absorption capacity `7/(2|Σ|^c)` **only at trace length `T ≤ 1`**
  (`lemma5_8Bound_one_le_uniformSlack` for the fit; `uniformSlack_lt_lemma5_8Bound` for
  the strict overflow at every `T ≥ 2`). So the estimated ε does **not** fit the
  `keyLemmaEagerDelta0_of_coreResidualsEps23` headline beyond trivial budgets — the
  precise overflow is recorded, not hidden.
* **The re-routing theorem, proven** (`Hyb23MemoTransparencyEpsFunResidual` +
  `hyb23StepEpsFun_delta0_of_coreResiduals` + `keyLemmaEager_of_steps_epsFun1223`): the
  budget-dependent ε-form of the memo-transparency leg feeds the full key lemma at
  unchanged `ηStarPaper` exactly when `ε₁₂(T) + ε₂₃(T)` stays within the per-budget
  claimSum slack — the hypothesis `hεsum` is the *exact* absorption capacity, so the
  theorem is the sharp boundary: inside it, no bound changes; outside it (in particular at
  the birthday estimate, by `birthdayRepair_not_absorbable`), the honest route is the
  documented re-statement of the Claim 5.21/5.24 budgets across the memo switch.

Everything stated here is proven (0 sorries); the two genuinely open analyses (full-game
repeat-derivation reachability, backtrack no-refire/its falsity) are documented as such.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.DoubtRepairs

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open Backtrack
open scoped NNReal ENNReal

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## Repair 1a — the repeat-derivation kernel: machine-checked falsity + injective rescue

`repeatDerivationKernelMemo ψ` is the observable two-draw law of the *memoized* fiber
resampler on a repeated encoded key (draw the table cell, redraw once in its `ψ`-fiber,
replay the stored redraw on the repeat); `repeatDerivationKernelFresh ψ` is the unmemoized
law (`gImplEncodedResampled` serves the repeat with an independent fiber redraw). The
exact-`0` repeat-derivation residual implicitly claims these are equal in distribution for
the in-tree decoders; the claim is machine-checked FALSE in general and TRUE for injective
decoders. -/

section RepeatKernel

/-- Memoized two-draw kernel of the repeat-derivation channel: one fiber redraw, replayed
on the repeated key (CO25 §5.4 D2SAlgo Item 3 determinism — `Hyb12MidMemo`'s behaviour). -/
noncomputable def repeatDerivationKernelMemo {V M : Type} [SampleableType V]
    (ψ : V → M) : ProbComp (V × V) := do
  let c ← $ᵗ V
  let r ← Hyb12Align.fiberResampleDraw ψ c
  pure (r, r)

/-- Fresh two-draw kernel of the repeat-derivation channel: independent fiber redraws on
the repeated key (`Hyb12Mid`'s unmemoized `gImplEncodedResampled` behaviour). -/
noncomputable def repeatDerivationKernelFresh {V M : Type} [SampleableType V]
    (ψ : V → M) : ProbComp (V × V) := do
  let c ← $ᵗ V
  let r₁ ← Hyb12Align.fiberResampleDraw ψ c
  let r₂ ← Hyb12Align.fiberResampleDraw ψ c
  pure (r₁, r₂)

/-- For an **injective** decoder the fiber redraw is deterministic: the `ψ`-fiber of
`ψ(c)` is the singleton `{c}`. -/
private lemma evalDist_fiberResampleDraw_of_injective {V M : Type} [Finite V] {ψ : V → M}
    (hψ : Function.Injective ψ) (c : V) :
    𝒟[Hyb12Align.fiberResampleDraw ψ c] = 𝒟[(pure c : ProbComp V)] := by
  refine evalDist_ext fun v => ?_
  rcases Classical.em (ψ c = ψ v) with h | h
  · obtain rfl : c = v := hψ h
    rw [Hyb12Align.probOutput_fiberResampleDraw_of_eq rfl, probOutput_pure_self]
    have hone : @Fintype.card {d : V // ψ c = ψ d} (Hyb12Align.fiberFintype ψ c) = 1 :=
      (@Fintype.card_eq_one_iff _ (Hyb12Align.fiberFintype ψ c)).mpr
        ⟨⟨c, rfl⟩, fun d => Subtype.ext (hψ d.prop).symm⟩
    rw [hone, Nat.cast_one, inv_one]
  · rw [Hyb12Align.probOutput_fiberResampleDraw_of_ne h]
    have hne : v ≠ c := fun hv => h (by rw [hv])
    exact (probOutput_eq_zero_of_not_mem_support (by simp [hne])).symm

/-- **The injective rescue, machine-checked** (the positive half of the `Hyb12Align`
docstring claim): for injective decoders the memoized and fresh repeat-derivation kernels
are equal in distribution — both collapse to the diagonal of the table draw. -/
theorem repeatDerivationKernel_transparent_of_injective {V M : Type} [SampleableType V]
    {ψ : V → M} (hψ : Function.Injective ψ) :
    tvDist (repeatDerivationKernelMemo ψ) (repeatDerivationKernelFresh ψ) = 0 := by
  rw [tvDist_eq_zero_iff]
  unfold repeatDerivationKernelMemo repeatDerivationKernelFresh
  simp only [evalDist_bind, evalDist_fiberResampleDraw_of_injective hψ, evalDist_pure,
    pure_bind]

/-- The memoized kernel is supported on the diagonal: the replayed draw is the stored
draw. -/
private lemma eq_of_mem_support_repeatDerivationKernelMemo {V M : Type} [SampleableType V]
    (ψ : V → M) {p : V × V} (hp : p ∈ support (repeatDerivationKernelMemo ψ)) :
    p.1 = p.2 := by
  unfold repeatDerivationKernelMemo at hp
  rw [mem_support_bind_iff] at hp
  obtain ⟨c, -, hp⟩ := hp
  rw [mem_support_bind_iff] at hp
  obtain ⟨r, -, hp⟩ := hp
  rw [mem_support_pure_iff] at hp
  subst hp
  rfl

/-- Against the constant (maximally non-injective) decoder on `Bool`, every value is in
every fiber draw's support. -/
private lemma mem_support_fiberResampleDraw_const (c v : Bool) :
    v ∈ support (Hyb12Align.fiberResampleDraw (fun _ : Bool => ()) c) := by
  unfold Hyb12Align.fiberResampleDraw
  rw [support_map]
  exact ⟨⟨v, rfl⟩,
    @mem_support_uniformSample _ (Hyb12Align.fiberSampleable (fun _ : Bool => ()) c) _, rfl⟩

/-- The fresh kernel reaches the off-diagonal point `(true, false)`. -/
private lemma mem_support_repeatDerivationKernelFresh_bool :
    ((true, false) : Bool × Bool)
      ∈ support (repeatDerivationKernelFresh (fun _ : Bool => ())) := by
  unfold repeatDerivationKernelFresh
  rw [mem_support_bind_iff]
  refine ⟨true, mem_support_uniformSample Bool, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨true, mem_support_fiberResampleDraw_const true true, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨false, mem_support_fiberResampleDraw_const true false, by simp⟩

/-- **The repeat-derivation kernel divergence, machine-checked**: at the non-injective
decoder `ψ = const : Bool → Unit`, the memoized and fresh kernels have *different*
distributions — the memo law is diagonal while the fresh law reaches `(true, false)`. -/
theorem repeatDerivationKernel_memo_ne_fresh :
    𝒟[repeatDerivationKernelMemo (fun _ : Bool => ())]
      ≠ 𝒟[repeatDerivationKernelFresh (fun _ : Bool => ())] := by
  intro h
  have h0 : Pr[= ((true, false) : Bool × Bool)
      | repeatDerivationKernelMemo (fun _ : Bool => ())] = 0 :=
    probOutput_eq_zero_of_not_mem_support fun hmem => by
      simpa using eq_of_mem_support_repeatDerivationKernelMemo _ hmem
  exact probOutput_ne_zero_of_mem_support mem_support_repeatDerivationKernelFresh_bool
    ((evalDist_ext_iff.mp h ((true, false) : Bool × Bool)).symm.trans h0)

/-- The kernel divergence in TV form: the distance is **provably positive** (the exact-`0`
claim has no distribution-level escape on non-injective fibers). -/
theorem repeatDerivationKernel_tvDist_pos :
    0 < tvDist (repeatDerivationKernelMemo (fun _ : Bool => ()))
        (repeatDerivationKernelFresh (fun _ : Bool => ())) :=
  lt_of_le_of_ne (tvDist_nonneg _ _) fun h =>
    repeatDerivationKernel_memo_ne_fresh ((tvDist_eq_zero_iff _ _).mp h.symm)

/-- The kernel claim implicit in the exact-`0` repeat-derivation residual: memo replay on
a repeated derivation key is invisible against a fresh fiber redraw, for *every* decoder. -/
def RepeatDerivationKernelTransparency : Prop :=
  ∀ (V M : Type) [SampleableType V] (ψ : V → M),
    tvDist (repeatDerivationKernelMemo ψ) (repeatDerivationKernelFresh ψ) = 0

/-- **The repeat-derivation kernel transparency is FALSE as a universal statement**
(machine-checked counterexample `V = Bool`, `M = Unit`, `ψ = const`; mirror of the
`BacktrackLemmas.lemma5_12HonestResidual_not_universal` pattern). The honest repair of the
game-level residual is therefore the birthday-budgeted relaxation below, not a direct
proof. (The full-game `Hyb12RepeatDerivationResidual` is *not* hereby refuted: the missing
piece is the reachability of a repeat-derivation path in a concrete DSFS instance — the
documented open §5.4 channel.) -/
theorem repeatDerivationKernelTransparency_not_universal :
    ¬ RepeatDerivationKernelTransparency := fun hall =>
  repeatDerivationKernel_memo_ne_fresh
    ((tvDist_eq_zero_iff _ _).mp (hall Bool Unit (fun _ => ())))

end RepeatKernel

/-! ## Repairs 1b/3a — the absorption numerics: birthday shapes vs the proven F1b slack

`Hyb23Delta0.claimSum_add_le_ηStarPaper` proved the exact claimSum slack
`(14t + 7)/(2|Σ|^c)` (`t = tₕ + tₚ + tₚᵢ`), of which `7/(2|Σ|^c)` is budget-uniform. The
honest estimates for both repaired legs are birthday-shaped (`lemma5_8Bound U T`,
quadratic in the trace length `T`). These are the machine-checked fit/overflow verdicts. -/

section AbsorptionNumerics

variable (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]

/-- **Fit at trivial budgets**: at trace length `T = 1` the birthday shape
`(7 − 3)/(2|Σ|^c)` fits the budget-uniform absorption capacity `7/(2|Σ|^c)`. -/
theorem lemma5_8Bound_one_le_uniformSlack :
    BirthdayBound.lemma5_8Bound U 1 ≤ 7 / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
  have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C :=
    mul_pos two_pos (pow_pos hc0 _)
  unfold BirthdayBound.lemma5_8Bound
  rw [div_le_div_iff₀ h2P h2P]
  push_cast
  nlinarith [h2P.le]

/-- **Overflow of the budget-uniform capacity, machine-checked**: at every trace length
`T ≥ 2` the birthday shape strictly exceeds `7/(2|Σ|^c)` — the §5.6 estimate of the
memo-transparency ε does **not** fit the `keyLemmaEagerDelta0_of_coreResidualsEps23`
headline beyond trivial budgets. -/
theorem uniformSlack_lt_lemma5_8Bound (T : ℕ) (hT : 2 ≤ T) :
    7 / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) < BirthdayBound.lemma5_8Bound U T := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
  have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C :=
    mul_pos two_pos (pow_pos hc0 _)
  unfold BirthdayBound.lemma5_8Bound
  rw [div_lt_div_iff₀ h2P h2P]
  refine mul_lt_mul_of_pos_right ?_ h2P
  have hT' : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hfact : (0 : ℝ) ≤ ((T : ℝ) - 2) * (7 * (T : ℝ) + 11) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [hfact]

/-- **Overflow of the full claimSum slack, machine-checked**: at the `Hyb₀/Hyb₁` trace
length `T = tₕ + 1 + tₚ + L + tₚᵢ`, the birthday shape strictly exceeds the *entire* F1b
slack `(14t + 7)/(2|Σ|^c)` for every non-trivial budget (`1 ≤ tₕ + tₚ + tₚᵢ + L`). A
birthday-budgeted repeat-derivation leg therefore cannot ride the claimSum absorption. -/
theorem claimSlack_lt_lemma5_8Bound (tₕ tₚ tₚᵢ L : ℕ) (hnz : 1 ≤ tₕ + tₚ + tₚᵢ + L) :
    (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7) / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
      < BirthdayBound.lemma5_8Bound U (tₕ + 1 + tₚ + L + tₚᵢ) := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
  have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C :=
    mul_pos two_pos (pow_pos hc0 _)
  unfold BirthdayBound.lemma5_8Bound
  rw [div_lt_div_iff₀ h2P h2P]
  refine mul_lt_mul_of_pos_right ?_ h2P
  have hs : (1 : ℝ) ≤ (tₕ : ℝ) + (tₚ : ℝ) + (tₚᵢ : ℝ) + (L : ℝ) := by exact_mod_cast hnz
  have hfact : (0 : ℝ) ≤ ((tₕ : ℝ) + (tₚ : ℝ) + (tₚᵢ : ℝ) + (L : ℝ) - 1)
      * (7 * ((tₕ : ℝ) + (tₚ : ℝ) + (tₚᵢ : ℝ) + (L : ℝ)) + 4) :=
    mul_nonneg (by linarith) (by positivity)
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  push_cast
  nlinarith [hfact, hL]

/-- **The birthday repair is NOT absorbable, machine-checked**: no nonnegative companion
budget `ε'` makes the birthday-shaped `ε₁₂` satisfy the per-budget claimSum-absorption
hypothesis of `keyLemmaEager_of_steps_epsFun1223` at all budgets — already `tₕ = 1` (with
`tₚ = tₚᵢ = L = 0`) overflows. The honest route for the birthday-budgeted repairs beyond
the slack is the **documented re-statement** of the Claim 5.21/5.24 budgets (CO25 charges
these collision paths inside the existing §5.6 birthday terms, not as a new additive ε). -/
theorem birthdayRepair_not_absorbable {ε' : ℕ → ℝ} (hnn : ∀ T, 0 ≤ ε' T) :
    ¬ ∀ tₕ tₚ tₚᵢ L : ℕ,
        BirthdayBound.lemma5_8Bound U (tₕ + 1 + tₚ + L + tₚᵢ)
            + ε' (tₕ + 1 + tₚ + L + tₚᵢ)
          ≤ (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7)
              / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
  intro hall
  have h := hall 1 0 0 0
  have hlt := claimSlack_lt_lemma5_8Bound U 1 0 0 0 (by norm_num)
  have hε := hnn (1 + 1 + 0 + 0 + 0)
  linarith

end AbsorptionNumerics

/-! ## Repair 3b — the §5.6 capacity-collision channel for the re-exposure event

The repeat-key raw-`ρ̂ᵢ` re-exposure event of the memo-transparency leg is a
permutation-state **capacity collision** (CO25 §5.4/§5.6): two distinct sponge states with
equal capacity segments forcing a repeated derivation key. These bricks pin the §5.6
classification: the collision event is a sub-event of `E` *by definition*, and any game
event factoring through it on the logged `D_𝔖`-carrier trace is bounded by the Lemma 5.8
birthday bound modulo only the named 5.8 residual. -/

section CapacityChannel

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- The §5.6 capacity-collision event is a sub-event of the combined bad event `E` (by
definition of `E = capacitySegmentDup ∨ notFunction`). This is the classification step of
the re-exposure estimate: re-exposure ⊆ capacity collision ⊆ `E`. -/
lemma E_of_capacitySegmentDup {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : capacitySegmentDup tr) : E tr := Or.inl h

/-- Capacity-collision mass is dominated by `E`-mass in any experiment exposing a trace. -/
theorem probEvent_capacityDup_le_probEvent_E {β : Type} (game : ProbComp β)
    (tr : β → QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    Pr[ fun z => capacitySegmentDup (tr z) | game]
      ≤ Pr[ fun z => E (tr z) | game] :=
  probEvent_mono'' fun _ hz => E_of_capacitySegmentDup hz

/-- **The §5.6 → §5.8 channel for the re-exposure event class** (the quantitative
estimate): modulo the named `Lemma5_8EagerBirthdayResidual`, the capacity-collision mass
of the logged `D_𝔖`-carrier trace — the event class containing the memo-transparency
re-exposure event — is bounded by `lemma5_8Bound U T`. Combined with the overflow verdicts
above: the honest ε estimate for `Hyb23MemoTransparencyEpsResidual` is birthday-shaped,
fits `7/(2|Σ|^c)` only at `T ≤ 1`, and otherwise must be consumed through the per-budget
re-routing theorem below. -/
theorem probEvent_capacityDup_le_lemma5_8Bound
    [Fintype U] [DecidableEq U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (h58 : BirthdayBound.Lemma5_8EagerBirthdayResidual StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        capacitySegmentDup z.2 |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ BirthdayBound.lemma5_8Bound U T := by
  refine le_trans (ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) ?_) (h58 P T hT)
  exact probEvent_capacityDup_le_probEvent_E _
    (fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => z.2)

end CapacityChannel

/-! ## The DSFS variable block (shared by the repaired surfaces below) -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-! ## Repair 2 — B4's Dead certificate: the canonical no-refire residual + proven
reduction -/

section OncePerRound

/-- 0/1-valuedness of the round-`i` dispatcher fire count (branch-tree of
`d2sStepRoundFires`). -/
private lemma d2sStepRoundFires_le_one
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (i : pSpec.ChallengeIdx)
    (qq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Hyb12Budgets.d2sStepRoundFires (T_H := T_H) (T_P := T_P) i qq st ≤ 1 := by
  unfold Hyb12Budgets.d2sStepRoundFires
  split <;> (try split) <;> (try split) <;> omega

/-- 0/1-valuedness of the round-`i` outer pipeline fire count. -/
private lemma d2fStepRoundFires_le_one
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (i : pSpec.ChallengeIdx)
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t st ≤ 1 := by
  unfold Hyb12Budgets.d2fStepRoundFires
  split
  all_goals first
    | exact d2sStepRoundFires_le_one T_H T_P δ i _ st
    | exact Nat.zero_le _

/-- **The canonical Dead certificate for B4** — the backtrack **no-refire invariant** at
the `Hyb₂` dispatcher, stated for the canonical dead predicate
`Dead_i s := ∀ t, d2fStepRoundFires i t s = 0` ("no query can fire round `i` from `s`"):

* (fire kills) every state reached by a step that fires the round-`i` derivation is dead
  for round `i`, and
* (dead stays dead) dead states remain dead across every dispatcher step

— both demanded on **every support path** (`IsQueryBoundP` counts sampled-capacity
collision paths too; this is exactly where the honest doubt lives, mirroring the
Lemma 5.12 raw-trace subtlety). This is precisely the "`Dead` certificate" the
`Hyb12Budgets` header identified as the open core of B4: by the proven reduction below it
implies the full `Hyb12VerifierOncePerRoundResidual` with **no** counting argument left.
On the dedup surface, `BacktrackLemmas.backtrackSequence_unique` settles per-state
uniqueness of the backtrack family; the open content here is the *temporal* claim that a
fired derivation's trace extension de-activates round `i` for the rest of the run. -/
def Hyb12OncePerRoundNoRefireResidual
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ) : Prop :=
  ∀ (i : pSpec.ChallengeIdx)
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : PUnit),
    (Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t s₁ = 1
      ∨ ∀ t' : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain,
          Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t' s₁ = 0) →
    ∀ x ∈ support
      ((((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
          (gImpl := gImplDecodedChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ)) t).run s₁).run s₂).run),
      ∀ (u : (oSpec + duplexSpongeChallengeOracle StmtIn U).Range t)
        (s₁' : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (s₂' : PUnit),
        x = some ((u, s₁'), s₂') →
        ∀ t' : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain,
          Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t' s₁' = 0

/-- **The Dead-certificate reduction for B4, proven**: the canonical no-refire certificate
implies the full once-per-round residual `Hyb12Budgets.Hyb12VerifierOncePerRoundResidual`
— via the fire-once carrier (`isQueryBoundP_simulateQ_stateT2_optionT_fireOnce`) fed by
the round-indexed F4 per-step budget (`d2fOuterImpl_decoded_round_step`) and the
0/1-valuedness brick above. After this theorem, B4's remaining open content is purely the
backtrack no-refire state analysis — no `IsQueryBoundP` induction is left. Note the
conclusion holds for *every* computation through the dispatcher (in particular the honest
verifier replay of the residual), since the certificate is state-global. -/
theorem hyb12VerifierOncePerRound_of_noRefire
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (h : Hyb12OncePerRoundNoRefireResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12Budgets.Hyb12VerifierOncePerRoundResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ := by
  classical
  intro V stmtIn messages mm i
  unfold d2fRaw
  exact Hyb12Budgets.isQueryBoundP_simulateQ_stateT2_optionT_fireOnce
    (Fire := fun t s₁ =>
      Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t s₁ = 1)
    (Dead := fun s₁ =>
      ∀ t' : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain,
        Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t' s₁ = 0)
    (fun t s₁ s₂ => by
      have hb := Hyb12Budgets.d2fOuterImpl_decoded_round_step (oSpec := oSpec)
        (T_H := T_H) (T_P := T_P) (δ := δ) i t s₁ s₂
      have hle := d2fStepRoundFires_le_one T_H T_P δ i t s₁
      by_cases hf :
          Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t s₁ = 1
      · rw [if_pos hf, ← hf]
        exact hb
      · have h0 :
            Hyb12Budgets.d2fStepRoundFires (T_H := T_H) (T_P := T_P) i t s₁ = 0 := by
          omega
        rw [if_neg hf, ← h0]
        exact hb)
    (fun t s₁ hd hf => by have := hd t; omega)
    (fun t s₁ s₂ hf x hx u s₁' s₂' hxeq => h i t s₁ s₂ (Or.inl hf) x hx u s₁' s₂' hxeq)
    (fun t s₁ s₂ hd x hx u s₁' s₂' hxeq => h i t s₁ s₂ (Or.inr hd) x hx u s₁' s₂' hxeq)
    default mm

end OncePerRound

/-! ## Repair 1b — the budget-quantified repaired surfaces of the Claim 5.22 lane -/

section EpsFun12

/-- **The honest repair of the repeat-derivation leg** — budget-quantified ε-form
(`Δ(Hyb12MidMemo, Hyb12Mid) ≤ ε(T)` at the `Hyb₀/Hyb₁` trace length
`T = tₕ + 1 + tₚ + L + tₚᵢ`): the divergence of the memoized vs fresh fiber redraw on
repeated derivation keys is charged to a budget-dependent bound rather than claimed to
vanish (the exact-`0` form's kernel is machine-checked false above for non-injective
decoders). The intended instantiation is the §5.6 birthday attribution
`Hyb12RepeatDerivationBirthdayResidual` below; the exact-`0` form embeds at `ε = 0`
(`hyb12RepeatDerivationEpsFun_of_exact`). -/
def Hyb12RepeatDerivationEpsFunResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) (ε : ℕ → ℝ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb12Align.Hyb12MidMemo T_H T_P δ oImpl V P)
      (Hyb12Step.Hyb12Mid T_H T_P δ oImpl V P) ≤ ε (tₕ + 1 + tₚ + L + tₚᵢ)

/-- The birthday-budgeted repeat-derivation repair at the Lemma 5.8 bound shape — the CO25
§5.6 attribution of the collision paths that open the repeat channel. **Caveat
(machine-checked)**: this shape is *not* absorbable in the claimSum slack
(`birthdayRepair_not_absorbable`); consuming it requires the documented re-statement of
the Claim 5.21/5.24 budgets, not the unchanged-`ηStarPaper` route. -/
abbrev Hyb12RepeatDerivationBirthdayResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl
    (BirthdayBound.lemma5_8Bound U)

/-- The exact-`0` repeat-derivation residual embeds into the repaired surface at `ε = 0`
(the repair strictly generalizes the round-4 frontier hypothesis). -/
theorem hyb12RepeatDerivationEpsFun_of_exact [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (h : Hyb12Align.Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl) :
    Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl (fun _ => 0) := by
  intro V P tₕ tₚ tₚᵢ L _ _ _ _
  exact le_of_eq (h V P)

/-- ε-budget form of CO25 Claim 5.22: `Δ(Hyb₁, Hyb₂) ≤ claim5_22Bound + ε(T)`. -/
def Hyb12StepEpsFunResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) (ε : ℕ → ℝ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb1 T_H T_P δ oImpl V P) (Hyb2 T_H T_P δ oImpl V P)
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ codec.decodingBias
          + ε (tₕ + 1 + tₚ + L + tₚᵢ)

/-- **The re-routed Claim 5.22 reduction, proven** (the round-4 core assembly with the
repeat-derivation leg consumed in repaired ε-form): the all-lazy redraw coupling, the
ε-budgeted repeat-derivation leg, the cross-spec lazy re-keying, and the once-per-round
verifier budget give the ε-budget Claim 5.22 — B1/B3 and all reductions consumed here are
the proven round-4 closures. -/
theorem hyb12StepEpsFun_of_coreResiduals [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) {ε : ℕ → ℝ}
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hRepeat : Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl ε)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hOnce : Hyb12Budgets.Hyb12VerifierOncePerRoundResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ) :
    Hyb12StepEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl ε := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have hA := (Hyb12EagerLazy.hyb12LazyEagerResample_of_redrawCoupling
    T_H T_P δ oImpl hRedraw) V P
  have hB := hRepeat V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have hBias := (Hyb12Accounting.hyb12BiasAccounting_of_freshPipeline T_H T_P δ oImpl
      (Hyb12EagerLazy.hyb12MidFreshAlign_of_crossSpecAlign T_H T_P δ oImpl hCross)
      (Hyb12EagerLazy.hyb2FreshAlign_holds T_H T_P δ oImpl)
      (Hyb12Budgets.hyb12ProverPipelineBudget (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P))
      (Hyb12Budgets.hyb12VerifierPipelineBudget_of_oncePerRound hOnce))
    V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have t1 := SPMF.tvDist_triangle (Hyb1 T_H T_P δ oImpl V P)
    (Hyb12Align.Hyb12MidMemo T_H T_P δ oImpl V P)
    (Hyb12Step.Hyb12Mid T_H T_P δ oImpl V P)
  have t2 := SPMF.tvDist_triangle (Hyb1 T_H T_P δ oImpl V P)
    (Hyb12Step.Hyb12Mid T_H T_P δ oImpl V P) (Hyb2 T_H T_P δ oImpl V P)
  linarith

end EpsFun12

/-! ## Repair 3c — the budget-quantified repaired surfaces of the Claim 5.23 lane -/

section EpsFun23

/-- Budget-quantified ε-form of the `tr_i` memo-transparency leg (step B of the salted
split): `Δ(Hyb3SaltedFresh, Hyb3SaltedMemo) ≤ ε(T)` at the trace length
`T = tₕ + 1 + tₚ + L + tₚᵢ`. The §5.6 estimate for `ε` is the birthday shape (the
re-exposure event is a capacity collision: `E_of_capacitySegmentDup` /
`probEvent_capacityDup_le_lemma5_8Bound`); the constant-budget form
`Hyb23Delta0.Hyb23MemoTransparencyEpsResidual` embeds via
`hyb23MemoTransparencyEpsFun_of_const`. -/
def Hyb23MemoTransparencyEpsFunResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) (ε : ℕ → ℝ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb23Step.Hyb3SaltedFresh T_H T_P δ Salt oImpl V P)
      (Hyb23Step.Hyb3SaltedMemo T_H T_P δ Salt oImpl V P) ≤ ε (tₕ + 1 + tₚ + L + tₚᵢ)

/-- The §5.6 birthday-estimated memo-transparency repair (the honest estimated form;
**machine-checked caveat**: fits the budget-uniform absorption only at `T ≤ 1`,
`uniformSlack_lt_lemma5_8Bound`). -/
abbrev Hyb23MemoTransparencyBirthdayResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  Hyb23MemoTransparencyEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl
    (BirthdayBound.lemma5_8Bound U)

/-- The constant-budget ε-form embeds into the budget-quantified surface. -/
theorem hyb23MemoTransparencyEpsFun_of_const [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) {ε : ℝ}
    (h : Hyb23Delta0.Hyb23MemoTransparencyEpsResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl ε) :
    Hyb23MemoTransparencyEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl
      (fun _ => ε) := by
  intro V P tₕ tₚ tₚᵢ L _ _ _ _
  exact h V P

/-- Budget-quantified ε-form of the whole Claim 5.23 step: `Δ(Hyb₂, Hyb₃) ≤ ε(T)`. -/
def Hyb23StepEpsFunResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) (ε : ℕ → ℝ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb2 T_H T_P δ oImpl V P) (Hyb3 T_H T_P δ Salt oImpl V P)
      ≤ ε (tₕ + 1 + tₚ + L + tₚᵢ)

/-- **The re-routed Claim 5.23 reduction at `δ = 0`, proven**: the fixed-table cross-spec
lift (step A's round-4 core) plus the budget-quantified memo-transparency leg give the
budget-quantified Claim 5.23 step — steps A's probabilistic content and C (salt erasure)
are the proven round-4 closures. -/
theorem hyb23StepEpsFun_delta0_of_coreResiduals [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [Fintype (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) {ε : ℕ → ℝ}
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23MemoTransparencyEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε) :
    Hyb23StepEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have hA := (Hyb23Decoded.hyb23DecodedQuery_delta0_of_crossLift T_H T_P Salt oImpl
    h23X) V P
  have hB := h23B V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have hC := (Hyb23Delta0Lift.hyb23SaltErasure_delta0 T_H T_P Salt oImpl) V P
  have t1 := SPMF.tvDist_triangle (Hyb2 T_H T_P 0 oImpl V P)
    (Hyb23Step.Hyb3SaltedFresh T_H T_P 0 Salt oImpl V P)
    (Hyb3 T_H T_P 0 Salt oImpl V P)
  have t2 := SPMF.tvDist_triangle (Hyb23Step.Hyb3SaltedFresh T_H T_P 0 Salt oImpl V P)
    (Hyb23Step.Hyb3SaltedMemo T_H T_P 0 Salt oImpl V P)
    (Hyb3 T_H T_P 0 Salt oImpl V P)
  linarith

end EpsFun23

/-! ## The re-routed key-lemma assembly: both repaired legs inside the exact claimSum
slack -/

section MasterAssembly

/-- **The re-routed ladder assembly, proven** (the sharp absorption boundary): with the
Claim 5.22 leg in repaired ε₁₂-form and the Claim 5.23 leg in repaired ε₂₃-form, the four
step residuals and witness budgets still give the full eager key lemma at the **unchanged**
`ηStarPaper` bound — provided the combined per-budget cost stays inside the *exact* F1b
claimSum slack (`hεsum`, the hypothesis form of
`Hyb23Delta0.claimSum_add_le_ηStarPaper`). This is sharp in both directions: any
`ε₁₂ + ε₂₃` within the slack needs no bound change, and the birthday-shaped estimates
overflow it for every non-trivial budget (`birthdayRepair_not_absorbable`) — beyond the
slack the honest route is the documented re-statement of the Claim 5.21/5.24 budgets. -/
theorem keyLemmaEager_of_steps_epsFun1223
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (oImpl : QueryImpl oSpec ProbComp) {ε₁₂ ε₂₃ : ℕ → ℝ}
    (hεsum : ∀ tₕ tₚ tₚᵢ L : ℕ,
      ε₁₂ (tₕ + 1 + tₚ + L + tₚᵢ) + ε₂₃ (tₕ + 1 + tₚ + L + tₚᵢ)
        ≤ (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7)
            / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C))
    (h01 : Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h12 : Hyb12StepEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl ε₁₂)
    (h23 : Hyb23StepEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl ε₂₃)
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
  · have hchain := tvDist_chain4
      (Hyb0 T_H T_P δ oImpl V P) (Hyb1 T_H T_P δ oImpl V P) (Hyb2 T_H T_P δ oImpl V P)
      (Hyb3 T_H T_P δ Salt oImpl V P)
      (Hyb4 oImpl V
        (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
      (h01 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
      (h12 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
      (h23 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
      (h34 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
    rw [← hyb4_eq_basicFiatShamirEagerRand oImpl V
        (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P),
      ← hyb0_eq_duplexSpongeRemappedEager T_H T_P δ oImpl V P,
      SPMF.tvDist_comm]
    have hsum := Hyb23Delta0.claimSum_add_le_ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L
      codec.decodingBias (hεsum tₕ tₚ tₚᵢ L)
    linarith

/-- **The re-routed `δ = 0` frontier (the honest repaired headline)**: the round-4 cores
with **both** doubt-flagged distribution legs consumed in repaired budget-quantified
ε-form (repeat derivation: `ε₁₂`; memo transparency: `ε₂₃`), absorbed at the unchanged
`ηStarPaper` bound whenever their combined cost stays inside the exact claimSum slack. The
once-per-round leg stays at the round-4 core (`hOnce`; the Dead-certificate route
`hyb12VerifierOncePerRound_of_noRefire` feeds it); all other legs are the proven round-4
closures. -/
theorem keyLemmaEagerDelta0_of_coreResidualsEpsFun1223
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
    (oImpl : QueryImpl oSpec ProbComp) {ε₁₂ ε₂₃ : ℕ → ℝ}
    (hεsum : ∀ tₕ tₚ tₚᵢ L : ℕ,
      ε₁₂ (tₕ + 1 + tₚ + L + tₚᵢ) + ε₂₃ (tₕ + 1 + tₚ + L + tₚᵢ)
        ≤ (14 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) + 7)
            / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C))
    -- Claim 5.21 lane (Lemma 5.8 fresh-split granularity)
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
    -- Claim 5.22 lane (round-4 cores, repeat derivation REPAIRED)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl ε₁₂)
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hOnce : Hyb12Budgets.Hyb12VerifierOncePerRoundResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0)
    -- Claim 5.23 lane at `δ = 0` (round-4 core, memo transparency REPAIRED)
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23MemoTransparencyEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl ε₂₃)
    -- Claim 5.24 lane
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl :=
  keyLemmaEager_of_steps_epsFun1223 T_H T_P 0 Salt oImpl hεsum
    (Hyb01Step.hyb01Step_of_offEventCoupling_of_freshSplit T_H T_P 0 oImpl h01C
      εsw εev h01sw h01ev h01sum)
    (hyb12StepEpsFun_of_coreResiduals T_H T_P 0 oImpl hRedraw hRepeat hCross hOnce)
    (hyb23StepEpsFun_delta0_of_coreResiduals T_H T_P Salt oImpl h23X h23B)
    (Hyb34Step.hyb34Step_of_divergence_collapse T_H T_P 0 Salt oImpl h34A h34B)
    (SimulatorBudgets.simulatedProverChallengeBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := 0) (Salt := Salt) (T_H := T_H) (T_P := T_P))
    (SimulatorBudgets.simulatedProverSharedBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := 0) (Salt := Salt) (T_H := T_H) (T_P := T_P))

/-- **Constant-budget corollary** (the absorption route in closed form): both repaired
legs at constant budgets with `ε₁₂ + ε₂₃ ≤ 7/(2|Σ|^c)` — the budget-uniform part of the
proven F1b slack — give the full `δ = 0` eager key lemma at the unchanged `ηStarPaper`
bound. This is the proven "repaired forms still feed Claim 5.22/5.23 within claimSum
absorption" statement; the birthday-shaped estimates exceed every constant fitting here
beyond trivial budgets (`uniformSlack_lt_lemma5_8Bound`). -/
theorem keyLemmaEagerDelta0_of_coreResidualsEps1223
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
    (oImpl : QueryImpl oSpec ProbComp) {ε₁₂ ε₂₃ : ℝ}
    (hε : ε₁₂ + ε₂₃ ≤ 7 / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C))
    (h01C : Hyb01Step.Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (εsw εev : ℕ → ℝ)
    (h01sw : Hyb01Step.DDSFreshSwitchResidual StmtIn U εsw)
    (h01ev : Hyb01Step.FreshTraceEventResidual StmtIn U εev)
    (h01sum : ∀ T : ℕ, εsw T + εev T ≤ BirthdayBound.lemma5_8Bound U T)
    (hRedraw : Hyb12EagerLazy.Hyb12LazyRedrawCouplingResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hRepeat : Hyb12RepeatDerivationEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl (fun _ => ε₁₂))
    (hCross : Hyb12EagerLazy.Hyb12MidCrossSpecAlignResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 oImpl)
    (hOnce : Hyb12Budgets.Hyb12VerifierOncePerRoundResidual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0)
    (h23X : Hyb23Decoded.Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl)
    (h23B : Hyb23MemoTransparencyEpsFunResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl
      (fun _ => ε₂₃))
    (h34A : Hyb34Step.Hyb34DivergenceResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl)
    (h34B : Hyb34Step.Hyb34CollapseResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 oImpl := by
  refine keyLemmaEagerDelta0_of_coreResidualsEpsFun1223 T_H T_P Salt oImpl
    (ε₁₂ := fun _ => ε₁₂) (ε₂₃ := fun _ => ε₂₃) (fun tₕ tₚ tₚᵢ L => ?_)
    h01C εsw εev h01sw h01ev h01sum hRedraw hRepeat hCross hOnce h23X h23B h34A h34B
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
  have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C :=
    mul_pos two_pos (pow_pos hc0 _)
  refine le_trans hε ?_
  rw [div_le_div_iff₀ h2P h2P]
  nlinarith [Nat.cast_nonneg (α := ℝ) (tₕ + tₚ + tₚᵢ), h2P.le]

end MasterAssembly

end DuplexSpongeFS.DoubtRepairs

/-! ## Axiom audit -/

#print axioms DuplexSpongeFS.DoubtRepairs.repeatDerivationKernel_transparent_of_injective
#print axioms DuplexSpongeFS.DoubtRepairs.repeatDerivationKernel_memo_ne_fresh
#print axioms DuplexSpongeFS.DoubtRepairs.repeatDerivationKernel_tvDist_pos
#print axioms DuplexSpongeFS.DoubtRepairs.repeatDerivationKernelTransparency_not_universal
#print axioms DuplexSpongeFS.DoubtRepairs.lemma5_8Bound_one_le_uniformSlack
#print axioms DuplexSpongeFS.DoubtRepairs.uniformSlack_lt_lemma5_8Bound
#print axioms DuplexSpongeFS.DoubtRepairs.claimSlack_lt_lemma5_8Bound
#print axioms DuplexSpongeFS.DoubtRepairs.birthdayRepair_not_absorbable
#print axioms DuplexSpongeFS.DoubtRepairs.E_of_capacitySegmentDup
#print axioms DuplexSpongeFS.DoubtRepairs.probEvent_capacityDup_le_probEvent_E
#print axioms DuplexSpongeFS.DoubtRepairs.probEvent_capacityDup_le_lemma5_8Bound
#print axioms DuplexSpongeFS.DoubtRepairs.hyb12VerifierOncePerRound_of_noRefire
#print axioms DuplexSpongeFS.DoubtRepairs.hyb12RepeatDerivationEpsFun_of_exact
#print axioms DuplexSpongeFS.DoubtRepairs.hyb12StepEpsFun_of_coreResiduals
#print axioms DuplexSpongeFS.DoubtRepairs.hyb23MemoTransparencyEpsFun_of_const
#print axioms DuplexSpongeFS.DoubtRepairs.hyb23StepEpsFun_delta0_of_coreResiduals
#print axioms DuplexSpongeFS.DoubtRepairs.keyLemmaEager_of_steps_epsFun1223
#print axioms DuplexSpongeFS.DoubtRepairs.keyLemmaEagerDelta0_of_coreResidualsEpsFun1223
#print axioms DuplexSpongeFS.DoubtRepairs.keyLemmaEagerDelta0_of_coreResidualsEps1223

end
