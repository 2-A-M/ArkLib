/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaHybrids
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBound

/-!
# The Hyb₀ → Hyb₁ step (CO25 Claim 5.21): PRP/RF switching layer

This module attacks `KeyLemmaHybrids.Hyb01StepResidual` — CO25 Claim 5.21, the Lemma 5.8
birthday switch from the real one-permutation `D_𝔖` world (`Hyb₀`) to the g-encoded forward
world (`Hyb₁`) at cost `claim5_21Bound = (7T² − 3T)/(2|Σ|^c)`, `T = tₕ + 1 + tₚ + L + tₚᵢ`.

## Proven here (no `sorry`, axiom-clean)

**S0 — TV toolkit** (generic, candidates for upstreaming):
- `tsum_probOutput_toReal_mul_tvDist_le`: the weighted TV sum produced by
  `tvDist_bind_left_le` is bounded by any uniform on-support bound on the continuation TVs.
- `probEvent_toReal_sub_le_tvDist`: event-probability differences are dominated by the
  total-variation distance (the data-processing channel that converts a world switch into a
  bad-event probability transfer; consumed by the `DDSFreshSwitchResidual` route).

**S1 — TV accumulator** (the two-implementation companion of
`BirthdayBound.probEvent_simulateQ_stateT_le_sum_of_step`):
- `tvDist_simulateQ_stateT_le_sum_of_step`: if two stateful `QueryImpl`s are within `ε (size s)`
  in TV at every step from a good state `s`, and the right implementation grows the state size
  by at most one per query, then the full `T`-query simulations are within
  `∑_{i<T} ε (size s₀ + i)` in TV. This is the union-bound skeleton of every game-hopping
  "identical-until-bad" argument at the SPMF level.

**S2 — the PRP/RF switching lemma** (the classic birthday switch, at the SPMF level):
- `patchedUniformLogImpl`: fresh-uniform answers, *patched* by an arbitrary resampler on the
  collision event (the lazy-sampling skeleton common to all switch variants).
- `tvDist_freshUniform_patched_le_tight` / `tvDist_freshUniform_patched_le`: **any**
  collision-patched world is within `T(T−1)/(2|X|) ≤ T²/(2|X|)` of the fresh-uniform world,
  for arbitrary adaptive `T`-query-bounded computations — outputs *and* full answer logs.
- `wrUniformLogImpl` (`complementResample`): the without-replacement instantiation — the lazy
  uniform-injection sampler, i.e. the answer behaviour of a uniform permutation on distinct
  forward queries. `wrUniformLogImpl_step_nodup` certifies the no-repeat invariant.
- `tvDist_freshUniform_wrUniform_le_tight` / `tvDist_freshUniform_wrUniform_le`: the
  **PRP-vs-RF switching lemma**: the without-replacement world and the fresh-uniform world are
  within `T(T−1)/(2|X|) ≤ T²/(2|X|)` in total variation.

**S3 — budget recombination** (gap 3 of `BirthdayBound.Lemma5_8EagerBirthdayResidual`):
- `isTotalQueryBound_of_isQueryBoundP_cover`: three covering predicate budgets recombine into
  a total query bound (no disjointness needed).
- `isTotalQueryBound_dsChallenge_of_flavorBudgets` / `..._hyb01TraceLength`: the per-flavor
  `tₕ/tₚ/tₚᵢ` budgets of a duplex-sponge-challenge adversary recombine into
  `IsTotalQueryBound` at `tₕ + tₚ + tₚᵢ`, hence at the Hyb₀/Hyb₁ trace length
  `tₕ + 1 + tₚ + L + tₚᵢ` of `lemma5_8Bound_eq_claim5_21Bound`.

**S5 — proven reductions** (each consumes strictly smaller residuals):
- `lemma5_8Eager_of_freshSplit`: any switch/event split `(εsw, εev)` summing to
  `lemma5_8Bound` discharges `BirthdayBound.Lemma5_8EagerBirthdayResidual`.
- `hyb01Step_of_offEventCoupling_of_birthday`: the off-`E` game coupling plus the Lemma 5.8
  birthday residual discharge `Hyb01StepResidual` (via `lemma5_8Bound_eq_claim5_21Bound`).
- `hyb01Step_of_offEventCoupling_of_freshSplit`: the composition of the two.

## Open core (named `*Residual : Prop`, NOT proven)

- `Hyb01OffEventCouplingResidual` — strictly smaller than `Hyb01StepResidual`: it owes only
  the CO25 §5.6/§5.9–5.10 BackTrack coupling — exhibit a combined prover+verifier adversary
  `Q` at the Hyb₀/Hyb₁ trace length whose `D_𝔖`-world bad-event mass `Pr[E]` dominates
  `Δ(Hyb₀, Hyb₁)`; the numeric side (`Pr[E] ≤ claim5_21Bound`) is no longer owed (it is the
  birthday residual's, discharged separately).
- `DDSFreshSwitchResidual` / `FreshTraceEventResidual` — the split of
  `Lemma5_8EagerBirthdayResidual` along the proven S2 switch: (i) move from the eager
  `(h, p, p⁻¹)` carrier to the all-fresh world (the remaining gap over S2 is the *eager-lazy*
  permutation coupling — one `Equiv.Perm` answering both directions versus the lazy
  `wrUniformLogImpl` view — plus the three-summand spec bookkeeping; the cost channel is
  `probEvent_toReal_sub_le_tvDist` + `tvDist_freshUniform_wrUniform_le`); (ii) the §5.6 event
  decomposition of `E` into capacity-segment collision/landing families in the fresh world,
  where `BirthdayBound.probEvent_collision_freshUniformLog_le` /
  `probEvent_hit_freshUniformHit_le` apply directly.

## Honest status note

The switching lemma proven here compares *fresh-uniform* with *without-replacement* answers.
The eager `D_DS` world additionally answers repeated and inverse queries consistently through
its one `Equiv.Perm`; identifying that world (after dedup, `removeRedundantEntryDS`) with the
lazy `wrUniformLogImpl` view is exactly the eager-lazy coupling left inside
`DDSFreshSwitchResidual` — it is *not* claimed here.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb01Step

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
  BirthdayBound
open scoped NNReal ENNReal

/-! ## S0 — TV toolkit -/

section TVToolkit

/-- S0a — bound the weighted TV sum of `tvDist_bind_left_le` by a uniform on-support bound:
off-support outputs carry zero probability mass, so only the supported continuations matter. -/
lemma tsum_probOutput_toReal_mul_tvDist_le
    {γ β : Type} (mx : ProbComp γ) (f g : γ → ProbComp β) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ support mx, tvDist (f x) (g x) ≤ c) :
    (∑' x, Pr[= x | mx].toReal * tvDist (f x) (g x)) ≤ c := by
  have hsum_le_one : (∑' x : γ, Pr[= x | mx]) ≤ 1 := tsum_probOutput_le_one
  have hsum_ne_top : (∑' x : γ, Pr[= x | mx]) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hsum_le_one
  have hsummable : Summable fun x : γ => Pr[= x | mx].toReal :=
    ENNReal.summable_toReal hsum_ne_top
  have hpt : ∀ x : γ,
      Pr[= x | mx].toReal * tvDist (f x) (g x) ≤ Pr[= x | mx].toReal * c := by
    intro x
    by_cases hx : x ∈ support mx
    · exact mul_le_mul_of_nonneg_left (h x hx) ENNReal.toReal_nonneg
    · rw [probOutput_eq_zero_of_not_mem_support hx]
      simp
  have hlhs : Summable fun x : γ => Pr[= x | mx].toReal * tvDist (f x) (g x) :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)) hpt
      (hsummable.mul_right c)
  refine le_trans (Summable.tsum_le_tsum hpt hlhs (hsummable.mul_right c)) ?_
  rw [tsum_mul_right]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hc) (one_mul c).le
  rw [← ENNReal.tsum_toReal_eq
    (fun x => ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one)]
  simp

/-- S0b — **event differences are dominated by TV distance** (data processing through the
event indicator): for any two games and any event, the difference of event probabilities is at
most the total variation between the games. This is the channel that converts the proven S2
world switch into a bad-event probability transfer for `DDSFreshSwitchResidual`. -/
lemma probEvent_toReal_sub_le_tvDist {α : Type} (g₁ g₂ : ProbComp α) (p : α → Prop) :
    Pr[ p | g₁].toReal - Pr[ p | g₂].toReal ≤ tvDist g₁ g₂ := by
  classical
  have key : ∀ g : ProbComp α,
      Pr[= true | (fun a => decide (p a)) <$> g] = Pr[ p | g] := by
    intro g
    rw [← probEvent_eq_eq_probOutput, probEvent_map]
    simp only [Function.comp_def, decide_eq_true_eq]
  have habs := abs_probOutput_toReal_sub_le_tvDist
    ((fun a => decide (p a)) <$> g₁) ((fun a => decide (p a)) <$> g₂)
  rw [key g₁, key g₂] at habs
  calc Pr[ p | g₁].toReal - Pr[ p | g₂].toReal
      ≤ |Pr[ p | g₁].toReal - Pr[ p | g₂].toReal| := le_abs_self _
    _ ≤ tvDist ((fun a => decide (p a)) <$> g₁) ((fun a => decide (p a)) <$> g₂) := habs
    _ ≤ tvDist g₁ g₂ := tvDist_map_le _ g₁ g₂

end TVToolkit

/-! ## S1 — the TV accumulator: per-step TV costs sum across an adaptive run

Two-implementation companion of `BirthdayBound.probEvent_simulateQ_stateT_le_sum_of_step`:
per-step total-variation costs of a pair of stateful `QueryImpl`s sum across an adaptively
chosen `T`-query computation. The per-step triangle splits the bind through the mixed world
(right implementation, left continuation); `tvDist_bind_right_le` pays the current step and
`tvDist_bind_left_le` + S0a pay the recursive remainder. -/

/-- S1 — **TV accumulator**. Let `impl₁ impl₂` answer queries inside `StateT σ ProbComp`,
`good : σ → Prop` an invariant with size measure `size : σ → ℕ`. If from every good state `s`

* one step of the two implementations is within `ε (size s)` in TV (`hstep_tv`), and
* the right implementation preserves `good` and grows the size by at most one (`hstep_state`),

then any computation making at most `T` queries, started at a good `s₀`, satisfies
`tvDist ≤ ∑_{i<T} ε (size s₀ + i)` between the two simulated worlds (jointly with the final
states). This is the SPMF-level union-bound skeleton of the game-hopping switch arguments
(CO25 Lemma 5.8 / Claim 5.21 included). -/
theorem tvDist_simulateQ_stateT_le_sum_of_step
    {ι' : Type} {spec : OracleSpec ι'} {α σ : Type}
    {impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)}
    {good : σ → Prop} {size : σ → ℕ} {ε : ℕ → ℝ}
    (hmono : Monotone ε) (hnonneg : ∀ m, 0 ≤ ε m)
    (hstep_tv : ∀ (t : spec.Domain) (s : σ), good s →
      tvDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ ε (size s))
    (hstep_state : ∀ (t : spec.Domain) (s : σ), good s →
      ∀ us ∈ support ((impl₂ t).run s), good us.2 ∧ size us.2 ≤ size s + 1)
    {oa : OracleComp spec α} (T : ℕ) (hT : IsTotalQueryBound oa T)
    (s₀ : σ) (h₀ : good s₀) :
    tvDist ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀)
      ≤ ∑ i ∈ Finset.range T, ε (size s₀ + i) := by
  induction oa using OracleComp.inductionOn generalizing T s₀ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      exact Finset.sum_nonneg fun i _ => hnonneg _
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at hT
      obtain ⟨hTpos, hrest⟩ := hT
      simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query,
        monadLift_self]
      have h₁ : tvDist
            ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
          ≤ ε (size s₀) :=
        le_trans (tvDist_bind_right_le _ _ _) (hstep_tv t s₀ h₀)
      have h₂ : tvDist
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2)
            ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (mx us.1)).run us.2)
          ≤ ∑ i ∈ Finset.range (T - 1), ε (size s₀ + 1 + i) := by
        refine le_trans (tvDist_bind_left_le _ _ _) ?_
        refine tsum_probOutput_toReal_mul_tvDist_le _ _ _
          (Finset.sum_nonneg fun i _ => hnonneg _) ?_
        intro us hus
        obtain ⟨hgood, hsize⟩ := hstep_state t s₀ h₀ us hus
        refine le_trans (ih us.1 (T - 1) (hrest us.1) us.2 hgood) ?_
        exact Finset.sum_le_sum fun i _ => hmono (by omega)
      refine le_trans
        (tvDist_triangle _
          ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₁ (mx us.1)).run us.2) _)
        (le_trans (add_le_add h₁ h₂) (le_of_eq ?_))
      have hT1 : T = (T - 1) + 1 := by omega
      conv_rhs => rw [hT1, Finset.sum_range_succ']
      rw [Nat.add_zero, add_comm]
      exact congrArg (· + ε (size s₀))
        (Finset.sum_congr rfl fun i _ => by congr 1; omega)

/-! ## S2 — the PRP/RF switching lemma at the SPMF level

The fresh-uniform world (`BirthdayBound.freshUniformLogImpl`) answers every query by an
independent uniform draw. A *collision-patched* world behaves identically while the fresh draw
misses the answer log and runs an arbitrary resampler on a collision. By the per-step
identical-until-bad bound (`tvDist_bind_left_event_le`) one step costs at most
`Pr[collision] ≤ |log|/|X|`; the S1 accumulator sums these to the birthday bound. The
without-replacement instantiation `wrUniformLogImpl` is the lazy uniform-injection sampler —
the answer behaviour of a uniform permutation on distinct forward queries — giving the classic
PRP-vs-RF switching lemma. -/

section Switching

variable (A X : Type) [SampleableType X] [Fintype X] [DecidableEq X]

/-- S2a — collision-patched fresh-uniform answer oracle: a fresh uniform draw is used (and
logged) while it misses the answer log; on a collision the arbitrary resampler `patch` takes
over. All switch variants (without-replacement, conditioned resampling, abort) share this
skeleton. -/
noncomputable def patchedUniformLogImpl
    (patch : A → List X → ProbComp (X × List X)) :
    QueryImpl (A →ₒ X) (StateT (List X) ProbComp) :=
  fun a l => do
    let x ← ($ᵗ X : ProbComp X)
    if x ∈ l then patch a l else pure (x, x :: l)

omit [Fintype X] in
/-- The patched step is the fresh-uniform draw bound into the collision test (definitional
unfolding, used to expose the `mx >>= f` vs `mx >>= g` shape). -/
lemma patchedUniformLogImpl_run_eq (patch : A → List X → ProbComp (X × List X))
    (a : A) (l : List X) :
    (patchedUniformLogImpl A X patch a).run l
      = ($ᵗ X : ProbComp X) >>= fun x =>
          if x ∈ l then patch a l else pure (x, x :: l) := rfl

omit [Fintype X] [DecidableEq X] in
/-- The fresh-uniform step in bind form (definitional unfolding of
`BirthdayBound.freshUniformLogImpl`). -/
lemma freshUniformLogImpl_run_eq (a : A) (l : List X) :
    (freshUniformLogImpl A X a).run l
      = ($ᵗ X : ProbComp X) >>= fun x => pure (x, x :: l) := by
  change (fun x => (x, x :: l)) <$> ($ᵗ X : ProbComp X) = _
  rw [map_eq_bind_pure_comp]
  rfl

/-- S2b — **per-step switch cost**: one fresh-uniform step and one collision-patched step
from the same answer log `l` are within `|l|/|X|` in total variation — they share the uniform
draw and only diverge on the collision event (`tvDist_bind_left_event_le`). -/
lemma patchedUniformLogImpl_step_tvDist_le [Nonempty X]
    (patch : A → List X → ProbComp (X × List X)) (a : A) (l : List X) :
    tvDist ((freshUniformLogImpl A X a).run l) ((patchedUniformLogImpl A X patch a).run l)
      ≤ (l.length : ℝ) / (Fintype.card X : ℝ) := by
  rw [freshUniformLogImpl_run_eq, patchedUniformLogImpl_run_eq]
  refine le_trans
    (tvDist_bind_left_event_le ($ᵗ X : ProbComp X) _ _ (fun x => x ∈ l)
      (fun x hx => by rw [if_neg hx])) ?_
  have hev : Pr[ fun x : X => x ∈ l | ($ᵗ X : ProbComp X)]
      ≤ (l.length : ℝ≥0∞) * (Fintype.card X : ℝ≥0∞)⁻¹ := by
    rw [probEvent_uniformSample, div_eq_mul_inv]
    refine mul_le_mul' ?_ le_rfl
    calc ((Finset.univ.filter (fun x : X => x ∈ l)).card : ℝ≥0∞)
        ≤ (l.toFinset.card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_le_card fun x hx =>
            List.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
      _ ≤ (l.length : ℝ≥0∞) := by exact_mod_cast l.toFinset_card_le
  refine le_trans (ENNReal.toReal_mono ?_ hev) (le_of_eq ?_)
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero (α := X)))
  · rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, div_eq_mul_inv]

omit [Fintype X] in
/-- The patched step grows the answer log by at most one entry, provided the patch does. -/
lemma patchedUniformLogImpl_step_support
    (patch : A → List X → ProbComp (X × List X))
    (hpatch : ∀ a l, ∀ us ∈ support (patch a l), us.2.length ≤ l.length + 1)
    (a : A) (l : List X) :
    ∀ us ∈ support ((patchedUniformLogImpl A X patch a).run l),
      us.2.length ≤ l.length + 1 := by
  intro us hus
  rw [patchedUniformLogImpl_run_eq, support_bind] at hus
  simp only [Set.mem_iUnion] at hus
  obtain ⟨x, _, hus⟩ := hus
  by_cases hxl : x ∈ l
  · rw [if_pos hxl] at hus
    exact hpatch a l us hus
  · rw [if_neg hxl, support_pure, Set.mem_singleton_iff] at hus
    subst hus
    simp

/-- S2c (tight) — **generalized switching lemma**: any collision-patched world is within
`T(T−1)/(2|X|)` of the fresh-uniform world across `T` adaptive queries, jointly with the
final answer logs. S1 accumulator at `ε m = m/|X|` plus the Gauss sum. -/
theorem tvDist_freshUniform_patched_le_tight [Nonempty X] {α : Type}
    (patch : A → List X → ProbComp (X × List X))
    (hpatch : ∀ a l, ∀ us ∈ support (patch a l), us.2.length ≤ l.length + 1)
    (oa : OracleComp (A →ₒ X) α) (T : ℕ) (hT : IsTotalQueryBound oa T) :
    tvDist ((simulateQ (freshUniformLogImpl A X) oa).run [])
        ((simulateQ (patchedUniformLogImpl A X patch) oa).run [])
      ≤ ((T * (T - 1) : ℕ) : ℝ) / (2 * (Fintype.card X : ℝ)) := by
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := tvDist_simulateQ_stateT_le_sum_of_step
    (impl₁ := freshUniformLogImpl A X)
    (impl₂ := patchedUniformLogImpl A X patch)
    (good := fun _ => True) (size := List.length)
    (ε := fun m => (m : ℝ) / (Fintype.card X : ℝ))
    (fun m₁ m₂ hm => by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hcard.le)
    (fun m => by positivity)
    (fun t s _ => patchedUniformLogImpl_step_tvDist_le A X patch t s)
    (fun t s _ us hus =>
      ⟨trivial, patchedUniformLogImpl_step_support A X patch hpatch t s us hus⟩)
    T hT [] trivial
  refine le_trans h (le_of_eq ?_)
  simp only [List.length_nil, Nat.zero_add]
  rw [← Finset.sum_div]
  have h2 : ((T * (T - 1) : ℕ) : ℝ) = (∑ i ∈ Finset.range T, (i : ℝ)) * 2 := by
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.sum_range_id_mul_two T).symm
  rw [h2]
  field_simp

/-- S2c — generalized switching lemma, squared form `T²/(2|X|)`. -/
theorem tvDist_freshUniform_patched_le [Nonempty X] {α : Type}
    (patch : A → List X → ProbComp (X × List X))
    (hpatch : ∀ a l, ∀ us ∈ support (patch a l), us.2.length ≤ l.length + 1)
    (oa : OracleComp (A →ₒ X) α) (T : ℕ) (hT : IsTotalQueryBound oa T) :
    tvDist ((simulateQ (freshUniformLogImpl A X) oa).run [])
        ((simulateQ (patchedUniformLogImpl A X patch) oa).run [])
      ≤ (T : ℝ) ^ 2 / (2 * (Fintype.card X : ℝ)) := by
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  refine le_trans (tvDist_freshUniform_patched_le_tight A X patch hpatch oa T hT) ?_
  have hnum : ((T * (T - 1) : ℕ) : ℝ) ≤ (T : ℝ) ^ 2 := by
    calc ((T * (T - 1) : ℕ) : ℝ) ≤ ((T * T : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left T (Nat.sub_le T 1)
      _ = (T : ℝ) ^ 2 := by push_cast; ring
  exact div_le_div_of_nonneg_right hnum (by linarith)

/-- S2d — uniform resampling from the complement of the answer log (the without-replacement
draw of the lazy permutation sampler). Falls back to a full uniform draw when the log already
exhausts `X` (unreachable from duplicate-free logs of length `< |X|`). -/
noncomputable def complementResample (l : List X) : ProbComp X :=
  match (Finset.univ.filter (fun x : X => x ∉ l)).toList with
  | [] => ($ᵗ X : ProbComp X)
  | y :: ys =>
      (fun i : Fin (ys.length + 1) => (y :: ys).get i) <$>
        ($ᵗ (Fin (ys.length + 1)) : ProbComp _)

/-- When the log does not exhaust `X`, the complement resampler only produces fresh values. -/
lemma complementResample_support_not_mem (l : List X) (hne : ∃ x : X, x ∉ l) :
    ∀ y ∈ support (complementResample X l), y ∉ l := by
  intro y hy
  rcases hl : (Finset.univ.filter (fun x : X => x ∉ l)).toList with - | ⟨y₀, ys⟩
  · exfalso
    obtain ⟨x, hx⟩ := hne
    have hmem : x ∈ Finset.univ.filter (fun x : X => x ∉ l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    rw [← Finset.mem_toList, hl] at hmem
    simp at hmem
  · rw [show complementResample X l
        = (fun i : Fin (ys.length + 1) => (y₀ :: ys).get i) <$>
            ($ᵗ (Fin (ys.length + 1)) : ProbComp _) by
          unfold complementResample
          rw [hl]] at hy
    rw [support_map] at hy
    obtain ⟨i, _, rfl⟩ := hy
    change (y₀ :: ys).get i ∉ l
    have hmem : (y₀ :: ys).get i
        ∈ (Finset.univ.filter (fun x : X => x ∉ l)).toList := by
      rw [hl]
      exact List.get_mem _ _
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2

/-- S2e — the **without-replacement sampler** (lazy uniform-injection / lazy-PRP view):
fresh uniform answers, resampled uniformly from the unused values on a collision. -/
noncomputable def wrUniformLogImpl : QueryImpl (A →ₒ X) (StateT (List X) ProbComp) :=
  patchedUniformLogImpl A X fun _ l => (fun y => (y, y :: l)) <$> complementResample X l

/-- The without-replacement world preserves duplicate-freeness of the answer log (so from
`[]` its answers are the lazy view of a uniformly sampled injection — the PRP answer
behaviour on distinct forward queries). -/
lemma wrUniformLogImpl_step_nodup (a : A) (l : List X) (hl : l.Nodup)
    (hlen : l.length < Fintype.card X) :
    ∀ us ∈ support ((wrUniformLogImpl A X a).run l), us.2.Nodup := by
  have hne : ∃ x : X, x ∉ l := by
    by_contra hall
    have hall' : ∀ x : X, x ∈ l := fun x => not_not.mp (not_exists.mp hall x)
    have hcard : (Finset.univ : Finset X).card ≤ l.toFinset.card :=
      Finset.card_le_card fun x _ => List.mem_toFinset.mpr (hall' x)
    rw [Finset.card_univ, List.toFinset_card_of_nodup hl] at hcard
    omega
  intro us hus
  rw [show (wrUniformLogImpl A X a).run l
      = ($ᵗ X : ProbComp X) >>= fun x =>
          if x ∈ l then (fun y => (y, y :: l)) <$> complementResample X l
          else pure (x, x :: l) from rfl, support_bind] at hus
  simp only [Set.mem_iUnion] at hus
  obtain ⟨x, _, hus⟩ := hus
  by_cases hxl : x ∈ l
  · rw [if_pos hxl, support_map] at hus
    obtain ⟨y, hy, rfl⟩ := hus
    exact List.nodup_cons.mpr ⟨complementResample_support_not_mem X l hne y hy, hl⟩
  · rw [if_neg hxl, support_pure, Set.mem_singleton_iff] at hus
    subst hus
    exact List.nodup_cons.mpr ⟨hxl, hl⟩

/-- S2 (tight) — **the PRP-vs-RF switching lemma at the SPMF level**: across `T` adaptive
queries, the fresh-uniform world and the without-replacement world (the lazy view of a
uniformly sampled injection, i.e. of a uniform permutation on distinct forward queries) are
within `T(T−1)/(2|X|)` in total variation — outputs and answer logs jointly. -/
theorem tvDist_freshUniform_wrUniform_le_tight [Nonempty X] {α : Type}
    (oa : OracleComp (A →ₒ X) α) (T : ℕ) (hT : IsTotalQueryBound oa T) :
    tvDist ((simulateQ (freshUniformLogImpl A X) oa).run [])
        ((simulateQ (wrUniformLogImpl A X) oa).run [])
      ≤ ((T * (T - 1) : ℕ) : ℝ) / (2 * (Fintype.card X : ℝ)) :=
  tvDist_freshUniform_patched_le_tight A X _
    (fun a l us hus => by
      rw [support_map] at hus
      obtain ⟨y, -, rfl⟩ := hus
      simp)
    oa T hT

/-- S2 — the PRP-vs-RF switching lemma, squared form `T²/(2|X|)` (the shape quoted by the
CO25 §5.8 accounting). -/
theorem tvDist_freshUniform_wrUniform_le [Nonempty X] {α : Type}
    (oa : OracleComp (A →ₒ X) α) (T : ℕ) (hT : IsTotalQueryBound oa T) :
    tvDist ((simulateQ (freshUniformLogImpl A X) oa).run [])
        ((simulateQ (wrUniformLogImpl A X) oa).run [])
      ≤ (T : ℝ) ^ 2 / (2 * (Fintype.card X : ℝ)) :=
  tvDist_freshUniform_patched_le A X _
    (fun a l us hus => by
      rw [support_map] at hus
      obtain ⟨y, -, rfl⟩ := hus
      simp)
    oa T hT

end Switching

/-! ## S3 — budget recombination: per-flavor budgets to a total query bound

Gap 3 of `BirthdayBound.Lemma5_8EagerBirthdayResidual`: CO25 Lemma 5.8 is applied at the
*total* trace length, while the Key-Lemma surface hands out per-flavor budgets `tₕ/tₚ/tₚᵢ`. -/

section BudgetRecombination

/-- S3a — **covering predicate budgets recombine**: if every oracle index satisfies at least
one of three predicates (no disjointness needed) and `oa` is `IsQueryBoundP`-bounded for each,
then `oa` makes at most `b₁ + b₂ + b₃` queries in total. -/
theorem isTotalQueryBound_of_isQueryBoundP_cover
    {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    {p₁ p₂ p₃ : ι' → Prop} [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p₃]
    (hcover : ∀ i, p₁ i ∨ p₂ i ∨ p₃ i)
    {oa : OracleComp spec α} {b₁ b₂ b₃ : ℕ}
    (h₁ : IsQueryBoundP oa p₁ b₁) (h₂ : IsQueryBoundP oa p₂ b₂)
    (h₃ : IsQueryBoundP oa p₃ b₃) :
    IsTotalQueryBound oa (b₁ + b₂ + b₃) := by
  induction oa using OracleComp.inductionOn generalizing b₁ b₂ b₃ with
  | pure x => exact trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h₁ h₂ h₃
      rw [isTotalQueryBound_query_bind_iff]
      have hpos : 0 < b₁ + b₂ + b₃ := by
        rcases hcover t with hp | hp | hp
        · rcases h₁.1 with hn | hb
          · exact absurd hp hn
          · omega
        · rcases h₂.1 with hn | hb
          · exact absurd hp hn
          · omega
        · rcases h₃.1 with hn | hb
          · exact absurd hp hn
          · omega
      refine ⟨hpos, fun u => ?_⟩
      refine (ih u (h₁.2 u) (h₂.2 u) (h₃.2 u)).mono ?_
      rcases hcover t with hp | hp | hp
      · rcases h₁.1 with hn | hb
        · exact absurd hp hn
        · simp only [if_pos hp]
          split_ifs <;> omega
      · rcases h₂.1 with hn | hb
        · exact absurd hp hn
        · simp only [if_pos hp]
          split_ifs <;> omega
      · rcases h₃.1 with hn | hb
        · exact absurd hp hn
        · simp only [if_pos hp]
          split_ifs <;> omega

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize]

/-- S3b — **flavor budgets recombine** for a duplex-sponge-challenge adversary: the hash /
forward-perm / inverse-perm budgets of `Q` give `IsTotalQueryBound Q (tₕ + tₚ + tₚᵢ)` (the
three summands cover the whole index type of `duplexSpongeChallengeOracle`). -/
theorem isTotalQueryBound_dsChallenge_of_flavorBudgets
    {β : Type} (Q : OracleComp (duplexSpongeChallengeOracle StmtIn U) β)
    {tₕ tₚ tₚᵢ : ℕ}
    (hh : IsQueryBoundP Q (fun j => j matches .inl _) tₕ)
    (hp : IsQueryBoundP Q (fun j => j matches .inr (.inl _)) tₚ)
    (hpi : IsQueryBoundP Q (fun j => j matches .inr (.inr _)) tₚᵢ) :
    IsTotalQueryBound Q (tₕ + tₚ + tₚᵢ) :=
  isTotalQueryBound_of_isQueryBoundP_cover
    (fun j => by rcases j with _ | (_ | _) <;> simp) hh hp hpi

/-- S3c — flavor budgets dominate the Hyb₀/Hyb₁ trace length: the adversary's own
`tₕ + tₚ + tₚᵢ` queries are within the CO25 Lemma 5.8 budget `T = tₕ + 1 + tₚ + L + tₚᵢ`
(the `+1+L` slack is the re-deriving verifier's, accounted inside the coupling residual). -/
theorem isTotalQueryBound_dsChallenge_hyb01TraceLength
    {β : Type} (Q : OracleComp (duplexSpongeChallengeOracle StmtIn U) β)
    {tₕ tₚ tₚᵢ : ℕ} (L : ℕ)
    (hh : IsQueryBoundP Q (fun j => j matches .inl _) tₕ)
    (hp : IsQueryBoundP Q (fun j => j matches .inr (.inl _)) tₚ)
    (hpi : IsQueryBoundP Q (fun j => j matches .inr (.inr _)) tₚᵢ) :
    IsTotalQueryBound Q (tₕ + 1 + tₚ + L + tₚᵢ) :=
  (isTotalQueryBound_dsChallenge_of_flavorBudgets Q hh hp hpi).mono (by omega)

end BudgetRecombination

/-! ## S4 — the logged `D_𝔖` world, the all-fresh world, and the split of the Lemma 5.8
eager birthday residual -/

section FreshWorlds

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

variable (StmtIn U : Type) [SpongeUnit U] [SpongeSize] [Fintype U] [DecidableEq U]

/-- S4a — the all-fresh duplex-sponge-challenge realization: every hash, forward-perm and
inverse-perm query is answered by an independent uniform draw (no carrier is sampled; no
consistency across repeats or directions). This is the world where the generic fresh-uniform
bricks of `BirthdayBound` (R1b/R1c) apply directly. -/
noncomputable def freshDSChallengeImpl [SampleableType U] :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U) ProbComp :=
  fun q =>
    match q with
    | .inl _ => ($ᵗ (Vector U SpongeSize.C) : ProbComp _)
    | .inr (.inl _) => ($ᵗ (CanonicalSpongeState U) : ProbComp _)
    | .inr (.inr _) => ($ᵗ (CanonicalSpongeState U) : ProbComp _)

/-- The logged eager `D_𝔖`-carrier game of `BirthdayBound.Lemma5_8EagerBirthdayResidual`:
sample the `(h, p, p⁻¹)` carrier once, answer `Q` through it, log the trace. -/
noncomputable def ddsLoggedGame
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    {β : Type} (Q : OracleComp (duplexSpongeChallengeOracle StmtIn U) β) :
    ProbComp (β × QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let c ← (D_DS StmtIn U).sample
  simulateQ ((D_DS StmtIn U).toImpl c) ((simulateQ loggingOracle Q).run)

/-- The logged all-fresh game: answer `Q` through `freshDSChallengeImpl`, log the trace. -/
noncomputable def freshDSLoggedGame [SampleableType U]
    {β : Type} (Q : OracleComp (duplexSpongeChallengeOracle StmtIn U) β) :
    ProbComp (β × QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  simulateQ (freshDSChallengeImpl StmtIn U) ((simulateQ loggingOracle Q).run)

variable [SampleableType U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- S4b residual — **the eager-lazy carrier switch** (one leg of the
`Lemma5_8EagerBirthdayResidual` split): moving the §5.6 bad-event mass from the eager
`(h, p, p⁻¹)` carrier world to the all-fresh world costs at most `εsw T`.

**Exact gap to the proven bricks of this file.** `probEvent_toReal_sub_le_tvDist` reduces
this to a TV bound between `ddsLoggedGame` and `freshDSLoggedGame`; the S2 switching lemma
(`tvDist_freshUniform_wrUniform_le`) proves the `T²/(2|X|)` bound between *fresh* and
*without-replacement* single-oracle worlds. What remains is the eager-lazy coupling: the once-
sampled `Equiv.Perm` answering both `p` and `p⁻¹` (and the once-sampled `h` answering repeated
hash queries consistently) versus the corresponding lazy samplers over the three-summand spec,
mediated by the dedup'd trace (`removeRedundantEntryDS`). -/
def DDSFreshSwitchResidual (εsw : ℕ → ℝ) : Prop :=
  ∀ {β : Type} (Q : OracleComp (duplexSpongeChallengeOracle StmtIn U) β) (T : ℕ),
    IsTotalQueryBound Q T →
    (Pr[ fun z : β × QueryLog (duplexSpongeChallengeOracle StmtIn U) => E z.2 |
        ddsLoggedGame StmtIn U Q]).toReal
      ≤ (Pr[ fun z : β × QueryLog (duplexSpongeChallengeOracle StmtIn U) => E z.2 |
          freshDSLoggedGame StmtIn U Q]).toReal + εsw T

/-- S4c residual — **the fresh-world event decomposition** (the other leg of the
`Lemma5_8EagerBirthdayResidual` split): in the all-fresh world the §5.6 event `E` of the
logged trace has mass at most `εev T`. This is where `E = E_dup ∨ E_func` is split into the
capacity-segment collision/landing families counted by the CO25 Lemma 5.8 numerator; the
fresh-uniform bricks `BirthdayBound.probEvent_collision_freshUniformLog_le` (collisions at
`T(T−1)/(2|X|)`) and `BirthdayBound.probEvent_hit_freshUniformHit_le` (landings at `Tk/|X|`)
with the `capacitySegment` projection and `hit_toReal_le_capacityRatio` are the intended
per-family bounds. -/
def FreshTraceEventResidual (εev : ℕ → ℝ) : Prop :=
  ∀ {β : Type} (Q : OracleComp (duplexSpongeChallengeOracle StmtIn U) β) (T : ℕ),
    IsTotalQueryBound Q T →
    (Pr[ fun z : β × QueryLog (duplexSpongeChallengeOracle StmtIn U) => E z.2 |
        freshDSLoggedGame StmtIn U Q]).toReal ≤ εev T

variable {StmtIn U}

/-- S5a — **proven reduction**: any switch/event split `(εsw, εev)` summing to
`lemma5_8Bound` discharges the round-1 open core
`BirthdayBound.Lemma5_8EagerBirthdayResidual`. Pure triangle arithmetic; the two legs are
strictly smaller than the combined residual (neither owes the other's bound nor the final
numerics). -/
theorem lemma5_8Eager_of_freshSplit (εsw εev : ℕ → ℝ)
    (hsw : DDSFreshSwitchResidual StmtIn U εsw)
    (hev : FreshTraceEventResidual StmtIn U εev)
    (hsum : ∀ T : ℕ, εsw T + εev T ≤ lemma5_8Bound U T) :
    Lemma5_8EagerBirthdayResidual StmtIn U := by
  intro β Q T hT
  have h1 := hsw Q T hT
  have h2 := hev Q T hT
  have h3 := hsum T
  have hgame : (do
      let c ← (D_DS StmtIn U).sample
      simulateQ ((D_DS StmtIn U).toImpl c) ((simulateQ loggingOracle Q).run))
      = ddsLoggedGame StmtIn U Q := rfl
  rw [hgame]
  linarith

end FreshWorlds

/-! ## S5 — the off-`E` coupling residual and the proven discharge of `Hyb01StepResidual` -/

section Hyb01Reduction

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-- S5b residual — **the off-`E` BackTrack coupling** (CO25 §5.6 / Lemmas 5.9–5.10 + the
Claim 5.21 game rewrite), strictly smaller than `Hyb01StepResidual`: exhibit a combined
prover+verifier adversary `Q` against the bare duplex-sponge challenge oracle, within the
Hyb₀/Hyb₁ trace budget `tₕ + 1 + tₚ + L + tₚᵢ` (the prover's three flavor budgets recombined
by `isTotalQueryBound_dsChallenge_hyb01TraceLength`, plus the re-deriving verifier's one hash
and `≤ L` permutation queries), such that off the trace event `E` the two hybrids couple
exactly — so the whole `Δ(Hyb₀, Hyb₁)` is dominated by the `D_𝔖`-world mass of `E`.

Neither the numeric bound on `Pr[E]` (that is `Lemma5_8EagerBirthdayResidual`'s) nor the final
`claim5_21Bound` identification (proven below) is owed here. -/
def Hyb01OffEventCouplingResidual [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    ∃ (β : Type) (Q : OracleComp (duplexSpongeChallengeOracle StmtIn U) β),
      IsTotalQueryBound Q (tₕ + 1 + tₚ + L + tₚᵢ) ∧
      SPMF.tvDist (Hyb0 T_H T_P δ oImpl V P) (Hyb1 T_H T_P δ oImpl V P)
        ≤ (Pr[ fun z : β × QueryLog (duplexSpongeChallengeOracle StmtIn U) => E z.2 |
            do
              let c ← (D_DS StmtIn U).sample
              simulateQ ((D_DS StmtIn U).toImpl c)
                ((simulateQ loggingOracle Q).run)]).toReal

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- S5c — **proven reduction for Claim 5.21**: the off-`E` coupling residual plus the round-1
Lemma 5.8 eager birthday residual discharge `Hyb01StepResidual`. The trace-length bookkeeping
is `lemma5_8Bound_eq_claim5_21Bound` (definitional). -/
theorem hyb01Step_of_offEventCoupling_of_birthday [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hC : Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (h58 : Lemma5_8EagerBirthdayResidual StmtIn U) :
    Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  obtain ⟨β, Q, hQbound, hQtv⟩ := hC V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  refine le_trans hQtv ?_
  have h := h58 Q (tₕ + 1 + tₚ + L + tₚᵢ) hQbound
  rw [lemma5_8Bound_eq_claim5_21Bound] at h
  exact h

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- S5d — composition: the off-`E` coupling plus any switch/event split summing to
`lemma5_8Bound` discharge `Hyb01StepResidual` outright. -/
theorem hyb01Step_of_offEventCoupling_of_freshSplit [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hC : Hyb01OffEventCouplingResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (εsw εev : ℕ → ℝ)
    (hsw : DDSFreshSwitchResidual StmtIn U εsw)
    (hev : FreshTraceEventResidual StmtIn U εev)
    (hsum : ∀ T : ℕ, εsw T + εev T ≤ lemma5_8Bound U T) :
    Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  hyb01Step_of_offEventCoupling_of_birthday T_H T_P δ oImpl hC
    (lemma5_8Eager_of_freshSplit εsw εev hsw hev hsum)

end Hyb01Reduction

end DuplexSpongeFS.Hyb01Step

#print axioms DuplexSpongeFS.Hyb01Step.tsum_probOutput_toReal_mul_tvDist_le
#print axioms DuplexSpongeFS.Hyb01Step.probEvent_toReal_sub_le_tvDist
#print axioms DuplexSpongeFS.Hyb01Step.tvDist_simulateQ_stateT_le_sum_of_step
#print axioms DuplexSpongeFS.Hyb01Step.patchedUniformLogImpl_step_tvDist_le
#print axioms DuplexSpongeFS.Hyb01Step.patchedUniformLogImpl_step_support
#print axioms DuplexSpongeFS.Hyb01Step.tvDist_freshUniform_patched_le_tight
#print axioms DuplexSpongeFS.Hyb01Step.tvDist_freshUniform_patched_le
#print axioms DuplexSpongeFS.Hyb01Step.complementResample_support_not_mem
#print axioms DuplexSpongeFS.Hyb01Step.wrUniformLogImpl_step_nodup
#print axioms DuplexSpongeFS.Hyb01Step.tvDist_freshUniform_wrUniform_le_tight
#print axioms DuplexSpongeFS.Hyb01Step.tvDist_freshUniform_wrUniform_le
#print axioms DuplexSpongeFS.Hyb01Step.isTotalQueryBound_of_isQueryBoundP_cover
#print axioms DuplexSpongeFS.Hyb01Step.isTotalQueryBound_dsChallenge_of_flavorBudgets
#print axioms DuplexSpongeFS.Hyb01Step.isTotalQueryBound_dsChallenge_hyb01TraceLength
#print axioms DuplexSpongeFS.Hyb01Step.lemma5_8Eager_of_freshSplit
#print axioms DuplexSpongeFS.Hyb01Step.hyb01Step_of_offEventCoupling_of_birthday
#print axioms DuplexSpongeFS.Hyb01Step.hyb01Step_of_offEventCoupling_of_freshSplit

end
