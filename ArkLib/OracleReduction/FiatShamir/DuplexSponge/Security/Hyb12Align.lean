/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb12Step

/-!
# `Hyb₁ → Hyb12Mid` fiber-resample alignment: the table-level identity + the lazy/repeat split

This module attacks `Hyb12Step.Hyb12ResampleAlignResidual` (`Δ(Hyb₁, Hyb12Mid) = 0`), the
"fiber resampling is invisible" leg of the CO25 Claim 5.22 resample split.

## The table-level identity (PROVEN, transported through the game)

The eager surface makes the per-derivation identity `map_bind_uniformFiber_eq_uniform` a
statement about the *whole sampled `gSpec` table*: resampling each cell `c q` of a uniform
table inside its own `ψ_q`-fiber is the same as resampling the table `c` inside the fiber of
the induced map `Ψ(c) := fun q => ψ_q (c q)` (the product of the cell fibers **is** the
`Ψ`-fiber), and resampling a uniform draw inside its own fiber is invisible. Proven here:

- `evalDist_fiberResampleSampler` — the generic **table identity** in sampler form: for any
  `ψ : V → M`, drawing `c ← 𝒰(V)` and then a uniform element of `ψ⁻¹(ψ(c))` is distributed
  exactly as `𝒰(V)` (subtype-fiber form of `Hyb12Step.map_bind_uniformFiber_eq_uniform`,
  with no surjectivity hypothesis — only reached fibers are sampled).
- `evalDist_hybGameEager_functionTable_congr` — **game transport**: `hybGameEager` reads its
  challenge-oracle distribution only through `sample` (once, eagerly) and the deterministic
  `tableQueryImpl`, so function-table distributions with equal `𝒟[sample]` give equal games.
- `hyb1_eq_hyb1TableResampled` / `tvDist_hyb1_hyb1TableResampled` — the **DSFS table-level
  alignment, closed outright**: `Hyb₁` equals the same game run against the per-cell
  `ψ`-fiber-resampled uniform `gSpec` table (`Δ = 0`, an equality of `SPMF`s).

## Why this does not close `Hyb12ResampleAlignResidual` outright (honest analysis)

`Hyb12Mid` does **not** resample the table per cell: `gImplEncodedResampled` (inner state
`PUnit`, no memo) draws a *fresh* `ψ⁻¹`-preimage from the `unifSpec` summand at **every**
`gSpec` query. The two notions agree on the *first* read of each table cell and diverge on
repeats: per-cell resampling answers a repeated key with the same value, per-query
resampling answers it with a fresh independent fiber draw.

Where repeats can actually occur and what they expose (from `ProverTransform.lean`):

1. `d2sHandleBacktrackSome` issues the Item 4(e)i `gᵢ` query **unconditionally**; on a
   `tr_∇.p` hit (Item 4(e)ii) the answer is **discarded**, and the upstream `D2SAlgoMemo`
   docstring states explicitly that without a memo the `uniformDeserializePreimage`
   randomness "would give them different responses, violating CO25 §5.4 D2SAlgo Item 3".
2. The **log channel is insensitive**: `loggingOracle` sits outside `d2fRaw`, so the logged
   response of a `gSpec` query is the *table* value `c q` (identical in `Hyb₁`/`Hyb12Mid`);
   the resample coins are `unifSpec` entries dropped by `projectChallengePlusUnitQueryLog`;
   and `hyb1Line4TraceEager` keeps only `ψ(response)`, a fiber invariant.
3. The **verifier-side re-derivation is insensitive**: the verifier run restarts from a
   `default` `D2SQueryState`, re-deriving the prover's keys, but the verifier consumes only
   the *decoded* squeezed challenges `ψ(v)` — equal across fiber mates.
4. The remaining channel is **prover-side**: a repeated key reached via two *distinct*
   sponge states that both miss the `p`-table (capacity collisions among fresh-sampled
   states, or `p⁻¹`-grafted chains that luckily hit a valid start state). On such paths the
   synthesized squeeze states expose raw fiber mates (`Hyb₁`: equal rate blocks; `Hyb12Mid`:
   independent fiber draws), which is observable whenever some decoder `ψᵢ` is non-injective.
   These paths have positive (birthday-sized) probability, so the **exact-`0`** claim for
   the repeat leg is DOUBTFUL in general; CO25 inserts the `tr_i` memo (§5.4 Item 3) to
   delete this channel and charges collision paths to birthday terms (§5.6, Lemma 5.8 / Eq.
   55), never claiming exact `0` against an unmemoized resampler.

## The finer split (named residuals + proven assembly)

The pivot is `Hyb12MidMemo`: `Hyb12Mid` with the per-query resampler replaced by
`gImplEncodedResampledMemo`, which still queries the eager table on every derivation (log
shape preserved, point 2 above) but memoizes the fiber draw per encoded key — the in-tree
`tr_i` memo (`D2SAlgoMemo`) specialized to the `Hyb₁ → Hyb₂` switch.

- `Hyb12LazyEagerResampleResidual` (A) — `Δ(Hyb₁, Hyb12MidMemo) = 0`: lazily resampling each
  *distinct* key once (at first read) matches the eagerly fiber-resampled table, which by
  the proven table identity *is* the uniform table. No repeat issue remains (the memo serves
  repeats); the open content is a lazy/eager induction in the style of
  `RandomOracleEagerTableDep` plus the `ψ`-image log decoupling of point 2. Plausibly TRUE.
- `Hyb12RepeatDerivationResidual` (B) — `Δ(Hyb12MidMemo, Hyb12Mid) = 0`: memoizing the fiber
  draw on repeated derivation keys is invisible. This isolates exactly the doubtful channel
  of point 4 (DOUBTFUL for non-injective decoders; TRUE when every `codec.decode i` is
  injective, where fibers are singletons and both sides return the unique preimage). An
  honest general repair would weaken `= 0` to a birthday-sized bound, which would propagate
  to a (still `ηStar`-compatible) relaxation of the resample split.
- `hyb12ResampleAlign_of_lazySplit` (**proven**): A and B assemble into
  `Hyb12ResampleAlignResidual` by the TV triangle inequality.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb12Align

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open Hyb12Step
open scoped NNReal ENNReal

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## Generic fiber-resampling sampler and the table identity

`fiberResampleSampler ψ` is the `ProbComp` sampler "draw `c` uniformly, then redraw a
uniform element of the `ψ`-fiber of `ψ(c)`". At `V := OracleFamily (gSpec …)` and
`ψ := Ψ = (decode ∘ ·)` applied cellwise, the `Ψ`-fiber of a table is exactly the product of
the per-cell decoder fibers, so this *is* the per-cell fiber resampling of the whole table.
The instances on the fiber subtype are pinned through explicit defs (`fiberFintype`,
`fiberSampleable`) so that the distribution computation can refer to them verbatim. -/

section FiberResample

variable {V M : Type}

/-- Pinned `Fintype` instance for the `ψ`-fiber subtype of `ψ c` (classical decidability of
the fiber predicate; `Fintype.ofFinite` carrier). -/
@[reducible] noncomputable def fiberFintype [Finite V] (ψ : V → M) (c : V) :
    Fintype {d : V // ψ c = ψ d} :=
  @Subtype.fintype V (fun d => ψ c = ψ d) (fun d => Classical.decEq M (ψ c) (ψ d))
    (Fintype.ofFinite V)

/-- The `ψ`-fiber of `ψ c` contains `c`. -/
@[reducible] def fiberNonempty (ψ : V → M) (c : V) : Nonempty {d : V // ψ c = ψ d} :=
  ⟨⟨c, rfl⟩⟩

/-- Pinned `SampleableType` instance for the `ψ`-fiber subtype of `ψ c`. -/
@[reducible] noncomputable def fiberSampleable [Finite V] (ψ : V → M) (c : V) :
    SampleableType {d : V // ψ c = ψ d} :=
  @SampleableType.ofFintype _ (fiberFintype ψ c) (fiberNonempty ψ c)

/-- Draw a uniform element of the `ψ`-fiber of `ψ c`. -/
noncomputable def fiberResampleDraw [Finite V] (ψ : V → M) (c : V) : ProbComp V :=
  Subtype.val <$> @uniformSample {d : V // ψ c = ψ d} (fiberSampleable ψ c)

/-- The fiber-resampled uniform sampler: `c ← 𝒰(V); c' ← 𝒰(ψ⁻¹(ψ(c)))`. -/
noncomputable def fiberResampleSampler [SampleableType V] (ψ : V → M) : ProbComp V :=
  ($ᵗ V) >>= fiberResampleDraw ψ

/-- Output law of one fiber draw, on-fiber case: uniform on the fiber of `ψ c`. -/
lemma probOutput_fiberResampleDraw_of_eq [Finite V] {ψ : V → M} {c v : V} (h : ψ c = ψ v) :
    Pr[= v | fiberResampleDraw ψ c]
      = (@Fintype.card {d : V // ψ c = ψ d} (fiberFintype ψ c) : ℝ≥0∞)⁻¹ := by
  unfold fiberResampleDraw
  have hv : v = Subtype.val (⟨v, h⟩ : {d : V // ψ c = ψ d}) := rfl
  rw [hv]
  exact (probOutput_map_injective _ Subtype.val_injective _).trans
    (@probOutput_uniformSample _ (fiberSampleable ψ c) (fiberFintype ψ c) _)

/-- Output law of one fiber draw, off-fiber case: zero outside the fiber of `ψ c`. -/
lemma probOutput_fiberResampleDraw_of_ne [Finite V] {ψ : V → M} {c v : V} (h : ¬ψ c = ψ v) :
    Pr[= v | fiberResampleDraw ψ c] = 0 := by
  refine probOutput_eq_zero_of_not_mem_support ?_
  unfold fiberResampleDraw
  rw [support_map]
  rintro ⟨d, -, rfl⟩
  exact h d.prop

/-- **The table identity** (generic sampler form): resampling a uniform draw inside its own
`ψ`-fiber is invisible — `c ← 𝒰(V); c' ← 𝒰(ψ⁻¹(ψ(c)))` is distributed exactly as `𝒰(V)`.

This is the subtype-fiber counterpart of `Hyb12Step.map_bind_uniformFiber_eq_uniform`
(needing no surjectivity: only reached fibers are sampled). Instantiated at a function-table
type `V = (q : ι) → R q` and a cellwise `ψ`, the `ψ`-fiber is the product of the per-cell
fibers, so this is precisely "resampling each cell of a uniform table inside its own fiber
returns the uniform table" — the finite product of the per-cell identity. -/
theorem evalDist_fiberResampleSampler [SampleableType V] [Nonempty V] (ψ : V → M) :
    𝒟[fiberResampleSampler ψ] = 𝒟[$ᵗ V] := by
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidableEq M := Classical.decEq M
  refine evalDist_ext fun v => ?_
  unfold fiberResampleSampler
  rw [HasEvalSPMF.probOutput_bind_eq_sum_fintype, probOutput_uniformSample V v]
  -- fiber cards transport along the fiber relation
  have hcard : ∀ c : V, ψ c = ψ v →
      @Fintype.card {d : V // ψ c = ψ d} (fiberFintype ψ c)
        = @Fintype.card {d : V // ψ v = ψ d} (fiberFintype ψ v) := fun c hc =>
    @Fintype.card_congr _ _ (fiberFintype ψ c) (fiberFintype ψ v)
      (Equiv.subtypeEquivRight fun d => by rw [hc])
  -- pointwise summand: an indicator of the fiber of `ψ v`, with constant weight
  have hterm : ∀ c : V,
      Pr[= c | $ᵗ V] * Pr[= v | fiberResampleDraw ψ c]
        = if ψ c = ψ v
            then (Fintype.card V : ℝ≥0∞)⁻¹ *
              (@Fintype.card {d : V // ψ v = ψ d} (fiberFintype ψ v) : ℝ≥0∞)⁻¹
            else 0 := by
    intro c
    by_cases h : ψ c = ψ v
    · rw [if_pos h, probOutput_uniformSample V c, probOutput_fiberResampleDraw_of_eq h,
        hcard c h]
    · rw [if_neg h, probOutput_fiberResampleDraw_of_ne h, mul_zero]
  refine (Finset.sum_congr rfl fun c _ => hterm c).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- the `c`-fiber of `ψ v` has exactly the fiber cardinality
  have hfilter : (Finset.univ.filter fun c => ψ c = ψ v).card
      = @Fintype.card {d : V // ψ v = ψ d} (fiberFintype ψ v) := by
    have h1 : (Finset.univ.filter fun c => ψ c = ψ v)
        = (Finset.univ.filter fun d => ψ v = ψ d) :=
      Finset.filter_congr fun x _ => eq_comm
    rw [h1, @Fintype.card_congr _ _ (fiberFintype ψ v) _ (Equiv.refl _),
      Fintype.card_subtype]
  rw [hfilter]
  have hn0 : (@Fintype.card {d : V // ψ v = ψ d} (fiberFintype ψ v) : ℝ≥0∞) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]
    exact @Fintype.card_ne_zero _ (fiberFintype ψ v) (fiberNonempty ψ v)
  rw [mul_comm ((Fintype.card V : ℝ≥0∞))⁻¹, ← mul_assoc,
    ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top _), one_mul]

end FiberResample

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
nonemptiness of the `gSpec` table type). Not exported. -/
local instance : Inhabited U := ⟨0⟩

/-- Local `Inhabited` for encoded blocks. Not exported. -/
local instance {m : ℕ} : Inhabited (Vector U m) := ⟨Vector.replicate m default⟩

/-- The `gSpec` table type is nonempty (synthesis cannot see through `OracleSpec.Range`, a
plain `def`, so the `Pi` route is provided explicitly). Not exported. -/
local instance : Nonempty (OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
  ⟨fun q => (Vector.replicate (challengeSize (pSpec := pSpec) q.1) 0 :
    Vector U (challengeSize (pSpec := pSpec) q.1))⟩

/-! ## Game transport: `hybGameEager` only reads `𝒟[sample]` of a function-table carrier -/

section Transport

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- **Game transport for function-table challenge distributions**: `hybGameEager` samples
the challenge-oracle realization once (line 1 of CO25 Figure 4) and then reads it only via
the deterministic `tableQueryImpl`, so two function-table distributions whose samplers agree
in distribution induce the same game distribution. -/
theorem evalDist_hybGameEager_functionTable_congr [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M' : Type} [Inhabited M'] (δ : ℕ)
    {D₁ D₂ : ProbComp (OracleFamily challengeSpec)}
    (h : 𝒟[D₁] = 𝒟[D₂])
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M')
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
        (.functionTable D₁) gImpl lineFour oImpl V P]
      = 𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
          (.functionTable D₂) gImpl lineFour oImpl V P] := by
  unfold hybGameEager
  simp only [OracleDistribution.functionTable]
  rw [evalDist_bind, evalDist_bind, h]

/-- The cellwise decoder map on `gSpec` tables: `Ψ(c) := fun q => ψ_{q.1}(c q)`. Its fibers
are exactly the products of the per-cell `ψᵢ`-fibers, so `fiberResampleSampler gTableDecode`
is the per-cell fiber resampling of the whole uniform table. -/
noncomputable def gTableDecode (δ : ℕ) :
    OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      ((q : (gSpec (U := U) StmtIn pSpec δ).Domain) → pSpec.Challenge q.1) :=
  fun c q =>
    let responseVec : Vector U (challengeSize (pSpec := pSpec) q.1) := c q
    (Deserialize.deserialize responseVec : pSpec.Challenge q.1)

/-- `Hyb₁`'s game run against the **per-cell fiber-resampled** uniform `gSpec` table
(everything else — `gImplEncodedForward`, the `(φ⁻¹, ψ)` line-4 map — as in `Hyb1`). -/
noncomputable def Hyb1TableResampled [SampleableType U]
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
      (.functionTable (fiberResampleSampler
        (gTableDecode (U := U) (StmtIn := StmtIn) (pSpec := pSpec) δ)))
      (gImplEncodedForward (StmtIn := StmtIn) (δ := δ))
      (hyb1Line4TraceEager (δ := δ)) oImpl V P]

/-- **The DSFS table-level alignment, closed outright**: `Hyb₁` *is* the game against the
per-cell `ψ`-fiber-resampled uniform `gSpec` table (table identity + game transport). -/
theorem hyb1_eq_hyb1TableResampled [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Hyb1 T_H T_P δ oImpl V P = Hyb1TableResampled T_H T_P δ oImpl V P := by
  unfold Hyb1 Hyb1TableResampled OracleDistribution.uniform
  exact evalDist_hybGameEager_functionTable_congr (T_H := T_H) (T_P := T_P) δ
    (evalDist_fiberResampleSampler
      (gTableDecode (U := U) (StmtIn := StmtIn) (pSpec := pSpec) δ)).symm
    _ _ oImpl V P

/-- Distance form of the table-level alignment: `Δ(Hyb₁, Hyb1TableResampled) = 0`. -/
theorem tvDist_hyb1_hyb1TableResampled [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF.tvDist (Hyb1 T_H T_P δ oImpl V P) (Hyb1TableResampled T_H T_P δ oImpl V P) = 0 := by
  rw [hyb1_eq_hyb1TableResampled T_H T_P δ oImpl V P]
  exact SPMF.tvDist_self _

end Transport

/-! ## The memoized per-query resampler and the lazy/repeat split

`gImplEncodedResampledMemo` is `gImplEncodedResampled` with the `tr_i` memo of CO25 §5.4
D2SAlgo Item 3 attached at the `Hyb₁`-world layer: the eager table is still queried on
*every* derivation (preserving the raw log shape, hence the projected/line-4 logs), but the
`ψ⁻¹`-fiber redraw is performed once per distinct encoded key and replayed from the memo on
repeats. -/

section MemoSplit

/-- A memo entry for the fiber-resampled `gᵢ` realization: the encoded key
`(i, 𝕩, τ̂, α̂_{<i})` together with the stored fiber redraw `ρ̂ᵢ`. (The unsalted-world
counterpart of `ProverTransform.D2SAlgoMemoEntry`, keyed at the on-sponge salt.) -/
structure ResampleMemoEntry (StmtIn : Type) (U : Type) (δ : ℕ)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Vector U δ
  encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc
  response : Vector U (challengeSize (pSpec := pSpec) roundIdx)

/-- The fiber-redraw memo table (CO25 §5.4 D2SAlgo Item 3 `tr_i`, `Hyb₁`-world form). -/
abbrev ResampleMemo (StmtIn : Type) (U : Type) (δ : ℕ)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :=
  List (ResampleMemoEntry StmtIn U δ pSpec)

open Classical in
/-- Lookup in the fiber-redraw memo (mirrors `ProverTransform.lookupD2SAlgoMemo`). -/
noncomputable def lookupResampleMemo
    (memo : ResampleMemo StmtIn U δ pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    Option (Vector U (challengeSize (pSpec := pSpec) i)) :=
  memo.foldl (init := none) fun acc entry =>
    acc.orElse fun _ =>
      if hRound : entry.roundIdx = i then by
        subst hRound
        exact
          if entry.stmt = stmt ∧ entry.salt = salt ∧ entry.encodedMessages = encodedMessages
            then some entry.response
            else none
      else none

/-- On the empty memo every lookup misses. -/
lemma lookupResampleMemo_nil
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    lookupResampleMemo ([] : ResampleMemo StmtIn U δ pSpec)
      i stmt salt encodedMessages = none := rfl

/-- The **memoized** fiber-resampled `Hyb₁` `gᵢ`-realization: query the encoded oracle `gᵢ`
on every derivation (the raw log keeps the `Hyb₁`/`Hyb12Mid` shape, with the *table* value
as the logged response), then answer with the memoized `ψᵢ⁻¹`-fiber redraw of the decoded
table value — drawn fresh on the first derivation of each encoded key, replayed from the
memo on repeats (CO25 §5.4 D2SAlgo Item 3 determinism). -/
noncomputable def gImplEncodedResampledMemo :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) (ResampleMemo StmtIn U δ pSpec) :=
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
    let memo ← get
    match lookupResampleMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
        memo q.1 q.2.1 q.2.2.1 q.2.2.2 with
    | some r => pure r
    | none => do
        let r ←
          StateT.lift <|
            OptionT.lift <|
              uniformDeserializePreimage (pSpec := pSpec) (U := U)
                (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
                (Deserialize.deserialize v : pSpec.Challenge q.1)
        modify (fun m => m ++
          [{ roundIdx := q.1, stmt := q.2.1, salt := q.2.2.1,
             encodedMessages := q.2.2.2, response := r }])
        pure r

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The memoized pivot hybrid: `Hyb12Mid` with the per-query fiber resampler replaced by its
`tr_i`-memoized version (uniform `gSpec` table, `Hyb₁` line-4 map). -/
noncomputable def Hyb12MidMemo [SampleableType U]
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
      (gImplEncodedResampledMemo (StmtIn := StmtIn) (δ := δ))
      (hyb1Line4TraceEager (δ := δ)) oImpl V P]

/-- Finer residual A — **lazy/eager fiber resampling** (`Δ(Hyb₁, Hyb12MidMemo) = 0`):
lazily redrawing each *distinct* encoded key inside its decoder fiber at first read (memo
replay on repeats) matches the eagerly per-cell fiber-resampled table — which by the proven
table identity (`hyb1_eq_hyb1TableResampled`) is `Hyb₁` itself. Open content: the
lazy-vs-eager table induction (`RandomOracleEagerTableDep`-style, with the memo overlay as
the cache) plus the `ψ`-image log decoupling (the raw log records the table value while the
simulator consumes the redraw; only `ψ(·)` of responses survives the line-4 map, and `ψ` is
constant on fibers). No repeated-key issue remains in this leg. -/
def Hyb12LazyEagerResampleResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb1 T_H T_P δ oImpl V P) (Hyb12MidMemo T_H T_P δ oImpl V P) = 0

/-- Finer residual B — **repeat-derivation memo transparency**
(`Δ(Hyb12MidMemo, Hyb12Mid) = 0`): replaying the stored fiber redraw on a repeated encoded
key is invisible against redrawing it fresh. The two games are identical except on
executions where the *same* encoded key is derived twice; the log channel and the
verifier-side re-derivation are fiber-invariant (see module docstring), so the only
divergence channel is a prover-side repeated key reached via two distinct table-missing
sponge states (capacity collisions / `p⁻¹`-grafted chains). **DOUBTFUL as stated** for any
round with a non-injective decoder: such paths have positive (birthday-sized) probability
and expose raw fiber mates through the synthesized squeeze states; CO25 inserts the `tr_i`
memo (§5.4 Item 3) precisely to delete this channel and charges collision paths to birthday
terms (§5.6 / Eq. 55) rather than claiming exact `0`. TRUE when every `codec.decode i` is
injective (singleton fibers); an honest general repair weakens `= 0` to a birthday bound. -/
def Hyb12RepeatDerivationResidual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb12MidMemo T_H T_P δ oImpl V P) (Hyb12Mid T_H T_P δ oImpl V P) = 0

/-- **Lazy split assembly (proven)**: the lazy/eager leg and the repeat-derivation leg
assemble into the full fiber-resample alignment `Hyb12ResampleAlignResidual` by the TV
triangle inequality through the memoized pivot `Hyb12MidMemo`. -/
theorem hyb12ResampleAlign_of_lazySplit [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hA : Hyb12LazyEagerResampleResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl)
    (hB : Hyb12RepeatDerivationResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P δ oImpl) :
    Hyb12ResampleAlignResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P
  have h1 := hA V P
  have h2 := hB V P
  have htri := SPMF.tvDist_triangle (Hyb1 T_H T_P δ oImpl V P)
    (Hyb12MidMemo T_H T_P δ oImpl V P) (Hyb12Mid T_H T_P δ oImpl V P)
  have hnn := SPMF.tvDist_nonneg (Hyb1 T_H T_P δ oImpl V P)
    (Hyb12Mid T_H T_P δ oImpl V P)
  linarith

end MemoSplit

end DuplexSpongeFS.Hyb12Align

#print axioms DuplexSpongeFS.Hyb12Align.probOutput_fiberResampleDraw_of_eq
#print axioms DuplexSpongeFS.Hyb12Align.probOutput_fiberResampleDraw_of_ne
#print axioms DuplexSpongeFS.Hyb12Align.evalDist_fiberResampleSampler
#print axioms DuplexSpongeFS.Hyb12Align.evalDist_hybGameEager_functionTable_congr
#print axioms DuplexSpongeFS.Hyb12Align.hyb1_eq_hyb1TableResampled
#print axioms DuplexSpongeFS.Hyb12Align.tvDist_hyb1_hyb1TableResampled
#print axioms DuplexSpongeFS.Hyb12Align.lookupResampleMemo_nil
#print axioms DuplexSpongeFS.Hyb12Align.hyb12ResampleAlign_of_lazySplit

end
