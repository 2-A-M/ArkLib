/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Delta0
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets
import ArkLib.OracleReduction.FiatShamir.HVZKKernelInfra

/-!
# CO25 Claim 5.23, step A at `δ = 0` — the decoded-query leg and its reachability invariant

`Hyb23Step.Hyb23DecodedQueryResidual` (step A of the Claim 5.23 salted split) demands
`Δ(Hyb₂, Hyb3SaltedFresh) = 0`. Round 2 proved the per-query coupling
(`gImplDecodedChallenge_run_eq_bridgeSalted_run`) **at parse-successful keys** and left two
gaps: (1) `Hyb₂` *can* read `eSpec` keys whose encoded prefix fails the `φ⁻¹` parse — keys on
which the salted Eq. 16 bridge aborts — so the coupling needs the **reachability invariant**:
along the `Hyb₂` game, every `eSpec` key actually queried passes the parse (the simulator's
Item 4(e) codec-image check guards every `gᵢ` emission); (2) the uniform `eSpec` table sample
must be re-indexed along the key map `(τ̂, α̂) ↦ (bin τ̂, φ⁻¹ α̂)`, which needs
`φ⁻¹`-injectivity on its success domain and, at `δ > 0`, runs into the same salt-grinding
obstruction as step C. This module discharges both gaps at `δ = 0`.

## Proven here (no `sorry`, axiom-clean)

The parse bridge (the Item 4(e) ⇒ `φ⁻¹`-success content):

- `hybEncodedMessagesBefore?_isSome_of_image` — if every encoded block of the prefix lies in
  the serialization image, the §5.8 `φ⁻¹` parser succeeds (per-round walk induction).
- `d2sInCodecImage_parse_isSome` — the simulator's Item 4(e) check
  (`d2sInCodecImagePredicate`) implies parse success at the emitted `gᵢ` key.
- `hybEncodedMessagesBefore?_inj` — **`φ⁻¹`-injectivity on its success domain**: two encoded
  prefixes parsing to the *same* message prefix are equal (block-by-block walk induction;
  uses `Serialize` injectivity through `List.find?`).

The reachability invariant (CO25 §5.4 Item 4(e), formalized as a zero query budget):

- `d2sQueryStep_badKey_budget` — the §5.4 dispatcher makes **zero** challenge-summand queries
  at parse-failed keys (branch-tree analysis; the unique `gᵢ` emission site is guarded by
  the Item 4(e) image check, which implies parse success).
- `d2fRaw_decoded_badKey_budget` / `d2fRaw_decoded_logged_badKey_budget` — the invariant
  lifted through the full `Hyb₂` pipeline (`d2fRaw` with the `Hyb₂` realization
  `gImplDecodedChallenge`, plus the logging layer): **no parse-failed `eSpec` key is ever
  queried**, for *any* driving computation (prover or verifier) and any initial memo.

Generic bricks (candidates for upstreaming):

- `isQueryBoundP_zero_of_imp` — zero budgets are antitone in the predicate.
- `simulateQ_congr_of_isQueryBoundP_zero` — **the invariant-consumption keystone**: two
  implementations agreeing outside a zero-budget predicate induce *equal* simulations.

Game-level consequences:

- `hybGameEagerBody_decoded_congr` — the `Hyb₂` game body at a fixed table depends on the
  table **only through its parse-successful cells** (keystone + invariant; any `δ`).
- `reindexTable` + `gImplDecodedChallenge_run_eq_bridgeSalted_run_reindex` — the per-query
  coupling instantiated at the pulled-back table, where the agreement hypothesis holds
  definitionally.
- `probOutput_uniformE_bind_eq_uniformSalted_reindex` (`δ = 0`) — **uniform re-indexing**:
  binding any good-cell-local continuation on a uniform `eSpec` table equals binding it on
  the pullback of a uniform salted table (two fiber-swap arguments through the good-cell
  space; injectivity of the key map from `hybEncodedMessagesBefore?_inj` plus the `δ = 0`
  salt subsingleton).
- `hyb23DecodedQuery_delta0_of_crossLift` — **the reduction theorem**: the named fixed-table
  cross-spec residual implies the full `Hyb23DecodedQueryResidual` at `δ = 0`. All
  probabilistic content (the uniform re-indexing) and the reachability invariant are
  discharged; what remains is a deterministic-coupling `simulateQ` bisimulation, exactly
  parallel to step C's `Hyb23SaltErasureLiftDelta0Residual`.

## Open (named obligation, NOT proven)

- `Hyb23DecodedCrossLiftDelta0Residual` — at every *fixed* salted table `c`, the `Hyb₂` body
  at the pulled-back table `reindexTable c` and the `Hyb3SaltedFresh` body at `c` have the
  same output distribution. Given the bricks here this coupling has **no remaining
  probabilistic content**: both sides are driven by the same auxiliary randomness, the
  per-query responses are equal (`gImplDecodedChallenge_run_eq_bridgeSalted_run_reindex`,
  applicable everywhere reachable by the invariant), and the line-4 maps send the paired raw
  logs to the same processed log (`hyb2Line4TraceEager` parse-projects the `eSpec` key;
  `eraseSaltLog` erases the salt of the replayed key). What remains is the
  `d2fRaw`/`loggingOracle` bisimulation that threads this per-query data through the game —
  the same plumbing class as step C's fixed-table lift.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb23Decoded

open Backtrack Lookahead DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations
  KeyLemmaHybrids VerifierReplay Hyb23Step Hyb23Delta0
open scoped ENNReal

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it
-- (repo precedent: the sibling lane modules `Hyb23Step`, `SimulatorBudgets`).
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open private decodeMessagePhiInv? lookupEncodedMessageAlphaHat? decodeMessagesPrefixStepPhiInv
  decodeMessagesPrefixPhiInv? from
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform

open private messageInSerializeImage d2sInCodecImagePredicate d2sHandleHashQuery
  d2sHandleInversePermQuery d2sHandleBacktrackNoResult d2sHandleBacktrackSome
  d2sHandleForwardPermQuery from
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform

open private isQueryBoundP_run2_bind isQueryBoundP_run2_lift_bind isQueryBoundP_run2_lift_failure
  d2sSampleState_left_budget d2sRateBlocksFromChallenge_left_budget
  d2sSynthesizeStateFromRateBlocks_left_budget d2sHandleHashQuery_left_budget
  d2sHandleInversePermQuery_left_budget d2sHandleBacktrackNoResult_left_budget
  d2fAuxImpl d2fOuterImpl_run_inl d2fOuterImpl_run_inr isQueryBoundP_simulateQ_inclusion from
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-! ## The §5.8 `φ⁻¹` parser, exposed as a per-round walk -/

section ParseWalk

/-- The per-round walk of the §5.8 `φ⁻¹` parser (`decodeMessagesPrefixPhiInv?`'s internal
`build`), exposed as a standalone function so the bridge/injectivity inductions can talk
about intermediate rounds. -/
private noncomputable def parseWalk
    (encodedList :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))) :
    (k : Fin (n + 1)) → Option (pSpec.MessagesUpTo k) :=
  Fin.induction
    (some default)
    (fun j ih =>
      match ih with
      | none => none
      | some messages =>
          decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) encodedList j messages)

/-- The public parser is the walk evaluated at the cutoff round. -/
private lemma hybEncodedMessagesBefore?_eq_parseWalk (i : pSpec.ChallengeIdx)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em
      = parseWalk (pSpec := pSpec) (U := U)
          (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) i.1.castSucc := rfl

private lemma parseWalk_zero
    (L : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))) :
    parseWalk (pSpec := pSpec) (U := U) L 0 = some default := by
  unfold parseWalk
  exact Fin.induction_zero _ _

private lemma parseWalk_succ
    (L : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)))
    (j : Fin n) :
    parseWalk (pSpec := pSpec) (U := U) L j.succ
      = match parseWalk (pSpec := pSpec) (U := U) L j.castSucc with
        | none => none
        | some messages =>
            decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) L j messages := by
  unfold parseWalk
  exact Fin.induction_succ _ _ _

/-- Success elimination for one parser step on a prover-message round: a successful step
exposes the block lookup, the block decode, and the `concat` output shape. -/
private lemma decodeStep_P_elim
    {L : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))}
    {j : Fin n} (hd : pSpec.dir j = .P_to_V) {m₀ : pSpec.MessagesUpTo j.castSucc}
    {m : pSpec.MessagesUpTo j.succ}
    (hstep : decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) L j m₀ = some m) :
    ∃ (enc : Vector U (messageSize ⟨j, hd⟩)) (msg : pSpec.Message ⟨j, hd⟩),
      lookupEncodedMessageAlphaHat? (pSpec := pSpec) L ⟨j, hd⟩ = some enc ∧
      decodeMessagePhiInv? (pSpec := pSpec) (U := U) ⟨j, hd⟩ enc = some msg ∧
      m = ProtocolSpec.MessagesUpTo.concat (pSpec := pSpec) m₀ hd msg := by
  unfold decodeMessagesPrefixStepPhiInv at hstep
  split at hstep
  · dsimp only at hstep
    split at hstep
    · simp at hstep
    · next enc hl =>
        split at hstep
        · simp at hstep
        · next msg hdec =>
            exact ⟨enc, msg, hl, hdec, (Option.some.inj hstep).symm⟩
  · next heq => exact absurd (hd.symm.trans heq) (by simp)

/-- Success introduction for one parser step on a prover-message round. -/
private lemma decodeStep_P_intro
    (L : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)))
    (j : Fin n) (hd : pSpec.dir j = .P_to_V) (m₀ : pSpec.MessagesUpTo j.castSucc)
    {enc : Vector U (messageSize ⟨j, hd⟩)} {msg : pSpec.Message ⟨j, hd⟩}
    (hl : lookupEncodedMessageAlphaHat? (pSpec := pSpec) L ⟨j, hd⟩ = some enc)
    (hdec : decodeMessagePhiInv? (pSpec := pSpec) (U := U) ⟨j, hd⟩ enc = some msg) :
    decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) L j m₀
      = some (ProtocolSpec.MessagesUpTo.concat (pSpec := pSpec) m₀ hd msg) := by
  unfold decodeMessagesPrefixStepPhiInv
  split
  · next heq =>
      simp only [show lookupEncodedMessageAlphaHat? (pSpec := pSpec) L ⟨j, heq⟩ = some enc
          from hl,
        show decodeMessagePhiInv? (pSpec := pSpec) (U := U) ⟨j, heq⟩ enc = some msg
          from hdec]
  · next heq => exact absurd (hd.symm.trans heq) (by simp)

/-- Shape of one parser step on a verifier-challenge round. -/
private lemma decodeStep_eq_of_dir_V
    (L : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)))
    (j : Fin n) (hd : pSpec.dir j = .V_to_P) (messages : pSpec.MessagesUpTo j.castSucc) :
    decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) L j messages
      = some (ProtocolSpec.MessagesUpTo.extend (pSpec := pSpec) messages hd) := by
  unfold decodeMessagesPrefixStepPhiInv
  split
  · next heq => exact absurd (hd.symm.trans heq) (by simp)
  · rfl

/-- A successful `φ⁻¹` block decode inverts the serialization (`List.find?` property). -/
private lemma decodeMessagePhiInv?_serialize {msgIdx : pSpec.MessageIdx}
    {enc : Vector U (messageSize msgIdx)} {msg : pSpec.Message msgIdx}
    (h : decodeMessagePhiInv? (pSpec := pSpec) (U := U) msgIdx enc = some msg) :
    Serialize.serialize msg = enc := by
  unfold decodeMessagePhiInv? at h
  have := List.find?_some h
  exact of_decide_eq_true this

/-- If the block lies in the serialization image, the `φ⁻¹` block decode succeeds. -/
private lemma decodeMessagePhiInv?_isSome {msgIdx : pSpec.MessageIdx}
    (enc : Vector U (messageSize msgIdx))
    (h : ∃ msg : pSpec.Message msgIdx, Serialize.serialize msg = enc) :
    ∃ msg, decodeMessagePhiInv? (pSpec := pSpec) (U := U) msgIdx enc = some msg := by
  obtain ⟨msg, hmsg⟩ := h
  unfold decodeMessagePhiInv?
  refine Option.isSome_iff_exists.mp ?_
  rw [List.find?_isSome]
  exact ⟨msg, Finset.mem_toList.mpr (Finset.mem_univ msg), by simp [hmsg]⟩

/-- Looking up a structured-prefix block from `toList` recovers the block itself
(`filterMap`/`findSome?` plumbing). -/
private lemma lookupEncodedMessageAlphaHat?_filterMap {k : Fin (n + 1)}
    (em : pSpec.EncodedMessagesBefore U k)
    (l : List pSpec.MessageIdx) (j : pSpec.MessageIdx) (hjl : j ∈ l) (hjk : j.1.1 < k.1) :
    lookupEncodedMessageAlphaHat? (pSpec := pSpec)
        (l.filterMap fun j' =>
          if h : j'.1.1 < k.1 then some ⟨j', em ⟨j', h⟩⟩ else none) j
      = some (em ⟨j, hjk⟩) := by
  induction l with
  | nil => cases hjl
  | cons a rest ih =>
      rw [List.filterMap_cons]
      by_cases haj : a = j
      · subst haj
        rw [dif_pos hjk]
        unfold lookupEncodedMessageAlphaHat?
        simp only [List.findSome?_cons]
        simp
      · have hjrest : j ∈ rest := (List.mem_cons.mp hjl).resolve_left (fun h => haj h.symm)
        by_cases hak : a.1.1 < k.1
        · rw [dif_pos hak]
          unfold lookupEncodedMessageAlphaHat? at ih ⊢
          simp only [List.findSome?_cons]
          rw [dif_neg haj]
          exact ih hjrest
        · rw [dif_neg hak]
          exact ih hjrest

/-- Looking up any in-range block from the CO25 Eq. 15 structured prefix returns exactly
that block. -/
private lemma lookupEncodedMessageAlphaHat?_toList {k : Fin (n + 1)}
    (em : pSpec.EncodedMessagesBefore U k) (j : pSpec.MessageIdx) (hjk : j.1.1 < k.1) :
    lookupEncodedMessageAlphaHat? (pSpec := pSpec)
        (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) j
      = some (em ⟨j, hjk⟩) := by
  unfold EncodedMessagesBefore.toList
  exact lookupEncodedMessageAlphaHat?_filterMap em _ j
    (Finset.mem_toList.mpr (Finset.mem_univ j)) hjk

end ParseWalk

/-! ## The parse bridge: Item 4(e) codec-image check ⇒ `φ⁻¹` success -/

section ParseBridge

/-- If every encoded block of the prefix is in the serialization image, the per-round walk
succeeds at every round up to the cutoff. -/
private lemma parseWalk_isSome {iB : Fin (n + 1)}
    (em : pSpec.EncodedMessagesBefore U iB)
    (himg : ∀ (j : pSpec.MessageIdx) (hlt : j.1.1 < iB.1),
      ∃ msg : pSpec.Message j, Serialize.serialize msg = em ⟨j, hlt⟩) :
    ∀ k : Fin (n + 1), k.1 ≤ iB.1 →
      (parseWalk (pSpec := pSpec) (U := U)
        (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) k).isSome := by
  intro k
  induction k using Fin.induction with
  | zero =>
      intro _
      rw [parseWalk_zero]
      rfl
  | succ j ih =>
      intro hk
      have hs : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
      have hc : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
      have hk' : (j.castSucc).1 ≤ iB.1 := by omega
      obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp (ih hk')
      rw [parseWalk_succ]
      simp only [hm₀]
      cases hdir : pSpec.dir j with
      | V_to_P =>
          rw [decodeStep_eq_of_dir_V _ j hdir m₀]
          rfl
      | P_to_V =>
          have hjlt : (⟨j, hdir⟩ : pSpec.MessageIdx).1.1 < iB.1 := by
            change (j : ℕ) < iB.1
            omega
          obtain ⟨msg, hmsg⟩ := decodeMessagePhiInv?_isSome _ (himg ⟨j, hdir⟩ hjlt)
          rw [decodeStep_P_intro _ j hdir m₀
            (lookupEncodedMessageAlphaHat?_toList em ⟨j, hdir⟩ hjlt) hmsg]
          rfl

/-- **The image-to-parse bridge**: if every encoded block of an Eq. 15 prefix lies in the
serialization image, the §5.8 `φ⁻¹` parser succeeds on it. -/
theorem hybEncodedMessagesBefore?_isSome_of_image (i : pSpec.ChallengeIdx)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (himg : ∀ (j : pSpec.MessageIdx) (hlt : j.1.1 < i.1.1),
      ∃ msg : pSpec.Message j, Serialize.serialize msg = em ⟨j, hlt⟩) :
    (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em).isSome := by
  rw [hybEncodedMessagesBefore?_eq_parseWalk]
  exact parseWalk_isSome em himg i.1.castSucc le_rfl

/-- **CO25 §5.4 Item 4(e) ⇒ `φ⁻¹` success**: the simulator's codec-image check on a
backtrack output implies the §5.8 parser succeeds at the emitted `gᵢ` key. This is the
content of the reachability invariant at a single emission site. -/
theorem d2sInCodecImage_parse_isSome {δ : ℕ}
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (h : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true) :
    (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U)
      out.roundIdx out.encodedMessages).isSome := by
  refine hybEncodedMessagesBefore?_isSome_of_image _ _ (fun j hlt => ?_)
  unfold d2sInCodecImagePredicate backtrackOutputMessagesInImage at h
  rw [List.all_eq_true] at h
  have hjmem : j ∈ messageIdxListBefore (pSpec := pSpec) out.roundIdx := by
    unfold messageIdxListBefore
    rw [Finset.mem_toList, Finset.mem_filter]
    exact ⟨Finset.mem_univ j, hlt⟩
  have hj := h ⟨j, hjmem⟩ (List.mem_attach _ _)
  simp only at hj
  unfold messageInSerializeImage at hj
  exact of_decide_eq_true hj

end ParseBridge

/-! ## `φ⁻¹`-injectivity on its success domain -/

section PhiInvInjective

/-- The round-`k` `concat` evaluated at the just-inserted round recovers the new message
(companion of `HVZKLazyVerifier`'s `concat_castSucc`; `Fin.dconcat_last` projection). -/
private lemma concat_apply_last {k : Fin n} (m : pSpec.MessagesUpTo k.castSucc)
    (h : pSpec.dir k = .P_to_V) (msg : pSpec.Message ⟨k, h⟩)
    (hd : (pSpec.take k.succ (by omega)).dir (Fin.last k.1) = .P_to_V) :
    (m.concat h msg) ⟨Fin.last k.1, hd⟩ = msg := by
  unfold ProtocolSpec.MessagesUpTo.concat ProtocolSpec.MessagesUpTo.concat'
  exact congrFun (Fin.dconcat_last
    (motive := fun x : Fin (k.1 + 1) =>
      pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
        pSpec.«Type» (Fin.castLE (by omega) x))
    (fun i hi => m ⟨i, hi⟩) (fun _ => msg)) hd

/-- Walk determinism: if the two walks on prefixes `em`, `em'` reach the **same** message
prefix at round `k`, then `em` and `em'` agree on every block strictly before `k`. -/
private lemma parseWalk_blocks_eq {iB : Fin (n + 1)}
    (em em' : pSpec.EncodedMessagesBefore U iB) :
    ∀ (k : Fin (n + 1)), k.1 ≤ iB.1 →
    ∀ (m : pSpec.MessagesUpTo k),
      parseWalk (pSpec := pSpec) (U := U)
        (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) k = some m →
      parseWalk (pSpec := pSpec) (U := U)
        (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em') k = some m →
      ∀ (j : pSpec.MessageIdx), j.1.1 < k.1 → ∀ (hjB : j.1.1 < iB.1),
        em ⟨j, hjB⟩ = em' ⟨j, hjB⟩ := by
  intro k
  induction k using Fin.induction with
  | zero =>
      intro _ m _ _ j hjk _
      exact absurd hjk (Nat.not_lt_zero _)
  | succ j₀ ih =>
      intro hk m hw hw' j hjk hjB
      have hs : ((j₀.succ : Fin (n + 1)) : ℕ) = (j₀ : ℕ) + 1 := rfl
      have hc : ((j₀.castSucc : Fin (n + 1)) : ℕ) = (j₀ : ℕ) := rfl
      have hk' : (j₀.castSucc).1 ≤ iB.1 := by omega
      have hjk2 : j.1.1 < (j₀ : ℕ) + 1 := hs ▸ hjk
      rw [parseWalk_succ] at hw hw'
      rcases hO : parseWalk (pSpec := pSpec) (U := U)
          (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) j₀.castSucc with _ | m₀
      · rw [hO] at hw
        simp at hw
      rcases hO' : parseWalk (pSpec := pSpec) (U := U)
          (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em') j₀.castSucc with _ | m₀'
      · rw [hO'] at hw'
        simp at hw'
      simp only [hO] at hw
      simp only [hO'] at hw'
      cases hdir : pSpec.dir j₀ with
      | V_to_P =>
          rw [decodeStep_eq_of_dir_V _ j₀ hdir m₀] at hw
          rw [decodeStep_eq_of_dir_V _ j₀ hdir m₀'] at hw'
          have hext : ProtocolSpec.MessagesUpTo.extend (pSpec := pSpec) m₀ hdir
              = ProtocolSpec.MessagesUpTo.extend (pSpec := pSpec) m₀' hdir :=
            (Option.some.inj hw).trans (Option.some.inj hw').symm
          have hm₀ : m₀ = m₀' := by
            have h1 := ProtocolSpec.MessagesUpTo.take_extend_self m₀ hdir
            have h2 := ProtocolSpec.MessagesUpTo.take_extend_self m₀' hdir
            rw [← h1, ← h2, hext]
          have hjk' : j.1.1 < (j₀.castSucc).1 := by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hjk2 with hlt | heq
            · omega
            · exfalso
              have hj1 : j.1 = j₀ := Fin.ext heq
              have hdj := j.2
              rw [hj1, hdir] at hdj
              exact Direction.noConfusion hdj
          exact ih hk' m₀ hO (hm₀ ▸ hO') j hjk' hjB
      | P_to_V =>
          obtain ⟨encE, msgE, hlE, hdecE, hmE⟩ := decodeStep_P_elim hdir hw
          obtain ⟨encE', msgE', hlE', hdecE', hmE'⟩ := decodeStep_P_elim hdir hw'
          have hjlt₀ : (⟨j₀, hdir⟩ : pSpec.MessageIdx).1.1 < iB.1 := by
            change (j₀ : ℕ) < iB.1
            omega
          have hencE : encE = em ⟨⟨j₀, hdir⟩, hjlt₀⟩ :=
            Option.some.inj
              ((lookupEncodedMessageAlphaHat?_toList em ⟨j₀, hdir⟩ hjlt₀).symm.trans hlE).symm
          have hencE' : encE' = em' ⟨⟨j₀, hdir⟩, hjlt₀⟩ :=
            Option.some.inj
              ((lookupEncodedMessageAlphaHat?_toList em' ⟨j₀, hdir⟩ hjlt₀).symm.trans
                hlE').symm
          have hcc : ProtocolSpec.MessagesUpTo.concat (pSpec := pSpec) m₀ hdir msgE
              = ProtocolSpec.MessagesUpTo.concat (pSpec := pSpec) m₀' hdir msgE' :=
            hmE.symm.trans hmE'
          have hm₀ : m₀ = m₀' := by
            have h1 := ProtocolSpec.MessagesUpTo.take_concat_self m₀ hdir msgE
            have h2 := ProtocolSpec.MessagesUpTo.take_concat_self m₀' hdir msgE'
            rw [← h1, ← h2, hcc]
          have hdX : (pSpec.take j₀.succ (by omega)).dir (Fin.last j₀.1) = .P_to_V := hdir
          have hmsgE : msgE = msgE' := by
            have h1 := concat_apply_last m₀ hdir msgE hdX
            have h2 := concat_apply_last m₀' hdir msgE' hdX
            rw [← h1, ← h2, hcc]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjk2 with hlt | heq
          · have hjk' : j.1.1 < (j₀.castSucc).1 := by omega
            exact ih hk' m₀ hO (hm₀ ▸ hO') j hjk' hjB
          · have hj1 : j = ⟨j₀, hdir⟩ := Subtype.ext (Fin.ext heq)
            subst hj1
            have hE := decodeMessagePhiInv?_serialize hdecE
            have hE' := decodeMessagePhiInv?_serialize hdecE'
            have hblocks : em ⟨⟨j₀, hdir⟩, hjlt₀⟩ = em' ⟨⟨j₀, hdir⟩, hjlt₀⟩ := by
              rw [← hencE, ← hencE', ← hE, ← hE', hmsgE]
            exact hblocks

/-- **`φ⁻¹`-injectivity on its success domain** (the missing brick flagged by round 2,
provable since round 3 exposed the public wrapper): two encoded prefixes that parse to the
*same* message prefix are equal. -/
theorem hybEncodedMessagesBefore?_inj (i : pSpec.ChallengeIdx)
    (em em' : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (msgs : pSpec.MessagesUpTo i.1.castSucc)
    (h : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em = some msgs)
    (h' : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em' = some msgs) :
    em = em' := by
  rw [hybEncodedMessagesBefore?_eq_parseWalk] at h h'
  funext jb
  obtain ⟨j, hj⟩ := jb
  exact parseWalk_blocks_eq em em' i.1.castSucc le_rfl msgs h h' j hj hj

end PhiInvInjective

/-! ## Generic bricks: zero budgets are predicate-antitone; zero-budget `simulateQ` congruence -/

section GenericBricks

universe u

variable {ι₁ : Type u} {spec : OracleSpec ι₁} {α : Type u}

/-- Zero query budgets are antitone in the predicate: if `oa` makes no `p`-queries and
`q ⊆ p`, then `oa` makes no `q`-queries. -/
theorem isQueryBoundP_zero_of_imp {p q : ι₁ → Prop} [DecidablePred p] [DecidablePred q]
    {oa : OracleComp spec α}
    (himp : ∀ t, q t → p t) (h : IsQueryBoundP oa p 0) :
    IsQueryBoundP oa q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h ⊢
      have hnp : ¬ p t := h.1.resolve_right (lt_irrefl 0)
      have hnq : ¬ q t := fun hq => hnp (himp t hq)
      refine ⟨Or.inl hnq, fun u => ?_⟩
      have hmx := h.2 u
      simp only [if_neg hnp] at hmx
      simp only [if_neg hnq]
      exact ih u hmx

/-- **The invariant-consumption keystone**: if `oa` makes no `p`-queries, then any two
implementations agreeing outside `p` induce *equal* simulations of `oa`. This is how a
proven reachability invariant (`IsQueryBoundP … 0`) turns into a game equality. -/
theorem simulateQ_congr_of_isQueryBoundP_zero {m : Type u → Type u}
    [Monad m] [LawfulMonad m] {p : ι₁ → Prop} [DecidablePred p]
    {impl₁ impl₂ : QueryImpl spec m} {oa : OracleComp spec α}
    (h : IsQueryBoundP oa p 0) (himpl : ∀ t, ¬ p t → impl₁ t = impl₂ t) :
    simulateQ impl₁ oa = simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      have hnp : ¬ p t := h.1.resolve_right (lt_irrefl 0)
      rw [simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query]
      rw [himpl t hnp]
      refine bind_congr fun u => ?_
      have hmx := h.2 u
      simp only [if_neg hnp] at hmx
      exact ih u hmx

end GenericBricks

/-! ## The bad-key classifiers (parse-failed challenge keys) -/

section BadKeyClassifiers

variable {δ : ℕ}

/-- A challenge-summand key (of `gSpec`/`eSpec`, which share the key type) is **bad** iff
its encoded message prefix fails the §5.8 `φ⁻¹` parse. The reachability invariant says bad
keys are never queried. -/
noncomputable def isBadChalKey :
    (((i : pSpec.ChallengeIdx) ×
        (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc))
      ⊕ (Unit ⊕ ℕ)) → Bool
  | .inl k => (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2).isNone
  | .inr _ => false

/-- Bad-key classifier on the outer pipeline spec `oSpec + (challengeSpec + aux)`. -/
noncomputable def isBadOuterKey :
    (ι ⊕ (((i : pSpec.ChallengeIdx) ×
        (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc))
      ⊕ (Unit ⊕ ℕ))) → Bool
  | .inr (.inl k) => (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2).isNone
  | _ => false

private lemma isBadChalKey_imp_isLeft
    (t : ((i : pSpec.ChallengeIdx) ×
        (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc))
      ⊕ (Unit ⊕ ℕ))
    (h : isBadChalKey (StmtIn := StmtIn) (δ := δ) t = true) : t.isLeft = true := by
  match t with
  | .inl k => rfl
  | .inr aux => simp [isBadChalKey] at h

/-- Convert a zero left-summand budget into a zero bad-key budget. -/
private lemma badKey_budget_of_left_budget {α : Type}
    {oa : OracleComp
      (D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α}
    (h : IsQueryBoundP oa (fun j => j.isLeft = true) 0) :
    IsQueryBoundP oa
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      0 :=
  isQueryBoundP_zero_of_imp (isBadChalKey_imp_isLeft (δ := δ)) h

end BadKeyClassifiers

/-! ## The reachability invariant, dispatcher level (CO25 §5.4 Items 2–4) -/

section DispatcherInvariant

variable {δ : ℕ} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The Item 4(e)i `gᵢ` query is emitted only after the Item 4(e) image check, hence at a
parse-successful (non-bad) key. -/
private lemma d2sQueryG_badKey_budget
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (himg : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out
      = true) :
    IsQueryBoundP
      (d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        out.roundIdx out.stmt out.salt out.encodedMessages)
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      0 := by
  unfold d2sQueryG
  simp only [HasQuery.instOfMonadLift_query]
  refine (isQueryBoundP_query_iff _ _ _).mpr (fun hbad => ?_)
  exfalso
  have hsome := d2sInCodecImage_parse_isSome (δ := δ) out himg
  simp only [isBadChalKey] at hbad
  rw [Option.isNone_iff_eq_none] at hbad
  rw [hbad] at hsome
  exact Bool.noConfusion hsome

/-- CO25 §5.4 Items 4(d)/(e) — the backtrack-success branch makes **no** bad-key query:
the unique `gᵢ` emission is guarded by the Item 4(e) image check. -/
private lemma d2sHandleBacktrackSome_badKey_budget (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleBacktrackSome (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut).run st).run)
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      0 := by
  unfold d2sHandleBacktrackSome
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · next himg =>
      refine isQueryBoundP_run2_lift_bind (n := 0) (m := 0)
        (d2sQueryG_badKey_budget backtrackOut himg) (fun sampledRhoHat => ?_)
      split
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          OptionT.run_pure]
        exact isQueryBoundP_pure _ _ _
      · refine isQueryBoundP_run2_lift_bind (n := 0) (m := 0)
          (badKey_budget_of_left_budget
            (d2sRateBlocksFromChallenge_left_budget _)) (fun rateBlocks => ?_)
        refine isQueryBoundP_run2_bind (n := 0) (m := 0)
          (badKey_budget_of_left_budget
            (d2sSynthesizeStateFromRateBlocks_left_budget _ _)) (fun sc s' => ?_)
        obtain ⟨s_out, cache'⟩ := sc
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          OptionT.run_pure]
        exact isQueryBoundP_pure _ _ _
  · split
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
    · refine isQueryBoundP_run2_lift_bind (n := 0) (m := 0)
        (badKey_budget_of_left_budget
          d2sSampleState_left_budget) (fun sampled => ?_)
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _

/-- CO25 §5.4 Item 4 — the forward-permutation handler makes no bad-key query. -/
private lemma d2sHandleForwardPermQuery_badKey_budget (stateIn : CanonicalSpongeState U)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st).run)
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      0 := by
  unfold d2sHandleForwardPermQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact isQueryBoundP_run2_lift_failure _ _
  · exact badKey_budget_of_left_budget
      (d2sHandleBacktrackNoResult_left_budget _ _)
  · exact d2sHandleBacktrackSome_badKey_budget _ _ _

/-- **The reachability invariant, dispatcher level**: the §5.4 `D2SQuery` dispatcher makes
**zero** challenge-summand queries at parse-failed keys — every `gᵢ` emission is guarded by
the Item 4(e) codec-image check, which implies `φ⁻¹` success. -/
theorem d2sQueryStep_badKey_budget
    (qq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) qq).run st).run)
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      0 := by
  match qq with
  | Sum.inl stmt =>
      exact badKey_budget_of_left_budget
        (d2sHandleHashQuery_left_budget stmt st)
  | Sum.inr (Sum.inl stateIn) =>
      exact d2sHandleForwardPermQuery_badKey_budget stateIn st
  | Sum.inr (Sum.inr stateOut) =>
      exact badKey_budget_of_left_budget
        (d2sHandleInversePermQuery_left_budget stateOut st)

end DispatcherInvariant

/-! ## The reachability invariant, pipeline level (the full `Hyb₂` realization) -/

section PipelineInvariant

variable {δ : ℕ} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The `ψ⁻¹` preimage sampler of the `Hyb₂` realization makes no challenge-summand query at
all (its only query is the `unifSpec` index draw). -/
private lemma uniformDeserializePreimage_badKey_budget {i : pSpec.ChallengeIdx}
    (ch : pSpec.Challenge i) :
    IsQueryBoundP
      (uniformDeserializePreimage (pSpec := pSpec) (U := U)
        (challengeSpec := eSpec (U := U) StmtIn pSpec δ) ch)
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      0 := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [HasQuery.instOfMonadLift_query]
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [isBadChalKey]), fun u => isQueryBoundP_pure _ _ _⟩

/-- Per-`gSpec`-query budget of the `Hyb₂` realization `gImplDecodedChallenge`: one `eSpec`
query at exactly the source key (bad iff the source key is bad), plus table-oblivious
sampling. -/
private lemma gImplDecodedChallenge_step_badKey (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (s : PUnit) :
    IsQueryBoundP
      (((gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ) gq).run s).run)
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      (if isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (.inl gq) = true
        then 1 else 0) := by
  have hL : (((gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ) gq).run s).run)
      = (query (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (.inl gq) : OracleComp _ _) >>= fun challenge =>
            (uniformDeserializePreimage (pSpec := pSpec) (U := U)
              (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge) >>= fun v =>
              pure (some (v, s)) := by
    unfold gImplDecodedChallenge
    simp only [StateT.run_bind, StateT.run_lift, OptionT.run_bind,
      Option.elimM, Option.elim, bind_pure_comp]
    rfl
  rw [hL]
  simp only [HasQuery.instOfMonadLift_query]
  refine (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨?_, fun u => ?_⟩
  · by_cases hbad : isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (.inl gq) = true
    · exact Or.inr (by simp [hbad])
    · exact Or.inl hbad
  · have hzero : IsQueryBoundP
        ((uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := eSpec (U := U) StmtIn pSpec δ) u) >>= fun v =>
          pure (some (v, s)))
        (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j
          = true) 0 :=
      isQueryBoundP_bind (n := 0) (m := 0)
        (uniformDeserializePreimage_badKey_budget u)
        (fun v _ => isQueryBoundP_pure _ _ _)
    exact hzero.mono (Nat.zero_le _)

/-- The §5.4 dispatcher with the `Hyb₂` realization plugged in makes no bad `eSpec` query:
the dispatcher emits only image-checked `gSpec` keys (the invariant), and the realization
forwards each to the *same* `eSpec` key. -/
private lemma d2sQueryImpl_decoded_run_badKey_budget
    (dsq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : PUnit) :
    IsQueryBoundP
      ((((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (m := StateT PUnit (OptionT (OracleComp
            (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)))))
          (gImpl := gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ))
          (auxImpl := d2fAuxImpl)
          dsq).run s₁).run s₂).run)
      (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j = true)
      0 := by
  unfold d2sQueryImpl
  refine isQueryBoundP_run2_bind (n := 0) (m := 0) ?_ (fun pairOpt m' => ?_)
  · refine isQueryBoundP_simulateQ_stateT_optionT_of_step
      (p := fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j
        = true)
      (d2sQueryStep_badKey_budget dsq s₁) (fun t s => ?_) s₂
    match t with
    | Sum.inl gq =>
        simp only [QueryImpl.add_apply_inl]
        exact gImplDecodedChallenge_step_badKey gq s
    | Sum.inr aux =>
        simp only [QueryImpl.add_apply_inr]
        have h0 : IsQueryBoundP
            ((query (spec := D2SChallengePlusUnitOracle (U := U)
                (eSpec (U := U) StmtIn pSpec δ)) (Sum.inr aux) :
                OracleComp (D2SChallengePlusUnitOracle (U := U)
                  (eSpec (U := U) StmtIn pSpec δ)) _)
              >>= fun u => pure (some (u, s)))
            (fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j
              = true) 0 := by
          simp only [HasQuery.instOfMonadLift_query]
          exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
            ⟨Or.inl (by simp [isBadChalKey]), fun u => isQueryBoundP_pure _ _ _⟩
        exact h0.mono (Nat.zero_le _)
  · match pairOpt with
    | none => exact isQueryBoundP_run2_lift_failure _ _
    | some p =>
        simp only [StateT.run_pure, OptionT.run_pure]
        exact isQueryBoundP_pure _ _ _

/-- Per-source-query budget of the outer `Hyb₂` implementation: no bad `eSpec` key is ever
queried (shared queries forward to `oSpec`; duplex-sponge queries run the dispatcher). -/
private lemma d2fOuterImpl_decoded_badKey_step
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : PUnit) :
    IsQueryBoundP
      ((((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
          (gImpl := gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ)) t).run s₁).run
            s₂).run)
      (fun j => isBadOuterKey (ι := ι) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (δ := δ) j = true)
      0 := by
  match t with
  | Sum.inl qo =>
      rw [d2fOuterImpl_run_inl]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨Or.inl (by simp [isBadOuterKey]), fun u => isQueryBoundP_pure _ _ _⟩
  | Sum.inr dsq =>
      rw [d2fOuterImpl_run_inr]
      refine isQueryBoundP_simulateQ_inclusion
        (p := fun j => isBadChalKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j
          = true)
        (d2sQueryImpl_decoded_run_badKey_budget dsq s₁ s₂) (fun t => ?_)
      match t with
      | Sum.inl k => simp [isBadOuterKey, isBadChalKey]
      | Sum.inr aux => simp [isBadOuterKey, isBadChalKey]

/-- **The reachability invariant, pipeline level**: along the full `Hyb₂` pipeline (`d2fRaw`
with the `Hyb₂` realization `gImplDecodedChallenge`), **no parse-failed `eSpec` key is ever
queried** — for *any* driving computation (the malicious prover or the honest verifier's
replay) and any initial memo state. -/
theorem d2fRaw_decoded_badKey_budget {α : Type}
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α) (initM : PUnit) :
    IsQueryBoundP
      ((d2fRaw (T_H := T_H) (T_P := T_P)
        (gImpl := gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ)) comp initM).run)
      (fun j => isBadOuterKey (ι := ι) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (δ := δ) j = true)
      0 := by
  unfold d2fRaw
  refine isQueryBoundP_simulateQ_stateT2_optionT_of_step (p := fun _ => False)
    (isQueryBoundP_false comp 0)
    (fun t s₁ s₂ => ?_) default initM
  simpa using d2fOuterImpl_decoded_badKey_step t s₁ s₂

/-- The invariant survives the logging layer of `hybGameEager`. -/
theorem d2fRaw_decoded_logged_badKey_budget {α : Type}
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α) (initM : PUnit) :
    IsQueryBoundP
      ((simulateQ loggingOracle
        ((d2fRaw (T_H := T_H) (T_P := T_P)
          (gImpl := gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ)) comp initM).run)).run)
      (fun j => isBadOuterKey (ι := ι) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (δ := δ) j = true)
      0 :=
  (OracleComp.isQueryBoundP_run_simulateQ_loggingOracle_iff _ _ 0).mpr
    (d2fRaw_decoded_badKey_budget comp initM)

end PipelineInvariant

/-! ## Good-cell locality of the `Hyb₂` game body (invariant + keystone, any `δ`) -/

section BodyLocality

variable {δ : ℕ} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- **Good-cell locality of the `Hyb₂` game body**: at any fixed `eSpec` tables agreeing on
all parse-successful keys, the `Hyb₂` bodies are *equal* `ProbComp` programs. This is the
game-level consumption of the reachability invariant: parse-failed cells of the table are
unreachable, hence invisible. -/
theorem hybGameEagerBody_decoded_congr [SampleableType U]
    (e₁ e₂ : OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (hagree : ∀ k, (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2).isSome →
      e₁ k = e₂ k)
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    hybGameEagerBody (T_H := T_H) (T_P := T_P) δ
        (tableQueryImpl e₁) (gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ))
        (hyb2Line4TraceEager (δ := δ)) oImpl V P
      = hybGameEagerBody (T_H := T_H) (T_P := T_P) δ
          (tableQueryImpl e₂) (gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ))
          (hyb2Line4TraceEager (δ := δ)) oImpl V P := by
  have himpl : ∀ t, ¬ (isBadOuterKey (ι := ι) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) t = true) →
      (oImpl + (tableQueryImpl e₁ + (d2sUnitSampleImpl (U := U)
        + (fun m => (liftM (unifSpec.query m) : ProbComp _))))) t
        = (oImpl + (tableQueryImpl e₂ + (d2sUnitSampleImpl (U := U)
          + (fun m => (liftM (unifSpec.query m) : ProbComp _))))) t := by
    intro t hnt
    match t with
    | .inl qo => rfl
    | .inr (.inl k) =>
        have hgood : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U)
            k.1 k.2.2.2).isSome := by
          rcases hop : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2
            with _ | msgs
          · exact absurd (by simp [isBadOuterKey, hop]) hnt
          · rfl
        simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        change (pure (e₁ k) : ProbComp _) = pure (e₂ k)
        rw [hagree k hgood]
    | .inr (.inr aux) => rfl
  have hcongr : ∀ {α : Type}
      (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α) (initM : PUnit),
      simulateQ (oImpl + (tableQueryImpl e₁ + (d2sUnitSampleImpl (U := U)
          + (fun m => (liftM (unifSpec.query m) : ProbComp _)))))
        ((simulateQ loggingOracle
          ((d2fRaw (T_H := T_H) (T_P := T_P)
            (gImpl := gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ))
            comp initM).run)).run)
      = simulateQ (oImpl + (tableQueryImpl e₂ + (d2sUnitSampleImpl (U := U)
          + (fun m => (liftM (unifSpec.query m) : ProbComp _)))))
        ((simulateQ loggingOracle
          ((d2fRaw (T_H := T_H) (T_P := T_P)
            (gImpl := gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ))
            comp initM).run)).run) := fun comp initM =>
    simulateQ_congr_of_isQueryBoundP_zero
      (d2fRaw_decoded_logged_badKey_budget comp initM) himpl
  simp only [hybGameEagerBody]
  rw [hcongr P default]
  refine bind_congr fun pr => ?_
  obtain ⟨pRes?, pLogRaw⟩ := pr
  cases pRes? with
  | none => rfl
  | some res =>
      obtain ⟨⟨⟨stmtIn, messages⟩, st⟩, memo⟩ := res
      dsimp only
      congr 1
      exact hcongr _ memo

end BodyLocality

/-! ## The pulled-back table and the per-query coupling at it -/

section Reindex

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-- Pull a salted basic-FS table back along the CO25 key map
`(i, 𝕩, τ̂, α̂) ↦ (i, (𝕩, bin τ̂), φ⁻¹(α̂))`: at parse-successful keys read the salted table at
the replayed key; parse-failed cells are junk (`default`) — they are unreachable by the
reachability invariant. -/
noncomputable def reindexTable
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OracleFamily (eSpec (U := U) StmtIn pSpec δ) := fun k =>
  match hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2 with
  | some msgs => c (replayKey (Salt := Salt) k msgs)
  | none => (default : pSpec.Challenge k.1)

lemma reindexTable_eq_of_parse
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (k : (gSpec (U := U) StmtIn pSpec δ).Domain)
    {msgs : pSpec.MessagesUpTo k.1.1.castSucc}
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2 = some msgs) :
    reindexTable (Salt := Salt) c k = c (replayKey (Salt := Salt) k msgs) := by
  simp only [reindexTable, hparse]

/-- **The per-query coupling at the pulled-back table**: at every parse-successful key, the
`Hyb₂` realization against `reindexTable c` and the memoless salted bridge against `c` are
equal computations — the agreement hypothesis of round 2's
`gImplDecodedChallenge_run_eq_bridgeSalted_run` holds definitionally at the pullback. -/
theorem gImplDecodedChallenge_run_eq_bridgeSalted_run_reindex
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (s : PUnit) :
    simulateQ (eTableAuxImpl (U := U) (reindexTable (Salt := Salt) c))
        (((gImplDecodedChallenge (StmtIn := StmtIn) (δ := δ) gq).run s).run)
      = simulateQ (fsTableAuxImpl (U := U) c)
          (((d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
              (δ := δ) (Salt := Salt) gq).run s).run) :=
  gImplDecodedChallenge_run_eq_bridgeSalted_run (reindexTable (Salt := Salt) c) c gq msgs
    hparse (reindexTable_eq_of_parse c gq hparse) s

end Reindex

/-! ## `δ = 0`: the good-key space, key-map injectivity, and uniform re-indexing -/

section Delta0Reindex

variable {Salt : Type} [SaltCodec U 0 Salt]

/-- Parse-successful (good) `eSpec`/`gSpec` keys at `δ = 0`. -/
@[reducible]
private def GoodKey : Type _ :=
  {k : (i : pSpec.ChallengeIdx) ×
      (StmtIn × Vector U 0 × pSpec.EncodedMessagesBefore U i.1.castSucc) //
    (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2).isSome}

/-- Good-cell value assignments: one challenge per good key. -/
@[reducible]
private def GoodSpace : Type _ :=
  (b : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) → pSpec.Challenge b.val.1

private noncomputable instance instFintypeGoodKey :
    Fintype (GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) := by
  infer_instance

private noncomputable instance instDecEqGoodKey :
    DecidableEq (GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :=
  Classical.decEq _

private noncomputable instance instFintypeGoodSpace :
    Fintype (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :=
  Pi.instFintype

/-- The salted replay key of a good key (total on `GoodKey`). -/
private noncomputable def replayKeyOfGood
    (b : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    (fsChallengeOracle (StmtIn × Salt) pSpec).Domain :=
  replayKey (Salt := Salt) b.val
    ((hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) b.val.1 b.val.2.2.2).get b.prop)

/-- **Injectivity of the CO25 key map on good keys at `δ = 0`** — from `φ⁻¹`-injectivity
plus the salt subsingleton. This is what makes the uniform re-indexing a bijection on
reachable cells, the distributional content CO25 leaves implicit in Claim 5.23. -/
theorem replayKeyOfGood_injective :
    Function.Injective
      (replayKeyOfGood (pSpec := pSpec) (StmtIn := StmtIn) (U := U) (Salt := Salt)) := by
  rintro ⟨⟨i, x, τ, em⟩, hb⟩ ⟨⟨i', x', τ', em'⟩, hb'⟩ heq
  unfold replayKeyOfGood at heq
  dsimp only at heq hb hb'
  obtain ⟨hi, hsnd⟩ := Sigma.mk.inj heq
  subst hi
  have hsnd' := eq_of_heq hsnd
  have hx : x = x' := congrArg (fun p => p.1.1) hsnd'
  have hM : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em).get hb
      = (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em').get hb' :=
    congrArg Prod.snd hsnd'
  have hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em
      = some ((hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em).get hb) :=
    (Option.some_get hb).symm
  have hparse' : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em'
      = some ((hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em).get hb) := by
    rw [hM]
    exact (Option.some_get hb').symm
  have hem : em = em' :=
    hybEncodedMessagesBefore?_inj i em em' _ hparse hparse'
  obtain rfl : x = x' := hx
  obtain rfl : em = em' := hem
  obtain rfl : τ = τ' := Hyb23Delta0.vector_zero_eq τ τ'
  rfl

/-! ### The two fiber-swap involutions (E-side and C-side) -/

/-- Swap the values of an `eSpec` table at every good key (between the two target
assignments); junk cells untouched. -/
private noncomputable def eSwapFun
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U))
    (e : OracleFamily (eSpec (U := U) StmtIn pSpec 0)) :
    OracleFamily (eSpec (U := U) StmtIn pSpec 0) := fun q =>
  if h : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) q.1 q.2.2.2).isSome
  then (Equiv.swap (v₁ ⟨q, h⟩) (v₂ ⟨q, h⟩)) (e q)
  else e q

private lemma eSwapFun_involutive
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    Function.Involutive (eSwapFun (pSpec := pSpec) (StmtIn := StmtIn) (U := U) v₁ v₂) := by
  intro e
  funext q
  unfold eSwapFun
  by_cases h : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) q.1 q.2.2.2).isSome
  · rw [dif_pos h, dif_pos h, Equiv.swap_apply_self]
  · rw [dif_neg h, dif_neg h]

/-- Read off the good cells of an `eSpec` table. -/
private noncomputable def pullE (e : OracleFamily (eSpec (U := U) StmtIn pSpec 0)) :
    GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U) := fun b => e b.val

private lemma pullE_eSwapFun
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U))
    (e : OracleFamily (eSpec (U := U) StmtIn pSpec 0)) :
    pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) (eSwapFun v₁ v₂ e)
      = fun b => Equiv.swap (v₁ b) (v₂ b) (pullE (U := U) e b) := by
  funext b
  change (if h : _ then _ else _) = _
  rw [dif_pos b.prop]
  rfl

private lemma pullE_eSwapFun_eq_iff
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U))
    (e : OracleFamily (eSpec (U := U) StmtIn pSpec 0)) :
    pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) (eSwapFun v₁ v₂ e) = v₂
      ↔ pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) e = v₁ := by
  constructor
  · intro h
    funext b
    have hb := congrFun h b
    rw [pullE_eSwapFun] at hb
    have h2 := congrArg (Equiv.swap (v₁ b) (v₂ b)) hb
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
    exact h2
  · intro h
    funext b
    rw [pullE_eSwapFun]
    simp only [congrFun h b, Equiv.swap_apply_left]

/-- Swap the values of a salted table along the (injective) image of the good keys. -/
private noncomputable def cSwapFun
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec) := fun q =>
  letI : Decidable (∃ b : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      replayKeyOfGood (Salt := Salt) b = q) := Classical.propDecidable _
  if h : ∃ b : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      replayKeyOfGood (Salt := Salt) b = q then
    (Equiv.swap
      (cast (congrArg (fun s => pSpec.Challenge s.1) h.choose_spec) (v₁ h.choose))
      (cast (congrArg (fun s => pSpec.Challenge s.1) h.choose_spec) (v₂ h.choose))) (c q)
  else c q

/-- Kill a transport along a self-equal index (the `choose = b` collapse). -/
private lemma cast_pull_val
    {b b' : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U)} (hbb : b' = b)
    (E : pSpec.Challenge (replayKeyOfGood (Salt := Salt) b').1
      = pSpec.Challenge (replayKeyOfGood (Salt := Salt) b).1)
    (v : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    cast E (v b') = v b := by
  subst hbb
  exact cast_eq_iff_heq.mpr HEq.rfl

private lemma cSwapFun_apply_image
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (b : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    cSwapFun (Salt := Salt) v₁ v₂ c (replayKeyOfGood (Salt := Salt) b)
      = Equiv.swap (v₁ b) (v₂ b) (c (replayKeyOfGood (Salt := Salt) b)) := by
  unfold cSwapFun
  have hex : ∃ b' : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      replayKeyOfGood (Salt := Salt) b' = replayKeyOfGood (Salt := Salt) b := ⟨b, rfl⟩
  rw [dif_pos hex]
  have hbb : hex.choose = b := replayKeyOfGood_injective hex.choose_spec
  have h₁ : cast (congrArg (fun s => pSpec.Challenge s.1) hex.choose_spec)
      (v₁ hex.choose) = v₁ b := cast_pull_val (Salt := Salt) hbb _ v₁
  have h₂ : cast (congrArg (fun s => pSpec.Challenge s.1) hex.choose_spec)
      (v₂ hex.choose) = v₂ b := cast_pull_val (Salt := Salt) hbb _ v₂
  exact congrArg₂
    (fun w₁ w₂ : pSpec.Challenge b.val.1 =>
      (Equiv.swap w₁ w₂) (c (replayKeyOfGood (Salt := Salt) b)))
    h₁ h₂

private lemma cSwapFun_involutive
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    Function.Involutive (cSwapFun (Salt := Salt) v₁ v₂) := by
  intro c
  funext q
  unfold cSwapFun
  by_cases h : ∃ b : GoodKey (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      replayKeyOfGood (Salt := Salt) b = q
  · rw [dif_pos h, dif_pos h, Equiv.swap_apply_self]
  · rw [dif_neg h, dif_neg h]

/-- Read off the good cells of a salted table along the key map. -/
private noncomputable def pullC
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U) := fun b =>
  c (replayKeyOfGood (Salt := Salt) b)

private lemma pullC_cSwapFun
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    pullC (Salt := Salt) (cSwapFun (Salt := Salt) v₁ v₂ c)
      = fun b => Equiv.swap (v₁ b) (v₂ b) (pullC (Salt := Salt) c b) := by
  funext b
  exact cSwapFun_apply_image v₁ v₂ c b

private lemma pullC_cSwapFun_eq_iff
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    pullC (Salt := Salt) (cSwapFun (Salt := Salt) v₁ v₂ c) = v₂
      ↔ pullC (Salt := Salt) c = v₁ := by
  constructor
  · intro h
    funext b
    have hb := congrFun h b
    rw [pullC_cSwapFun] at hb
    have h2 := congrArg (Equiv.swap (v₁ b) (v₂ b)) hb
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
    exact h2
  · intro h
    funext b
    rw [pullC_cSwapFun]
    simp only [congrFun h b, Equiv.swap_apply_left]

/-! ### Both good-cell pushforwards are uniform -/

private lemma probOutput_map_pullE_eq
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    Pr[= v₁ | pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) <$>
        ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
      = Pr[= v₂ | pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) <$>
          ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0))] := by
  classical
  rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
  rw [← Equiv.tsum_eq (Function.Involutive.toPerm _ (eSwapFun_involutive v₁ v₂))
    (fun e => Pr[= e | $ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0)]
      * Pr[= v₂ | (pure (pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) e) :
          ProbComp (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)))])]
  refine tsum_congr fun e => ?_
  have hsample : Pr[= eSwapFun (pSpec := pSpec) (StmtIn := StmtIn) (U := U) v₁ v₂ e |
        $ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0)]
      = Pr[= e | $ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0)] :=
    probOutput_uniformSample_inj _ _ _
  have hpure : Pr[= v₂ | (pure (pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U)
        (eSwapFun v₁ v₂ e)) :
        ProbComp (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)))]
      = Pr[= v₁ | (pure (pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) e) :
          ProbComp (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)))] := by
    rw [probOutput_pure, probOutput_pure]
    by_cases h : pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) e = v₁
    · have h2 := (pullE_eSwapFun_eq_iff v₁ v₂ e).mpr h
      rw [if_pos h2.symm, if_pos h.symm]
    · have h2 : ¬ pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U)
          (eSwapFun v₁ v₂ e) = v₂ :=
        fun hh => h ((pullE_eSwapFun_eq_iff v₁ v₂ e).mp hh)
      rw [if_neg (fun hh => h2 hh.symm), if_neg (fun hh => h hh.symm)]
  exact hsample ▸ hpure ▸ rfl

private lemma probOutput_map_pullE
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    (v : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    Pr[= v | pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) <$>
        ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
      = (Fintype.card (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) : ℝ≥0∞)⁻¹ := by
  classical
  have hfail : Pr[⊥ | pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) <$>
      ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0))] = 0 := by
    rw [probFailure_map]
    exact HasEvalPMF.probFailure_eq_zero _
  have hsum : ∑ v' : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      Pr[= v' | pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) <$>
        ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0))] = 1 :=
    sum_probOutput_eq_one hfail
  have hconst : ∑ _v' : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      Pr[= v | pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) <$>
        ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0))] = 1 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun v' _ => probOutput_map_pullE_eq v v'
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] at hconst
  exact ENNReal.eq_inv_of_mul_eq_one_left hconst

private lemma probOutput_map_pullC_eq
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (v₁ v₂ : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    Pr[= v₁ | pullC (Salt := Salt) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
      = Pr[= v₂ | pullC (Salt := Salt) <$>
          ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] := by
  classical
  rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
  rw [← Equiv.tsum_eq (Function.Involutive.toPerm _ (cSwapFun_involutive v₁ v₂))
    (fun c => Pr[= c | $ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)]
      * Pr[= v₂ | (pure (pullC (Salt := Salt) c) :
          ProbComp (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)))])]
  refine tsum_congr fun c => ?_
  have hsample : Pr[= cSwapFun (Salt := Salt) v₁ v₂ c |
        $ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)]
      = Pr[= c | $ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)] :=
    probOutput_uniformSample_inj _ _ _
  have hpure : Pr[= v₂ | (pure (pullC (Salt := Salt) (cSwapFun (Salt := Salt) v₁ v₂ c)) :
        ProbComp (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)))]
      = Pr[= v₁ | (pure (pullC (Salt := Salt) c) :
          ProbComp (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)))] := by
    rw [probOutput_pure, probOutput_pure]
    by_cases h : pullC (Salt := Salt) c = v₁
    · have h2 := (pullC_cSwapFun_eq_iff v₁ v₂ c).mpr h
      rw [if_pos h2.symm, if_pos h.symm]
    · have h2 : ¬ pullC (Salt := Salt) (cSwapFun (Salt := Salt) v₁ v₂ c) = v₂ :=
        fun hh => h ((pullC_cSwapFun_eq_iff v₁ v₂ c).mp hh)
      rw [if_neg (fun hh => h2 hh.symm), if_neg (fun hh => h hh.symm)]
  exact hsample ▸ hpure ▸ rfl

private lemma probOutput_map_pullC
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (v : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    Pr[= v | pullC (Salt := Salt) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
      = (Fintype.card (GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) : ℝ≥0∞)⁻¹ := by
  classical
  have hfail : Pr[⊥ | pullC (pSpec := pSpec) (StmtIn := StmtIn) (U := U) (Salt := Salt) <$>
      ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] = 0 := by
    rw [probFailure_map]
    exact HasEvalPMF.probFailure_eq_zero _
  have hsum : ∑ v' : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      Pr[= v' | pullC (Salt := Salt) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] = 1 :=
    sum_probOutput_eq_one hfail
  have hconst : ∑ _v' : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U),
      Pr[= v | pullC (Salt := Salt) <$>
        ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))] = 1 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun v' _ => probOutput_map_pullC_eq v v'
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] at hconst
  exact ENNReal.eq_inv_of_mul_eq_one_left hconst

/-! ### Uniform re-indexing along the key map -/

/-- Extend a good-cell assignment to a full `eSpec` table by junk on parse-failed cells. -/
private noncomputable def extendGood
    (v : GoodSpace (pSpec := pSpec) (StmtIn := StmtIn) (U := U)) :
    OracleFamily (eSpec (U := U) StmtIn pSpec 0) := fun k =>
  if h : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2).isSome
  then v ⟨k, h⟩ else (default : pSpec.Challenge k.1)

/-- **Uniform re-indexing at `δ = 0`** (the distributional content of CO25 Claim 5.23's
query re-format): binding any good-cell-local continuation on a uniform `eSpec` table is
the same as binding it on the pullback of a uniform salted basic-FS table. Proven by
pushing both samples to the good-cell space (two fiber-swap involutions) where the key map
is a bijection (`replayKeyOfGood_injective`). -/
theorem probOutput_uniformE_bind_eq_uniformSalted_reindex {γ : Type}
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (g : OracleFamily (eSpec (U := U) StmtIn pSpec 0) → ProbComp γ)
    (hloc : ∀ e₁ e₂ : OracleFamily (eSpec (U := U) StmtIn pSpec 0),
      (∀ k, (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) k.1 k.2.2.2).isSome →
        e₁ k = e₂ k) → g e₁ = g e₂)
    (z : γ) :
    Pr[= z | ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0)) >>= g]
      = Pr[= z | ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun c =>
          g (reindexTable (Salt := Salt) c)] := by
  classical
  have hge : ∀ e, g e = g (extendGood (pullE (pSpec := pSpec) (StmtIn := StmtIn)
      (U := U) e)) := fun e =>
    hloc _ _ (fun k h => by
      simp only [extendGood, dif_pos h]
      rfl)
  have hgc : ∀ c, g (reindexTable (Salt := Salt) c)
      = g (extendGood (pullC (Salt := Salt) c)) := fun c =>
    hloc _ _ (fun k h => by
      rw [reindexTable_eq_of_parse c k (Option.some_get h).symm]
      simp only [extendGood, dif_pos h]
      rfl)
  have hassocE : (($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0)) >>= g)
      = (pullE (pSpec := pSpec) (StmtIn := StmtIn) (U := U) <$>
          ($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0))) >>= fun v =>
            g (extendGood v) := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp only [Function.comp_apply, pure_bind]
    exact bind_congr fun e => hge e
  have hassocC : (($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun c =>
        g (reindexTable (Salt := Salt) c))
      = (pullC (Salt := Salt) <$>
          ($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))) >>= fun v =>
            g (extendGood v) := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp only [Function.comp_apply, pure_bind]
    exact bind_congr fun c => hgc c
  rw [hassocE, hassocC, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun v => ?_
  rw [probOutput_map_pullE v, probOutput_map_pullC v]

end Delta0Reindex

/-! ## Assembly: the reduction theorem for step A at `δ = 0` -/

section Assembly

/-- **The fixed-table cross-spec lift residual at `δ = 0`** (named obligation, NOT proven):
at every *fixed* salted table `c`, the `Hyb₂` body at the pulled-back table `reindexTable c`
and the `Hyb3SaltedFresh` body at `c` have the same output distribution.

This is the residual plumbing of step A at `δ = 0` — the per-query coupling
(`gImplDecodedChallenge_run_eq_bridgeSalted_run_reindex`, proven, applicable at every
reachable key by the reachability invariant `d2fRaw_decoded_badKey_budget`) lifted through
`d2fRaw`/`loggingOracle`, with `hyb2Line4TraceEager` and `eraseSaltLog` reconciling the
paired raw logs. All probabilistic content of the step (the uniform-table re-indexing,
`probOutput_uniformE_bind_eq_uniformSalted_reindex`) is **already discharged** by
`hyb23DecodedQuery_delta0_of_crossLift`; what remains is a deterministic-coupling
`simulateQ` bisimulation — the same plumbing class as step C's
`Hyb23SaltErasureLiftDelta0Residual`. -/
def Hyb23DecodedCrossLiftDelta0Residual [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)),
    𝒟[hybGameEagerBody (T_H := T_H) (T_P := T_P) 0
        (tableQueryImpl (reindexTable (Salt := Salt) c))
        (gImplDecodedChallenge (StmtIn := StmtIn) (δ := 0))
        (hyb2Line4TraceEager (δ := 0)) oImpl V P]
      = 𝒟[hybGameEagerBody (T_H := T_H) (T_P := T_P) 0
          (tableQueryImpl c)
          (d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (δ := 0) (Salt := Salt))
          (saltErasingLineFour (Salt := Salt)) oImpl V P]

/-- **Step A holds at `δ = 0`, modulo the fixed-table cross-spec lift** (the reduction
theorem): the named deterministic-coupling residual implies the full
`Hyb23DecodedQueryResidual` at `δ = 0`. The reachability invariant and the uniform-table
re-indexing — including `φ⁻¹`-injectivity on its success domain — are discharged. -/
theorem hyb23DecodedQuery_delta0_of_crossLift [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (Salt : Type) [SaltCodec U 0 Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec 0))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (hcross : Hyb23DecodedCrossLiftDelta0Residual (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) T_H T_P Salt oImpl) :
    Hyb23DecodedQueryResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P 0 Salt oImpl := by
  intro V P
  have h2 : Hyb2 (pSpec := pSpec) T_H T_P 0 oImpl V P
      = 𝒟[($ᵗ OracleFamily (eSpec (U := U) StmtIn pSpec 0)) >>= fun e =>
          hybGameEagerBody (T_H := T_H) (T_P := T_P) 0 (tableQueryImpl e)
            (gImplDecodedChallenge (StmtIn := StmtIn) (δ := 0))
            (hyb2Line4TraceEager (δ := 0)) oImpl V P] :=
    congrArg (𝒟[·]) (hybGameEager_uniform_eq 0
      (gImplDecodedChallenge (StmtIn := StmtIn) (δ := 0))
      (hyb2Line4TraceEager (δ := 0)) oImpl V P)
  have h3 : Hyb3SaltedFresh (pSpec := pSpec) T_H T_P 0 Salt oImpl V P
      = 𝒟[($ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun c =>
          hybGameEagerBody (T_H := T_H) (T_P := T_P) 0 (tableQueryImpl c)
            (d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (δ := 0) (Salt := Salt))
            (saltErasingLineFour (Salt := Salt)) oImpl V P] :=
    congrArg (𝒟[·]) (hybGameEager_uniform_eq 0
      (d2sCodecBridgeImplSalted (U := U) (StmtIn := StmtIn) (δ := 0) (Salt := Salt))
      (saltErasingLineFour (Salt := Salt)) oImpl V P)
  have hgames : Hyb2 (pSpec := pSpec) T_H T_P 0 oImpl V P
      = Hyb3SaltedFresh (pSpec := pSpec) T_H T_P 0 Salt oImpl V P := by
    rw [h2, h3]
    refine evalDist_ext fun z => ?_
    rw [probOutput_uniformE_bind_eq_uniformSalted_reindex (Salt := Salt)
      (g := fun e => hybGameEagerBody (T_H := T_H) (T_P := T_P) 0 (tableQueryImpl e)
        (gImplDecodedChallenge (StmtIn := StmtIn) (δ := 0))
        (hyb2Line4TraceEager (δ := 0)) oImpl V P)
      (fun e₁ e₂ h => hybGameEagerBody_decoded_congr e₁ e₂ h oImpl V P) z]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun c => ?_
    rw [evalDist_ext_iff.mp (hcross V P c) z]
  rw [hgames, SPMF.tvDist_self]

end Assembly

#print axioms DuplexSpongeFS.Hyb23Decoded.hybEncodedMessagesBefore?_isSome_of_image
#print axioms DuplexSpongeFS.Hyb23Decoded.d2sInCodecImage_parse_isSome
#print axioms DuplexSpongeFS.Hyb23Decoded.hybEncodedMessagesBefore?_inj
#print axioms DuplexSpongeFS.Hyb23Decoded.isQueryBoundP_zero_of_imp
#print axioms DuplexSpongeFS.Hyb23Decoded.simulateQ_congr_of_isQueryBoundP_zero
#print axioms DuplexSpongeFS.Hyb23Decoded.d2sQueryStep_badKey_budget
#print axioms DuplexSpongeFS.Hyb23Decoded.d2fRaw_decoded_badKey_budget
#print axioms DuplexSpongeFS.Hyb23Decoded.d2fRaw_decoded_logged_badKey_budget
#print axioms DuplexSpongeFS.Hyb23Decoded.hybGameEagerBody_decoded_congr
#print axioms DuplexSpongeFS.Hyb23Decoded.gImplDecodedChallenge_run_eq_bridgeSalted_run_reindex
#print axioms DuplexSpongeFS.Hyb23Decoded.replayKeyOfGood_injective
#print axioms DuplexSpongeFS.Hyb23Decoded.probOutput_uniformE_bind_eq_uniformSalted_reindex
#print axioms DuplexSpongeFS.Hyb23Decoded.hyb23DecodedQuery_delta0_of_crossLift

end DuplexSpongeFS.Hyb23Decoded

end
