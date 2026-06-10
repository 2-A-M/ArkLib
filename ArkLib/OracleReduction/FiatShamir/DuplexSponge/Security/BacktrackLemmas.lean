/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

/-!
# Backtrack case analyses for the honest bad events (M2: CO25 Lemmas 5.12 / 5.14 / 5.16)

This module proves the three complementary-event reductions of the §5.6 bad-event analysis
with the *honest* event definitions (`E_inv_honest` / `E_fork_honest` / `E_time_honest` over
`Backtrack.S_BT`, KeyLemmaFoundations F9), replacing the vacuous placebo forms in
`BadEvents.lean` (`E tr ∧ state = 0`):

- **Lemma 5.12** (`lemma5_12Honest_of_noRedundant`): off the combined collision event `E`,
  no chain link of any backtracking sequence is anchored by an inverse-permutation entry.
- **Lemma 5.14** (`lemma5_14Honest_of_noRedundant`): off `E`, the backtracking family has at
  most one maximal sequence. The proof factors through the stronger
  `backtrackSequence_unique`: off `E` *any two* backtracking sequences ending at the same
  state are equal (backward chain-uniqueness; CO25's fork analysis).
- **Lemma 5.16** (`lemma5_16Honest_of_noRedundant`): off `E`, the first-occurrence indices
  of the chain queries respect the chain order (no out-of-order hash, Eq. 41; no
  out-of-order permutation, Eq. 42).

All three are proven for **redundancy-free traces** (`NoRedundantEntryDS tr`), which is the
CO25 setting: the paper's §5.2 BackTrack and the §5.6 events run over the *deduplicated*
trace, and the in-tree `E` is itself defined over `removeRedundantEntryDS tr`.

## Proof architecture

1. `removeRedundantEntryDS_eq_self`: redundancy-free traces are fixed points of the dedup
   procedure, so the `E`-disjuncts can be read directly over `tr`.
2. Coverage bricks `E_of_*`: each capacity-collision pattern that the chain conditions can
   produce is matched to the `E_h` / `E_p` / `E_pinv` disjunct covering it. The order-free
   patterns (answer-capacity vs answer-capacity) are covered in both relative trace orders;
   the directional patterns (query-capacity vs answer-capacity) exactly when the
   query-capacity entry occurs no later — which is the orientation the timing analysis
   (Lemma 5.16) produces.
3. `E_of_bwd_chain_entry` (5.12 core): induction on the lowest inverse-anchored link. Link 0
   collides with the hash anchor (order-free pair); link `ι+1` collides with link `ι`'s
   forward answer (order-free pair); an inverse-anchored link `ι` below recurses.
4. `backtrackSequence_unique` (5.14 core): with all links forward-anchored (by 3), walk the
   two chains backwards from the shared final state; at each junction the two forward
   answers share a capacity, so off `E` they are the *same* trace entry
   (`fwdAns_cap_inj`). A length mismatch puts a hash answer capacity on a forward answer
   (order-free pair); distinct statements collide two hash answers.
5. 5.16 core: the relevant `J_BT` first-occurrence index facts are extracted from
   `BacktrackSequence.Index` (`Index_fst_spec` / `Index_snd_spec`), and each out-of-order
   configuration is exactly one directional coverage brick (or an inverse anchor, killed
   by 3).

## The general (redundant-trace) statements

`Lemma5_12HonestResidual` as stated in KeyLemmaFoundations quantifies over **all** raw
traces, while `E` reads the deduplicated trace. These two surfaces genuinely diverge:
dedup can keep only the orientation-*swap* of a raw inverse anchor, hiding `E_inv` from
`E`. This is **machine-checked**: `lemma5_12HonestResidual_not_universal` and
`lemma5_12HonestRedundantResidual_not_universal` below disprove the universally-quantified
original M2a surface via a concrete 3-entry trace. The original M2 residuals are reduced
to the proven redundancy-free cores plus the named redundant-trace corner residuals
(`lemma5_1*HonestResidual_of_redundantResidual`), which is the finest honest split; for
5.14/5.16 the corners remain open (an order-preserving dedup transport is the missing
ingredient — plausibly true since every dedup swap turns the relevant query capacity into
an answer capacity).
-/

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS
open DuplexSpongeFS DuplexSpongeFS.Backtrack DuplexSpongeFS.KeyLemmaFoundations

namespace DuplexSpongeFS.BacktrackLemmas

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-! ## Dedup fixed point -/

/-- A trace with no redundant entries is a fixed point of `removeRedundantEntryDS`, so the
`E`-events can be read directly over `tr` (CO25 §5.5: the events are stated for the
deduplicated trace). -/
lemma removeRedundantEntryDS_eq_self (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hNR : tr.NoRedundantEntryDS) :
    removeRedundantEntryDS tr = ⟨tr, hNR⟩ := by
  have hne : ¬∃ idx : Fin tr.length, tr.redundantEntryDS idx := by
    rintro ⟨idx, hidx⟩
    exact hNR idx hidx
  rw [removeRedundantEntryDS, dif_neg hne]

/-! ## Coverage bricks: capacity collisions force `E` on redundancy-free traces

Each brick exhibits one `E_h` / `E_p` / `E_pinv` disjunct (CO25 §5.6) for a pair of trace
entries sharing a capacity segment. "Order-free" bricks cover both relative trace orders
(the colliding capacities are both *answer* capacities, and the `< j` / `≤ j` disjuncts of
the three events cover both orientations); "directional" bricks require the query-capacity
entry to occur no later than the answer-capacity trigger. -/

section CoverageBricks

variable (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))

/-- Order-free: two hash entries with distinct statements but equal answer capacities
force `E` (the `E_h` self-disjunct). -/
lemma E_of_hashAns_hashAns (hNR : tr.NoRedundantEntryDS) {x x' : StmtIn}
    {c : Vector U SpongeSize.C}
    (h1 : (⟨.inl x, c⟩ : duplexSpongeTraceEntry) ∈ tr)
    (h2 : (⟨.inl x', c⟩ : duplexSpongeTraceEntry) ∈ tr)
    (hne : x ≠ x') :
    E tr := by
  rw [List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  have hij : i ≠ j := by
    intro h
    subst h
    rw [hgi] at hgj
    exact hne (congrArg (fun e => match e with | ⟨.inl s, _⟩ => s | _ => x) hgj)
  have hh : capacitySegmentDupHash (StmtIn := StmtIn) (U := U) tr := by
    unfold capacitySegmentDupHash
    rw [removeRedundantEntryDS_eq_self tr hNR]
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨⟨j, hj⟩, c, x', hgj, ⟨i, hi⟩, hlt, x, Or.inl hgi⟩
    · exact ⟨⟨i, hi⟩, c, x, hgi, ⟨j, hj⟩, hlt, x', Or.inl hgj⟩
  exact Or.inl (Or.inl hh)

/-- Order-free: a hash answer capacity colliding with a forward-permutation **answer**
capacity forces `E` (`E_h` disjunct 2 / `E_p` disjunct 1, depending on order). -/
lemma E_of_hashAns_fwdAns (hNR : tr.NoRedundantEntryDS) {x : StmtIn}
    {c : Vector U SpongeSize.C} {a b : CanonicalSpongeState U}
    (h1 : (⟨.inl x, c⟩ : duplexSpongeTraceEntry) ∈ tr)
    (h2 : (⟨.inr (.inl a), b⟩ : duplexSpongeTraceEntry) ∈ tr)
    (hcap : b.capacitySegment = c) :
    E tr := by
  rw [List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  have hij : i ≠ j := by
    intro h
    subst h
    rw [hgi] at hgj
    exact absurd (congrArg Sigma.fst hgj) (by simp)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · -- hash first → trigger `E_p` at the forward entry
    have hp : capacitySegmentDupPerm (StmtIn := StmtIn) (U := U) tr := by
      unfold capacitySegmentDupPerm
      rw [removeRedundantEntryDS_eq_self tr hNR]
      exact ⟨⟨j, hj⟩, c, ⟨a, b, hgj, hcap⟩, Or.inl ⟨⟨i, hi⟩, hlt, x, hgi⟩⟩
    exact Or.inl (Or.inr (Or.inl hp))
  · -- forward entry first → trigger `E_h` at the hash entry
    have hh : capacitySegmentDupHash (StmtIn := StmtIn) (U := U) tr := by
      unfold capacitySegmentDupHash
      rw [removeRedundantEntryDS_eq_self tr hNR]
      exact ⟨⟨i, hi⟩, c, x, hgi, ⟨j, hj⟩, hlt, x,
        Or.inr (Or.inl ⟨a, b, hgj, hcap⟩)⟩
    exact Or.inl (Or.inl hh)

/-- Order-free: a hash answer capacity colliding with an inverse-permutation **answer**
capacity forces `E` (`E_h` disjunct 3 / `E_pinv` disjunct 1, depending on order). -/
lemma E_of_hashAns_bwdAns (hNR : tr.NoRedundantEntryDS) {x : StmtIn}
    {c : Vector U SpongeSize.C} {sOut sIn : CanonicalSpongeState U}
    (h1 : (⟨.inl x, c⟩ : duplexSpongeTraceEntry) ∈ tr)
    (h2 : (⟨.inr (.inr sOut), sIn⟩ : duplexSpongeTraceEntry) ∈ tr)
    (hcap : sIn.capacitySegment = c) :
    E tr := by
  rw [List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  have hij : i ≠ j := by
    intro h
    subst h
    rw [hgi] at hgj
    exact absurd (congrArg Sigma.fst hgj) (by simp)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · -- hash first → trigger `E_pinv` at the inverse entry
    have hpinv : capacitySegmentDupPermInv (StmtIn := StmtIn) (U := U) tr := by
      unfold capacitySegmentDupPermInv
      rw [removeRedundantEntryDS_eq_self tr hNR]
      exact ⟨⟨j, hj⟩, c, ⟨sOut, sIn, hgj, hcap⟩, Or.inl ⟨⟨i, hi⟩, hlt, x, hgi⟩⟩
    exact Or.inl (Or.inr (Or.inr hpinv))
  · -- inverse entry first → trigger `E_h` at the hash entry
    have hh : capacitySegmentDupHash (StmtIn := StmtIn) (U := U) tr := by
      unfold capacitySegmentDupHash
      rw [removeRedundantEntryDS_eq_self tr hNR]
      exact ⟨⟨i, hi⟩, c, x, hgi, ⟨j, hj⟩, hlt, x,
        Or.inr (Or.inr (Or.inl ⟨sOut, sIn, hgj, hcap⟩))⟩
    exact Or.inl (Or.inl hh)

/-- Order-free: two distinct forward-permutation entries with equal **answer** capacities
force `E` (`E_p` disjunct 2 at the later entry). -/
lemma E_of_fwdAns_fwdAns (hNR : tr.NoRedundantEntryDS)
    {a b a' b' : CanonicalSpongeState U}
    (h1 : (⟨.inr (.inl a), b⟩ : duplexSpongeTraceEntry) ∈ tr)
    (h2 : (⟨.inr (.inl a'), b'⟩ : duplexSpongeTraceEntry) ∈ tr)
    (hcap : b.capacitySegment = b'.capacitySegment)
    (hne : ¬(a = a' ∧ b = b')) :
    E tr := by
  rw [List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  have hij : i ≠ j := by
    intro h
    subst h
    rw [hgi] at hgj
    refine hne ⟨?_, ?_⟩
    · exact congrArg (fun e => match e with | ⟨.inr (.inl s), _⟩ => s | _ => a) hgj
    · exact congrArg (fun e => match e with | ⟨.inr (.inl _), o⟩ => o | _ => b) hgj
  have hp : capacitySegmentDupPerm (StmtIn := StmtIn) (U := U) tr := by
    unfold capacitySegmentDupPerm
    rw [removeRedundantEntryDS_eq_self tr hNR]
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨⟨j, hj⟩, b'.capacitySegment, ⟨a', b', hgj, rfl⟩,
        Or.inr (Or.inl ⟨⟨i, hi⟩, hlt, a, b, hgi, hcap⟩)⟩
    · exact ⟨⟨i, hi⟩, b.capacitySegment, ⟨a, b, hgi, rfl⟩,
        Or.inr (Or.inl ⟨⟨j, hj⟩, hlt, a', b', hgj, hcap.symm⟩)⟩
  exact Or.inl (Or.inr (Or.inl hp))

/-- Order-free: a forward-permutation **answer** capacity colliding with an
inverse-permutation **answer** capacity forces `E` (`E_p` disjunct 3 / `E_pinv`
disjunct 2, depending on order). -/
lemma E_of_fwdAns_bwdAns (hNR : tr.NoRedundantEntryDS)
    {a b sOut sIn : CanonicalSpongeState U}
    (h1 : (⟨.inr (.inl a), b⟩ : duplexSpongeTraceEntry) ∈ tr)
    (h2 : (⟨.inr (.inr sOut), sIn⟩ : duplexSpongeTraceEntry) ∈ tr)
    (hcap : b.capacitySegment = sIn.capacitySegment) :
    E tr := by
  rw [List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  have hij : i ≠ j := by
    intro h
    subst h
    rw [hgi] at hgj
    exact absurd (congrArg Sigma.fst hgj) (by simp)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · -- forward first → trigger `E_pinv` at the inverse entry
    have hpinv : capacitySegmentDupPermInv (StmtIn := StmtIn) (U := U) tr := by
      unfold capacitySegmentDupPermInv
      rw [removeRedundantEntryDS_eq_self tr hNR]
      exact ⟨⟨j, hj⟩, sIn.capacitySegment, ⟨sOut, sIn, hgj, rfl⟩,
        Or.inr (Or.inl ⟨⟨i, hi⟩, hlt, a, b, hgi, hcap⟩)⟩
    exact Or.inl (Or.inr (Or.inr hpinv))
  · -- inverse first → trigger `E_p` at the forward entry (`≤ j` disjunct)
    have hp : capacitySegmentDupPerm (StmtIn := StmtIn) (U := U) tr := by
      unfold capacitySegmentDupPerm
      rw [removeRedundantEntryDS_eq_self tr hNR]
      exact ⟨⟨i, hi⟩, b.capacitySegment, ⟨a, b, hgi, rfl⟩,
        Or.inr (Or.inr (Or.inl ⟨⟨j, hj⟩, le_of_lt hlt, sOut, sIn, hgj,
          hcap.symm ▸ rfl⟩))⟩
    exact Or.inl (Or.inr (Or.inl hp))

/-- Directional: a forward-permutation **query** capacity occurring strictly before a hash
entry with the same answer capacity forces `E` (`E_h` disjunct 4; this is the out-of-order
hash configuration of CO25 Eq. 41). -/
lemma E_of_fwdQuery_before_hashAns (hNR : tr.NoRedundantEntryDS) {i j : ℕ}
    (hi : i < tr.length) (hj : j < tr.length) (hij : i < j)
    {a b : CanonicalSpongeState U} {x : StmtIn} {c : Vector U SpongeSize.C}
    (hgi : tr[i] = ⟨.inr (.inl a), b⟩) (hgj : tr[j] = ⟨.inl x, c⟩)
    (hcap : a.capacitySegment = c) :
    E tr := by
  have hh : capacitySegmentDupHash (StmtIn := StmtIn) (U := U) tr := by
    unfold capacitySegmentDupHash
    rw [removeRedundantEntryDS_eq_self tr hNR]
    exact ⟨⟨j, hj⟩, c, x, hgj, ⟨i, hi⟩, hij, x,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hgi, hcap⟩)))⟩
  exact Or.inl (Or.inl hh)

/-- Directional: a forward-permutation **query** capacity occurring no later than a
forward-permutation **answer** with the same capacity forces `E` (`E_p` disjunct 4; this is
the out-of-order permutation configuration of CO25 Eq. 42). -/
lemma E_of_fwdQuery_le_fwdAns (hNR : tr.NoRedundantEntryDS) {i j : ℕ}
    (hi : i < tr.length) (hj : j < tr.length) (hij : i ≤ j)
    {a b a' b' : CanonicalSpongeState U}
    (hgi : tr[i] = ⟨.inr (.inl a), b⟩) (hgj : tr[j] = ⟨.inr (.inl a'), b'⟩)
    (hcap : a.capacitySegment = b'.capacitySegment) :
    E tr := by
  have hp : capacitySegmentDupPerm (StmtIn := StmtIn) (U := U) tr := by
    unfold capacitySegmentDupPerm
    rw [removeRedundantEntryDS_eq_self tr hNR]
    exact ⟨⟨j, hj⟩, b'.capacitySegment, ⟨a', b', hgj, rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨i, hi⟩, hij, a, b, hgi, hcap⟩)))⟩
  exact Or.inl (Or.inr (Or.inl hp))

end CoverageBricks

/-! ## CO25 Lemma 5.12 core: inverse-anchored chain links force `E`

Induction on the lowest inverse-anchored link of a backtracking sequence. Link `0`'s
inverse **answer** is `inputState[0]`, whose capacity is the hash anchor's answer capacity
(order-free collision). Link `ι+1`'s inverse answer is `inputState[ι+1]`, whose capacity is
link `ι`'s **answer** capacity by chain condition (d); link `ι` is forward-anchored
(else recurse), so the pair is again an order-free answer/answer collision. -/

theorem E_of_bwd_chain_entry
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) {state : CanonicalSpongeState U}
    (hNR : tr.NoRedundantEntryDS)
    (seq : BacktrackSequence tr state) :
    ∀ (ι : ℕ) (hι : ι < seq.outputState.length),
      (⟨.inr (.inr seq.outputState[ι]),
        seq.inputState[ι]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega)⟩ :
        duplexSpongeTraceEntry) ∈ tr →
      E tr := by
  intro ι
  induction ι using Nat.strong_induction_on with
  | _ ι ih =>
    intro hι hmem
    cases ι with
    | zero =>
        -- the inverse answer capacity is the hash anchor capacity (CO25 Def. 5.3 (b))
        exact E_of_hashAns_bwdAns tr hNR seq.hash_in_trace hmem rfl
    | succ ι' =>
        have hι' : ι' < seq.outputState.length := by omega
        rcases seq.permute_or_inv_in_trace ⟨ι', hι'⟩ with hfwd | hbwd
        · -- link ι' forward-anchored: forward answer vs inverse answer capacities collide
          exact E_of_fwdAns_bwdAns tr hNR hfwd hmem
            (seq.capacitySegment_output_eq_input ⟨ι', hι'⟩)
        · -- link ι' also inverse-anchored: recurse
          exact ih ι' (Nat.lt_succ_self ι') hι' hbwd

/-! ## First-occurrence index extraction from `BacktrackSequence.Index` (CO25 Def. 5.4) -/

open private firstOccurrenceIndex firstOccurrenceOfEither from
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack

section IndexSpec

variable (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  (state : CanonicalSpongeState U)

/-- `firstOccurrenceIndex` points at an occurrence of the sought entry. -/
private lemma firstOccurrenceIndex_getElem (e : duplexSpongeTraceEntry) (he : e ∈ tr) :
    tr[(firstOccurrenceIndex tr e he).val]'((firstOccurrenceIndex tr e he).isLt) = e := by
  classical
  unfold firstOccurrenceIndex
  dsimp only
  have w : tr.findIdx (fun x => decide (x = e)) < tr.length :=
    List.findIdx_lt_length_of_exists ⟨e, he, by simp⟩
  have hsat : (fun x => decide (x = e))
      (tr[tr.findIdx (fun x => decide (x = e))]'w) = true :=
    List.findIdx_getElem (w := w)
  simpa using hsat

/-- `firstOccurrenceOfEither` points at an occurrence of one of the two sought entries. -/
private lemma firstOccurrenceOfEither_getElem (eA eB : duplexSpongeTraceEntry)
    (h : eA ∈ tr ∨ eB ∈ tr) :
    tr[(firstOccurrenceOfEither tr eA eB h).val]'((firstOccurrenceOfEither tr eA eB h).isLt)
        = eA ∨
      tr[(firstOccurrenceOfEither tr eA eB h).val]'((firstOccurrenceOfEither tr eA eB h).isLt)
        = eB := by
  classical
  unfold firstOccurrenceOfEither
  dsimp only
  have w : tr.findIdx (fun x => decide (x = eA ∨ x = eB)) < tr.length := by
    refine List.findIdx_lt_length_of_exists ?_
    rcases h with h | h
    · exact ⟨eA, h, by simp⟩
    · exact ⟨eB, h, by simp⟩
  have hsat : (fun x => decide (x = eA ∨ x = eB))
      (tr[tr.findIdx (fun x => decide (x = eA ∨ x = eB))]'w) = true :=
    List.findIdx_getElem (w := w)
  simpa using hsat

/-- The first component of `BacktrackSequence.Index` points at the (first occurrence of
the) anchoring hash entry. -/
private lemma index_fst_spec (seq : BacktrackSequence tr state) :
    ∃ hlt : (BacktrackSequence.Index tr state seq).1.val < tr.length,
      tr[(BacktrackSequence.Index tr state seq).1.val]'hlt =
        ⟨.inl seq.stmt,
          Vector.drop (seq.inputState[0]'(by
            have := seq.inputState_length_eq_outputState_length_succ; omega))
            SpongeSize.R⟩ := by
  classical
  have hval : (BacktrackSequence.Index tr state seq).1
      = firstOccurrenceIndex tr
          ⟨.inl seq.stmt,
            Vector.drop (seq.inputState[0]'(by
              have := seq.inputState_length_eq_outputState_length_succ; omega))
              SpongeSize.R⟩
          seq.hash_in_trace := by
    unfold BacktrackSequence.Index
    dsimp only
  rw [hval]
  exact ⟨Fin.isLt _, firstOccurrenceIndex_getElem tr _ seq.hash_in_trace⟩

/-- For a chain-link index `i < |outputState|`, the second component of
`BacktrackSequence.Index` points at a trace entry that is either the forward or the inverse
permutation entry of link `i`. -/
private lemma index_snd_spec (seq : BacktrackSequence tr state)
    {i : ℕ} (hi : i < seq.outputState.length) (hfin : i < seq.inputState.length) :
    ∃ hlt : ((BacktrackSequence.Index tr state seq).2 ⟨i, hfin⟩).val < tr.length,
      (tr[((BacktrackSequence.Index tr state seq).2 ⟨i, hfin⟩).val]'hlt =
        ⟨.inr (.inl (seq.inputState[i]'hfin)), seq.outputState[i]'hi⟩ ∨
      tr[((BacktrackSequence.Index tr state seq).2 ⟨i, hfin⟩).val]'hlt =
        ⟨.inr (.inr (seq.outputState[i]'hi)), seq.inputState[i]'hfin⟩) := by
  classical
  have hor := seq.permute_or_inv_in_trace ⟨i, hi⟩
  have hval : ((BacktrackSequence.Index tr state seq).2 ⟨i, hfin⟩).val
      = (firstOccurrenceOfEither tr
          ⟨.inr (.inl (seq.inputState[i]'hfin)), seq.outputState[i]'hi⟩
          ⟨.inr (.inr (seq.outputState[i]'hi)), seq.inputState[i]'hfin⟩
          hor).val := by
    unfold BacktrackSequence.Index
    dsimp only
    rw [dif_pos hi]
    rfl
  rw [hval]
  exact ⟨Fin.isLt _, firstOccurrenceOfEither_getElem tr _ _ hor⟩

/-- Past the last chain link, the second component of `BacktrackSequence.Index` is the
sentinel `trace.length`. -/
private lemma index_snd_val_of_last (seq : BacktrackSequence tr state)
    {i : ℕ} (hfin : i < seq.inputState.length) (hi : ¬ i < seq.outputState.length) :
    ((BacktrackSequence.Index tr state seq).2 ⟨i, hfin⟩).val = tr.length := by
  unfold BacktrackSequence.Index
  dsimp only
  rw [dif_neg hi]

end IndexSpec

/-! ## CO25 Lemma 5.12, honest form, redundancy-free traces -/

/-- **CO25 Lemma 5.12** (honest form, redundancy-free trace): off the combined collision
event `E`, no chain link of any backtracking sequence in `S_BT(tr, s)` is anchored by an
inverse-permutation entry. -/
theorem lemma5_12Honest_of_noRedundant
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)
    (S : Backtrack.S_BT tr state) (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr) :
    ¬ E_inv_honest tr state S := by
  classical
  rintro ⟨p, hp, ιx, s_out, s_in, hidx⟩
  simp only [Backtrack.J_BT, Finset.mem_image] at hp
  obtain ⟨seq, -, rfl⟩ := hp
  have hι : ιx.val < seq.outputState.length := ιx.isLt
  have hfin : ιx.val < seq.inputState.length := by
    have := seq.inputState_length_eq_outputState_length_succ; omega
  obtain ⟨hlt, hspec⟩ := index_snd_spec tr state seq hι hfin
  have hidx' : tr[((BacktrackSequence.Index tr state seq).2 ⟨ιx.val, hfin⟩).val]?
      = some ⟨.inr (.inr s_out), s_in⟩ := hidx
  rw [List.getElem?_eq_getElem hlt] at hidx'
  have hentry := Option.some.inj hidx'
  rcases hspec with hA | hB
  · -- the first occurrence is the forward entry: contradicts the inverse shape
    rw [hA] at hentry
    exact absurd (congrArg Sigma.fst hentry) (by simp)
  · -- the first occurrence is the inverse entry: Lemma 5.12 core fires
    have hmem : (⟨.inr (.inr (seq.outputState[ιx.val]'hι)),
        seq.inputState[ιx.val]'hfin⟩ : duplexSpongeTraceEntry) ∈ tr := by
      rw [← hB]
      exact List.getElem_mem hlt
    exact hE (E_of_bwd_chain_entry tr hNR seq ιx.val hι hmem)

/-! ## CO25 Lemma 5.14 core: backward chain uniqueness

Off `E` every chain link is forward-anchored (`E_of_bwd_chain_entry`), and forward answers
with equal capacities are unique trace entries (`fwdAns_cap_inj`). Walking two chains
backwards from the shared final state therefore identifies them link by link; a length
mismatch puts a hash answer capacity on a forward answer, and distinct statements collide
two hash answers. -/

section Uniqueness

variable (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  {state : CanonicalSpongeState U}

omit [SpongeSize] in
/-- Index-congruence helper for `List.getElem` (proof-irrelevant index rewriting). -/
private lemma getElem_idx_congr {α : Type _} {l : List α} {i j : ℕ} (hij : i = j)
    {hi : i < l.length} : l[i]'hi = l[j]'(hij ▸ hi) := by
  subst hij; rfl

/-- Off `E`, every chain link of a backtracking sequence is forward-anchored
(consequence of the Lemma 5.12 core). -/
private lemma fwd_anchor (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr)
    (seq : BacktrackSequence tr state) {ι : ℕ} (hι : ι < seq.outputState.length)
    (hfin : ι < seq.inputState.length) :
    (⟨.inr (.inl (seq.inputState[ι]'hfin)), seq.outputState[ι]'hι⟩ :
      duplexSpongeTraceEntry) ∈ tr := by
  rcases seq.permute_or_inv_in_trace ⟨ι, hι⟩ with hfwd | hbwd
  · exact hfwd
  · exact absurd (E_of_bwd_chain_entry tr hNR seq ι hι hbwd) hE

/-- Off `E`, a forward-permutation answer capacity determines the whole entry: two forward
entries with equal answer capacities are the same query/answer pair. -/
private lemma fwdAns_cap_inj (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr)
    {a b a' b' : CanonicalSpongeState U}
    (h1 : (⟨.inr (.inl a), b⟩ : duplexSpongeTraceEntry) ∈ tr)
    (h2 : (⟨.inr (.inl a'), b'⟩ : duplexSpongeTraceEntry) ∈ tr)
    (hcap : b.capacitySegment = b'.capacitySegment) :
    a = a' ∧ b = b' := by
  by_contra hne
  exact hE (E_of_fwdAns_fwdAns tr hNR h1 h2 hcap hne)

/-- Backward identification of two chains ending at the same state: `k` steps from the
end, the input states (and, for `k ≥ 1`, the output states) coincide. -/
private lemma chain_backward_eq (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr)
    (seq seq' : BacktrackSequence tr state) :
    ∀ (k : ℕ), k ≤ seq.outputState.length → k ≤ seq'.outputState.length →
      (seq.inputState[seq.outputState.length - k]'(by
            have := seq.inputState_length_eq_outputState_length_succ; omega)
          = seq'.inputState[seq'.outputState.length - k]'(by
            have := seq'.inputState_length_eq_outputState_length_succ; omega))
        ∧ (0 < k →
          ∀ (h1 : seq.outputState.length - k < seq.outputState.length)
            (h2 : seq'.outputState.length - k < seq'.outputState.length),
          seq.outputState[seq.outputState.length - k]'h1
            = seq'.outputState[seq'.outputState.length - k]'h2) := by
  intro k
  induction k with
  | zero =>
    intro hk hk'
    refine ⟨?_, fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
    have e1 : seq.inputState[seq.outputState.length - 0]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega)
        = seq.inputState[seq.inputState.length - 1]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega) :=
      getElem_idx_congr (by
        have := seq.inputState_length_eq_outputState_length_succ; omega)
    have e2 : seq'.inputState[seq'.outputState.length - 0]'(by
          have := seq'.inputState_length_eq_outputState_length_succ; omega)
        = seq'.inputState[seq'.inputState.length - 1]'(by
          have := seq'.inputState_length_eq_outputState_length_succ; omega) :=
      getElem_idx_congr (by
        have := seq'.inputState_length_eq_outputState_length_succ; omega)
    rw [e1, e2, seq.last_inputState_eq_state, seq'.last_inputState_eq_state]
  | succ k ih =>
    intro hk hk'
    obtain ⟨ihIn, -⟩ := ih (by omega) (by omega)
    have hι : seq.outputState.length - (k + 1) < seq.outputState.length := by omega
    have hι' : seq'.outputState.length - (k + 1) < seq'.outputState.length := by omega
    have hfin : seq.outputState.length - (k + 1) < seq.inputState.length := by
      have := seq.inputState_length_eq_outputState_length_succ; omega
    have hfin' : seq'.outputState.length - (k + 1) < seq'.inputState.length := by
      have := seq'.inputState_length_eq_outputState_length_succ; omega
    -- junction capacities (chain condition (d)), re-indexed to `length - k`
    have hjunc : (seq.outputState[seq.outputState.length - (k + 1)]'hι).capacitySegment
        = (seq.inputState[seq.outputState.length - k]'(by
            have := seq.inputState_length_eq_outputState_length_succ;
            omega)).capacitySegment := by
      have e : seq.inputState[(seq.outputState.length - (k + 1)) + 1]'(by
            have := seq.inputState_length_eq_outputState_length_succ; omega)
          = seq.inputState[seq.outputState.length - k]'(by
            have := seq.inputState_length_eq_outputState_length_succ; omega) :=
        getElem_idx_congr (by omega)
      rw [← e]
      exact seq.capacitySegment_output_eq_input ⟨seq.outputState.length - (k + 1), hι⟩
    have hjunc' : (seq'.outputState[seq'.outputState.length - (k + 1)]'hι').capacitySegment
        = (seq'.inputState[seq'.outputState.length - k]'(by
            have := seq'.inputState_length_eq_outputState_length_succ;
            omega)).capacitySegment := by
      have e : seq'.inputState[(seq'.outputState.length - (k + 1)) + 1]'(by
            have := seq'.inputState_length_eq_outputState_length_succ; omega)
          = seq'.inputState[seq'.outputState.length - k]'(by
            have := seq'.inputState_length_eq_outputState_length_succ; omega) :=
        getElem_idx_congr (by omega)
      rw [← e]
      exact seq'.capacitySegment_output_eq_input ⟨seq'.outputState.length - (k + 1), hι'⟩
    -- both links are forward-anchored with equal answer capacities, hence equal
    have hF := fwd_anchor tr hNR hE seq hι hfin
    have hF' := fwd_anchor tr hNR hE seq' hι' hfin'
    have hcap : (seq.outputState[seq.outputState.length - (k + 1)]'hι).capacitySegment
        = (seq'.outputState[seq'.outputState.length - (k + 1)]'hι').capacitySegment := by
      rw [hjunc, hjunc']
      exact congrArg CanonicalSpongeState.capacitySegment ihIn
    obtain ⟨hin, hout⟩ := fwdAns_cap_inj tr hNR hE hF hF' hcap
    exact ⟨hin, fun _ _ _ => hout⟩

/-- A strict length mismatch between two chains ending at the same state forces `E`:
the shorter chain's hash anchor capacity is the longer chain's interior forward answer
capacity. -/
private lemma E_of_outputState_length_lt (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr)
    (seq seq' : BacktrackSequence tr state)
    (hlt : seq.outputState.length < seq'.outputState.length) : False := by
  have hkey := (chain_backward_eq tr hNR hE seq seq' seq.outputState.length le_rfl
    (le_of_lt hlt)).1
  have hι' : seq'.outputState.length - seq.outputState.length - 1
      < seq'.outputState.length := by omega
  have hfin' : seq'.outputState.length - seq.outputState.length - 1
      < seq'.inputState.length := by
    have := seq'.inputState_length_eq_outputState_length_succ; omega
  have hanchor := fwd_anchor tr hNR hE seq' hι' hfin'
  -- the junction above the anchor is the shorter chain's initial input state
  have hjunc : (seq'.outputState[seq'.outputState.length - seq.outputState.length - 1]'
        hι').capacitySegment
      = (seq.inputState[0]'(by
          have := seq.inputState_length_eq_outputState_length_succ;
          omega)).capacitySegment := by
    have e : seq'.inputState[(seq'.outputState.length - seq.outputState.length - 1) + 1]'(by
          have := seq'.inputState_length_eq_outputState_length_succ; omega)
        = seq'.inputState[seq'.outputState.length - seq.outputState.length]'(by
          have := seq'.inputState_length_eq_outputState_length_succ; omega) :=
      getElem_idx_congr (by omega)
    have e0 : seq.inputState[seq.outputState.length - seq.outputState.length]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega)
        = seq.inputState[0]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega) :=
      getElem_idx_congr (by omega)
    have h := seq'.capacitySegment_output_eq_input
      ⟨seq'.outputState.length - seq.outputState.length - 1, hι'⟩
    rw [e0] at hkey
    rw [← hkey] at e
    rw [← e]
    exact h
  exact hE (E_of_hashAns_fwdAns tr hNR seq.hash_in_trace hanchor hjunc)

/-- **CO25 Lemma 5.14 core** (redundancy-free trace): off `E`, any two backtracking
sequences ending at the same state are equal. -/
theorem backtrackSequence_unique (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr)
    (seq seq' : BacktrackSequence tr state) : seq = seq' := by
  -- equal chain lengths
  have hm : seq.outputState.length = seq'.outputState.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact E_of_outputState_length_lt tr hNR hE seq seq' hlt
    · exact E_of_outputState_length_lt tr hNR hE seq' seq hlt
  have hlenIn : seq.inputState.length = seq'.inputState.length := by
    have := seq.inputState_length_eq_outputState_length_succ
    have := seq'.inputState_length_eq_outputState_length_succ
    omega
  -- equal input chains
  have hin : seq.inputState = seq'.inputState := by
    refine List.ext_getElem hlenIn ?_
    intro i h1 h2
    have hkey := (chain_backward_eq tr hNR hE seq seq' (seq.outputState.length - i)
      (by omega) (by omega)).1
    have e1 : seq.inputState[seq.outputState.length
          - (seq.outputState.length - i)]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega)
        = seq.inputState[i]'h1 :=
      getElem_idx_congr (by
        have := seq.inputState_length_eq_outputState_length_succ; omega)
    have e2 : seq'.inputState[seq'.outputState.length
          - (seq.outputState.length - i)]'(by
          have := seq'.inputState_length_eq_outputState_length_succ; omega)
        = seq'.inputState[i]'h2 :=
      getElem_idx_congr (by
        have := seq'.inputState_length_eq_outputState_length_succ; omega)
    rw [e1, e2] at hkey
    exact hkey
  -- equal output chains
  have hout : seq.outputState = seq'.outputState := by
    refine List.ext_getElem hm ?_
    intro i h1 h2
    have hkey := (chain_backward_eq tr hNR hE seq seq' (seq.outputState.length - i)
      (by omega) (by omega)).2 (by omega)
    have e1 : seq.outputState.length - (seq.outputState.length - i) = i := by omega
    have e2 : seq'.outputState.length - (seq.outputState.length - i) = i := by omega
    have hkey' := hkey (by omega) (by omega)
    rw [getElem_idx_congr (l := seq.outputState) e1,
      getElem_idx_congr (l := seq'.outputState) e2] at hkey'
    exact hkey'
  -- equal statements (hash answer capacities coincide)
  have hstmt : seq.stmt = seq'.stmt := by
    by_contra hne
    have hkey := (chain_backward_eq tr hNR hE seq seq' seq.outputState.length le_rfl
      (by omega)).1
    have e1 : seq.inputState[seq.outputState.length - seq.outputState.length]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega)
        = seq.inputState[0]'(by
          have := seq.inputState_length_eq_outputState_length_succ; omega) :=
      getElem_idx_congr (by omega)
    have e2 : seq'.inputState[seq'.outputState.length - seq.outputState.length]'(by
          have := seq'.inputState_length_eq_outputState_length_succ; omega)
        = seq'.inputState[0]'(by
          have := seq'.inputState_length_eq_outputState_length_succ; omega) :=
      getElem_idx_congr (by omega)
    rw [e1, e2] at hkey
    have h' := seq'.hash_in_trace
    have hcast : (⟨.inl seq'.stmt,
          Vector.drop (seq'.inputState[0]'(by
            have := seq'.inputState_length_eq_outputState_length_succ; omega))
            SpongeSize.R⟩ : duplexSpongeTraceEntry)
        = ⟨.inl seq'.stmt,
          Vector.drop (seq.inputState[0]'(by
            have := seq.inputState_length_eq_outputState_length_succ; omega))
            SpongeSize.R⟩ := by
      rw [← hkey]
    rw [hcast] at h'
    exact hE (E_of_hashAns_hashAns tr hNR seq.hash_in_trace h' hne)
  -- assemble
  obtain ⟨a, b, c, p1, p2, p3, p4, p5, p6⟩ := seq
  obtain ⟨a', b', c', q1, q2, q3, q4, q5, q6⟩ := seq'
  obtain rfl : a = a' := hstmt
  obtain rfl : b = b' := hin
  obtain rfl : c = c' := hout
  rfl

end Uniqueness

/-- **CO25 Lemma 5.14** (honest form, redundancy-free trace): off `E`, the backtracking
family `S_BT(tr, s)` has at most one maximal sequence. -/
theorem lemma5_14Honest_of_noRedundant
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)
    (S : Backtrack.S_BT tr state) (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr) :
    ¬ E_fork_honest tr state S := by
  intro hfork
  obtain ⟨s, _, s', _, hne⟩ := Finset.one_lt_card.mp hfork
  exact hne (backtrackSequence_unique tr hNR hE s s')

/-! ## CO25 Lemma 5.16, honest form, redundancy-free traces -/

/-- **CO25 Lemma 5.16** (honest form, redundancy-free trace): off `E`, all chain queries
of every `S_BT` sequence appear in trace order — the anchoring hash query precedes the
first chain permutation query (Eq. 41), and each chain permutation query precedes its
successor (Eq. 42). -/
theorem lemma5_16Honest_of_noRedundant
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)
    (S : Backtrack.S_BT tr state) (hNR : tr.NoRedundantEntryDS) (hE : ¬ E tr) :
    ¬ E_time_honest tr state S := by
  classical
  intro htime
  have htime' : E_time_h_honest tr state S ∨ E_time_p_honest tr state S := htime
  rcases htime' with htime | htime
  · -- Eq. 41: out-of-order hash
    obtain ⟨p, hp, hgt⟩ := htime
    simp only [Backtrack.J_BT, Finset.mem_image] at hp
    obtain ⟨seq, -, rfl⟩ := hp
    have hfin0 : 0 < seq.inputState.length := by
      have := seq.inputState_length_eq_outputState_length_succ; omega
    by_cases h0 : 0 < seq.outputState.length
    · obtain ⟨hlt2, hspec2⟩ := index_snd_spec tr state seq h0 hfin0
      obtain ⟨hlt1, hspec1⟩ := index_fst_spec tr state seq
      have hgt' : (BacktrackSequence.Index tr state seq).1.val
          > ((BacktrackSequence.Index tr state seq).2 ⟨0, hfin0⟩).val := hgt
      rcases hspec2 with hA | hB
      · -- forward link-0 query strictly before the hash answer: `E_h` disjunct 4
        exact hE (E_of_fwdQuery_before_hashAns tr hNR hlt2 hlt1 hgt' hA hspec1 rfl)
      · -- inverse anchor: Lemma 5.12 core
        have hmem : (⟨.inr (.inr (seq.outputState[0]'h0)),
            seq.inputState[0]'hfin0⟩ : duplexSpongeTraceEntry) ∈ tr := by
          rw [← hB]; exact List.getElem_mem hlt2
        exact hE (E_of_bwd_chain_entry tr hNR seq 0 h0 hmem)
    · -- no chain links: the sentinel index `tr.length` cannot be exceeded
      have hval := index_snd_val_of_last tr state seq hfin0 h0
      have hlt1 : (BacktrackSequence.Index tr state seq).1.val < tr.length :=
        Fin.isLt _
      have hgt' : (BacktrackSequence.Index tr state seq).1.val
          > ((BacktrackSequence.Index tr state seq).2 ⟨0, hfin0⟩).val := hgt
      omega
  · -- Eq. 42: out-of-order permutation
    obtain ⟨p, hp, ιx, hgt⟩ := htime
    simp only [Backtrack.J_BT, Finset.mem_image] at hp
    obtain ⟨seq, -, rfl⟩ := hp
    have hι : ιx.val < seq.outputState.length := ιx.isLt
    have hfin : ιx.val < seq.inputState.length := by
      have := seq.inputState_length_eq_outputState_length_succ; omega
    have hfin1 : ιx.val + 1 < seq.inputState.length := by
      have := seq.inputState_length_eq_outputState_length_succ; omega
    obtain ⟨hlt1, hspec1⟩ := index_snd_spec tr state seq hι hfin
    by_cases h1 : ιx.val + 1 < seq.outputState.length
    · obtain ⟨hlt2, hspec2⟩ := index_snd_spec tr state seq h1 hfin1
      have hgt' : ((BacktrackSequence.Index tr state seq).2 ⟨ιx.val, hfin⟩).val
          > ((BacktrackSequence.Index tr state seq).2 ⟨ιx.val + 1, hfin1⟩).val := hgt
      rcases hspec1 with hA1 | hB1
      · rcases hspec2 with hA2 | hB2
        · -- both forward: link `ιx+1`'s query capacity is link `ιx`'s answer capacity
          -- (chain condition (d)), and it occurs strictly earlier: `E_p` disjunct 4
          have hcap : (seq.inputState[ιx.val + 1]'hfin1).capacitySegment
              = (seq.outputState[ιx.val]'hι).capacitySegment :=
            (seq.capacitySegment_output_eq_input ⟨ιx.val, hι⟩).symm
          exact hE (E_of_fwdQuery_le_fwdAns tr hNR hlt2 hlt1 (le_of_lt hgt')
            hA2 hA1 hcap)
        · -- inverse anchor at link `ιx+1`: Lemma 5.12 core
          have hmem : (⟨.inr (.inr (seq.outputState[ιx.val + 1]'h1)),
              seq.inputState[ιx.val + 1]'hfin1⟩ : duplexSpongeTraceEntry) ∈ tr := by
            rw [← hB2]; exact List.getElem_mem hlt2
          exact hE (E_of_bwd_chain_entry tr hNR seq (ιx.val + 1) h1 hmem)
      · -- inverse anchor at link `ιx`: Lemma 5.12 core
        have hmem : (⟨.inr (.inr (seq.outputState[ιx.val]'hι)),
            seq.inputState[ιx.val]'hfin⟩ : duplexSpongeTraceEntry) ∈ tr := by
          rw [← hB1]; exact List.getElem_mem hlt1
        exact hE (E_of_bwd_chain_entry tr hNR seq ιx.val hι hmem)
    · -- sentinel: nothing exceeds `tr.length`
      have hval := index_snd_val_of_last tr state seq hfin1 h1
      have hub := ((BacktrackSequence.Index tr state seq).2 ⟨ιx.val, hfin⟩).isLt
      have hgt' : ((BacktrackSequence.Index tr state seq).2 ⟨ιx.val, hfin⟩).val
          > ((BacktrackSequence.Index tr state seq).2 ⟨ιx.val + 1, hfin1⟩).val := hgt
      omega

/-! ## Finest residual split of the original M2 residual surfaces

The KeyLemmaFoundations residuals `Lemma5_1*HonestResidual` quantify over **all** raw
traces, while `E` reads the *deduplicated* trace (`removeRedundantEntryDS`). The two
surfaces genuinely diverge on redundant traces, so the finest honest split is:
the redundancy-free core (proven above, the CO25 content) plus the named redundant-trace
corner residuals below, with proven case-split reductions. -/

/-- M2a-finest — the redundant-trace corner of CO25 Lemma 5.12 (honest form).

**FALSITY WARNING — this corner is FALSE (machine-checked); do not attempt to prove it.**
See `lemma5_12HonestRedundantResidual_not_universal` below: for the raw trace
`tr = [⟨h x, c⟩, ⟨p⁻¹ i₀, o₀⟩, ⟨p⁻¹ o₀, i₀⟩]` (with `cap i₀ = c ≠ cap o₀`) the third
entry is redundant — its query/answer swap precedes it, `redundantEntryDS`'s
inverse-direction clause — so `removeRedundantEntryDS` erases exactly it; on the remaining
two entries no `E_h`/`E_p`/`E_pinv`/`E_func` disjunct fires (the only shared capacity `c`
sits on a hash **answer** and an inverse **query**, in the uncovered order), so `¬E tr`.
Yet the raw trace still contains the inverse anchor `⟨p⁻¹ o₀, i₀⟩` for the one-link
sequence `x; [i₀, s]; [o₀]`, whose first-occurrence index witnesses `E_inv_honest`.
Consequently the original `Lemma5_12HonestResidual` (which quantifies over redundant raw
traces) is itself false as stated (`lemma5_12HonestResidual_not_universal`); the honest
repair is to state Lemma 5.12 for deduplicated traces, i.e.
`lemma5_12Honest_of_noRedundant` above. -/
def Lemma5_12HonestRedundantResidual (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ tr.NoRedundantEntryDS → ¬ E tr → ¬ E_inv_honest tr state S

/-- M2b-finest — the redundant-trace corner of CO25 Lemma 5.14 (honest form): raw-trace
chain anchors can be hidden from `E` by dedup orientation swaps, so the fork analysis on
redundant raw traces needs an order-preserving dedup transport (open; plausibly true, since
every swap turns the relevant query capacity into an answer capacity, but the transport
bookkeeping is genuinely finer than the §5.6 disjuncts). -/
def Lemma5_14HonestRedundantResidual (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ tr.NoRedundantEntryDS → ¬ E tr → ¬ E_fork_honest tr state S

/-- M2c-finest — the redundant-trace corner of CO25 Lemma 5.16 (honest form): raw-trace
first-occurrence indices vs. dedup'd-trace events (open; same transport obstruction as
`Lemma5_14HonestRedundantResidual`). -/
def Lemma5_16HonestRedundantResidual (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ tr.NoRedundantEntryDS → ¬ E tr → ¬ E_time_honest tr state S

variable (StmtIn) (U)

/-- Proven reduction: the original M2a residual surface follows from its (false!)
redundant-trace corner — the redundancy-free part is `lemma5_12Honest_of_noRedundant`.
Recorded for shape-compatibility with the KeyLemmaFoundations residual census; by the
machine-checked `lemma5_12HonestRedundantResidual_not_universal` the antecedent is not
universally satisfiable, and downstream consumers should migrate to the redundancy-free
core. -/
theorem lemma5_12HonestResidual_of_redundantResidual
    (h : Lemma5_12HonestRedundantResidual StmtIn U) :
    Lemma5_12HonestResidual StmtIn U := by
  intro tr state S hE
  by_cases hNR : tr.NoRedundantEntryDS
  · exact lemma5_12Honest_of_noRedundant tr state S hNR hE
  · exact h tr state S hNR hE

/-- Proven reduction: the original M2b residual surface splits into the proven
redundancy-free core plus the redundant-trace corner. -/
theorem lemma5_14HonestResidual_of_redundantResidual
    (h : Lemma5_14HonestRedundantResidual StmtIn U) :
    Lemma5_14HonestResidual StmtIn U := by
  intro tr state S hE
  by_cases hNR : tr.NoRedundantEntryDS
  · exact lemma5_14Honest_of_noRedundant tr state S hNR hE
  · exact h tr state S hNR hE

/-- Proven reduction: the original M2c residual surface splits into the proven
redundancy-free core plus the redundant-trace corner. -/
theorem lemma5_16HonestResidual_of_redundantResidual
    (h : Lemma5_16HonestRedundantResidual StmtIn U) :
    Lemma5_16HonestResidual StmtIn U := by
  intro tr state S hE
  by_cases hNR : tr.NoRedundantEntryDS
  · exact lemma5_16Honest_of_noRedundant tr state S hNR hE
  · exact h tr state S hNR hE

end DuplexSpongeFS.BacktrackLemmas

namespace DuplexSpongeFS.BacktrackLemmas

/-! ### Machine-checked falsity of the 5.12 redundant-trace corner

A concrete counterexample with `StmtIn := Unit`, `U := UInt8` and sponge geometry
`N = 2, R = 1, C = 1`. The raw trace is
`[⟨h (), [1]⟩, ⟨p⁻¹ [0,1], [0,2]⟩, ⟨p⁻¹ [0,2], [0,1]⟩]`:
the third entry (the chain's inverse anchor) is redundant — its query/answer swap precedes
it — so dedup erases exactly it, and on the surviving two entries no `E` disjunct fires
(the only shared capacity `[1]` sits on a hash **answer** and an inverse **query**, with
the hash first — the one orientation none of the `E_h`/`E_p`/`E_pinv` triggers cover).
The raw trace still anchors the one-link backtracking sequence
`(); [[0,1], [1,2]]; [[0,2]]` through the inverse entry, witnessing `E_inv_honest`.

(This section sits outside the namespace-level `variable [SpongeSize]` scope so that the
concrete `szCE` geometry is the instance in effect.) -/

section Counterexample

/-- Width-2, rate-1 sponge geometry for the counterexample (`C = 1`). -/
@[reducible] private def szCE : SpongeSize := ⟨2, 1, by omega⟩

attribute [local instance] szCE

/-- `s_in` of the chain link; capacity `[1]`. -/
private def iCE : CanonicalSpongeState UInt8 := #v[(0 : UInt8), (1 : UInt8)]

/-- `s_out` of the chain link; capacity `[2]`. -/
private def oCE : CanonicalSpongeState UInt8 := #v[(0 : UInt8), (2 : UInt8)]

/-- The target state; shares `oCE`'s capacity `[2]`. -/
private def sCE : CanonicalSpongeState UInt8 := #v[(1 : UInt8), (2 : UInt8)]

/-- Hash anchor entry `(h, (), cap(iCE)) = (h, (), [1])`. -/
private def hashCE : duplexSpongeTraceEntry (StartType := Unit) (U := UInt8) :=
  ⟨.inl (), iCE.capacitySegment⟩

/-- Orientation-swapped inverse entry `(p⁻¹, iCE, oCE)` (the dedup survivor). -/
private def bwd1CE : duplexSpongeTraceEntry (StartType := Unit) (U := UInt8) :=
  ⟨.inr (.inr iCE), oCE⟩

/-- The chain's true inverse anchor `(p⁻¹, oCE, iCE)` (erased by dedup). -/
private def bwd2CE : duplexSpongeTraceEntry (StartType := Unit) (U := UInt8) :=
  ⟨.inr (.inr oCE), iCE⟩

/-- The counterexample raw trace. -/
private def trCE : QueryLog (duplexSpongeChallengeOracle Unit UInt8) :=
  [hashCE, bwd1CE, bwd2CE]

/-- The deduplicated counterexample trace (`bwd2CE` erased). -/
private def baseCE : QueryLog (duplexSpongeChallengeOracle Unit UInt8) :=
  [hashCE, bwd1CE]

/-- The one-link backtracking sequence anchored by `bwd2CE` over the raw trace. -/
private def seqCE : BacktrackSequence trCE sCE where
  stmt := ()
  inputState := [iCE, sCE]
  outputState := [oCE]
  inputState_length_eq_outputState_length_succ := rfl
  last_inputState_eq_state := rfl
  hash_in_trace := .head _
  permute_or_inv_in_trace := by
    intro i
    obtain ⟨iv, hiv⟩ := i
    simp only [List.length_cons, List.length_nil] at hiv
    interval_cases iv
    exact Or.inr (.tail _ (.tail _ (.head _)))
  capacitySegment_output_eq_input := by
    intro i
    obtain ⟨iv, hiv⟩ := i
    simp only [List.length_cons, List.length_nil] at hiv
    interval_cases iv
    exact (show oCE.capacitySegment = sCE.capacitySegment by decide)
  capacitySegment_input_ne_output := by
    intro i
    obtain ⟨iv, hiv⟩ := i
    simp only [List.length_cons, List.length_nil] at hiv
    interval_cases iv
    exact (show iCE.capacitySegment ≠ oCE.capacitySegment by decide)

/-- The singleton backtracking family `{seqCE}`. -/
private def SCE : Backtrack.S_BT trCE sCE where
  seqFamily := {seqCE}
  maximality := by
    intro s hs s' hs' hne
    rw [Finset.mem_singleton] at hs hs'
    subst hs; subst hs'
    exact absurd rfl hne

/-- The raw counterexample trace has a redundant entry (`bwd2CE`, justified by its
orientation swap `bwd1CE`). -/
private lemma trCE_not_noRedundant : ¬ trCE.NoRedundantEntryDS := by
  intro h
  refine h ⟨2, by decide⟩ ?_
  exact ⟨⟨1, by decide⟩, by decide, Or.inr rfl⟩

/-- Only `bwd2CE` is redundant in the raw counterexample trace. -/
private lemma trCE_redundant_unique (idx : Fin trCE.length)
    (h : trCE.redundantEntryDS idx) : idx = ⟨2, by decide⟩ := by
  obtain ⟨iv, hiv⟩ := idx
  have hiv' : iv < 3 := hiv
  interval_cases iv
  · obtain ⟨j', hj', -⟩ :=
      (h : ∃ j' : Fin trCE.length, j' < ⟨0, hiv⟩ ∧ trCE[j'] = hashCE)
    exact absurd (hj' : j'.val < 0) (Nat.not_lt_zero _)
  · obtain ⟨j', hj', hdis⟩ :=
      (h : ∃ j' : Fin trCE.length, j' < ⟨1, hiv⟩ ∧
        (trCE[j'] = bwd1CE ∨ trCE[j'] = ⟨.inr (.inr oCE), iCE⟩))
    obtain ⟨jv, hjv⟩ := j'
    have hjv1 : jv < 1 := hj'
    have hjv0 : jv = 0 := by omega
    subst hjv0
    rcases hdis with hd | hd
    · exact absurd (congrArg Sigma.fst hd) (by simp [trCE, hashCE, bwd1CE])
    · exact absurd (congrArg Sigma.fst hd) (by simp [trCE, hashCE])
  · rfl

/-- The deduplicated counterexample trace is redundancy-free. -/
private lemma baseCE_noRedundant : baseCE.NoRedundantEntryDS := by
  intro idx h
  obtain ⟨iv, hiv⟩ := idx
  have hiv' : iv < 2 := hiv
  interval_cases iv
  · obtain ⟨j', hj', -⟩ :=
      (h : ∃ j' : Fin baseCE.length, j' < ⟨0, hiv⟩ ∧ baseCE[j'] = hashCE)
    exact absurd (hj' : j'.val < 0) (Nat.not_lt_zero _)
  · obtain ⟨j', hj', hdis⟩ :=
      (h : ∃ j' : Fin baseCE.length, j' < ⟨1, hiv⟩ ∧
        (baseCE[j'] = bwd1CE ∨ baseCE[j'] = ⟨.inr (.inr oCE), iCE⟩))
    obtain ⟨jv, hjv⟩ := j'
    have hjv1 : jv < 1 := hj'
    have hjv0 : jv = 0 := by omega
    subst hjv0
    rcases hdis with hd | hd
    · exact absurd (congrArg Sigma.fst hd) (by simp [baseCE, hashCE, bwd1CE])
    · exact absurd (congrArg Sigma.fst hd) (by simp [baseCE, hashCE])

/-- Dedup of the raw counterexample trace erases exactly `bwd2CE`. -/
private lemma removeRedundant_trCE :
    removeRedundantEntryDS trCE = ⟨baseCE, baseCE_noRedundant⟩ := by
  have hex : ∃ idx : Fin trCE.length, trCE.redundantEntryDS idx :=
    ⟨⟨2, by decide⟩, ⟨⟨1, by decide⟩, by decide, Or.inr rfl⟩⟩
  rw [removeRedundantEntryDS, dif_pos hex]
  have hch : Classical.choose hex = ⟨2, by decide⟩ :=
    trCE_redundant_unique _ (Classical.choose_spec hex)
  rw [hch]
  have herase : trCE.eraseIdx ((⟨2, by decide⟩ : Fin trCE.length) : ℕ) = baseCE := rfl
  rw [herase]
  exact removeRedundantEntryDS_eq_self baseCE baseCE_noRedundant

/-- The combined collision event does not fire on the counterexample trace: dedup hides
the inverse anchor, and the surviving hash-answer/inverse-query capacity pair is in the
orientation none of the `E` disjuncts cover. -/
private lemma trCE_not_E : ¬ E trCE := by
  intro hE
  have hE' : capacitySegmentDup trCE ∨ notFunction trCE := hE
  rcases hE' with hdup | hfunc
  · have hdup' : capacitySegmentDupHash trCE ∨ capacitySegmentDupPerm trCE
        ∨ capacitySegmentDupPermInv trCE := hdup
    rcases hdup' with hh | hp | hpinv
    · -- `E_h`: the only hash entry is first, nothing precedes it
      unfold capacitySegmentDupHash at hh
      rw [removeRedundant_trCE] at hh
      obtain ⟨⟨jv, hjv⟩, capSeg, stmt, htrig, ⟨j'v, hj'v⟩, hlt, stmt', -⟩ := hh
      have hjv' : jv < 2 := hjv
      interval_cases jv
      · exact absurd (hlt : j'v < 0) (Nat.not_lt_zero _)
      · simp [baseCE, bwd1CE] at htrig
    · -- `E_p`: no forward entries exist
      unfold capacitySegmentDupPerm at hp
      rw [removeRedundant_trCE] at hp
      obtain ⟨⟨jv, hjv⟩, capSeg, ⟨sIn, sOut, htrig, -⟩, -⟩ := hp
      have hjv' : jv < 2 := hjv
      interval_cases jv
      · simp [baseCE, hashCE] at htrig
      · simp [baseCE, bwd1CE] at htrig
    · -- `E_pinv`: trigger is `bwd1CE`'s answer capacity `[2]`; every disjunct fails
      unfold capacitySegmentDupPermInv at hpinv
      rw [removeRedundant_trCE] at hpinv
      obtain ⟨⟨jv, hjv⟩, capSeg, ⟨sOut, sIn, htrig, hcap⟩, hdisj⟩ := hpinv
      have hjv' : jv < 2 := hjv
      interval_cases jv
      · simp [baseCE, hashCE] at htrig
      · -- trigger at `bwd1CE`: `sOut = iCE`, `sIn = oCE`, `capSeg = cap oCE = [2]`
        have htrig' : bwd1CE = ⟨.inr (.inr sOut), sIn⟩ := htrig
        have hSout : sOut = iCE := by
          have := congrArg Sigma.fst htrig'
          simpa [bwd1CE] using this.symm
        subst hSout
        have hSin : sIn = oCE := by
          have : (⟨.inr (.inr iCE), oCE⟩ : duplexSpongeTraceEntry) = ⟨.inr (.inr iCE), sIn⟩ :=
            htrig'
          simpa [Sigma.mk.injEq] using this.symm
        subst hSin
        subst hcap
        rcases hdisj with ⟨⟨j'v, hj'v⟩, hlt, stmt', hd⟩
          | ⟨⟨j'v, hj'v⟩, hlt, sIn1, sOut1, hd, -⟩
          | ⟨⟨j'v, hj'v⟩, hlt, sIn2, sOut2, hd, hc⟩
          | ⟨⟨j'v, hj'v⟩, hle, sIn3, sOut3, hd, -⟩
          | ⟨⟨j'v, hj'v⟩, hle, sOut4, sIn4, hd, hc⟩
        · -- earlier hash with capacity `[2]`: but the hash answer is `[1]`
          have hj0 : j'v = 0 := by have : j'v < 1 := hlt; omega
          subst hj0
          have hd' : hashCE = ⟨.inl stmt', oCE.capacitySegment⟩ := hd
          have : iCE.capacitySegment = oCE.capacitySegment := by
            simpa [hashCE, Sigma.mk.injEq] using hd'
          exact absurd this (by decide)
        · -- earlier forward answer: no forward entries
          have hj0 : j'v = 0 := by have : j'v < 1 := hlt; omega
          subst hj0
          simp [baseCE, hashCE] at hd
        · -- earlier inverse answer: only the hash precedes
          have hj0 : j'v = 0 := by have : j'v < 1 := hlt; omega
          subst hj0
          simp [baseCE, hashCE] at hd
        · -- forward query at `≤`: no forward entries
          have hj1 : j'v < 2 := hj'v
          interval_cases j'v
          · simp [baseCE, hashCE] at hd
          · simp [baseCE, bwd1CE] at hd
        · -- inverse query at `≤` with capacity `[2]`: `bwd1CE`'s query capacity is `[1]`
          have hj1 : j'v < 2 := hj'v
          interval_cases j'v
          · simp [baseCE, hashCE] at hd
          · -- here `sIn4` is the entry's query (the def binds answer-then-query)
            have hd' : bwd1CE = ⟨.inr (.inr sIn4), sOut4⟩ := hd
            have hq : sIn4 = iCE := by
              have := congrArg Sigma.fst hd'
              simpa [bwd1CE] using this.symm
            subst hq
            exact absurd hc (by decide)
  · -- `E_func`: no forward entries exist
    unfold notFunction at hfunc
    rw [removeRedundant_trCE] at hfunc
    obtain ⟨⟨jv, hjv⟩, sIn, sOut, htrig, -⟩ := hfunc
    have hjv' : jv < 2 := hjv
    interval_cases jv
    · simp [baseCE, hashCE] at htrig
    · simp [baseCE, bwd1CE] at htrig

/-- The honest inverse-anchor event fires on the raw counterexample trace. -/
private lemma trCE_E_inv : E_inv_honest trCE sCE SCE := by
  classical
  have h0 : (0 : ℕ) < seqCE.outputState.length := by decide
  have hfin : (0 : ℕ) < seqCE.inputState.length := by decide
  obtain ⟨hlt, hspec⟩ := index_snd_spec trCE sCE seqCE h0 hfin
  have hspec' : trCE[((BacktrackSequence.Index trCE sCE seqCE).2 ⟨0, hfin⟩).val]'hlt
      = ⟨.inr (.inr (seqCE.outputState[0]'h0)), seqCE.inputState[0]'hfin⟩ := by
    rcases hspec with hA | hB
    · exfalso
      have hmem0 : (⟨.inr (.inl (seqCE.inputState[0]'hfin)), seqCE.outputState[0]'h0⟩ :
          duplexSpongeTraceEntry) ∈ trCE := by
        rw [← hA]
        exact List.getElem_mem hlt
      have hmem : (⟨.inr (.inl iCE), oCE⟩ : duplexSpongeTraceEntry) ∈ trCE := hmem0
      simp only [trCE, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h
      · exact absurd (congrArg Sigma.fst h) (by simp [hashCE])
      · exact absurd (congrArg Sigma.fst h) (by simp [bwd1CE])
      · exact absurd (congrArg Sigma.fst h) (by simp [bwd2CE])
    · exact hB
  refine ⟨⟨seqCE, BacktrackSequence.Index trCE sCE seqCE⟩, ?_, ⟨0, h0⟩, oCE, iCE, ?_⟩
  · simp only [Backtrack.J_BT, Finset.mem_image]
    exact ⟨seqCE, Finset.mem_singleton_self _, rfl⟩
  · change trCE[((BacktrackSequence.Index trCE sCE seqCE).2 ⟨0, hfin⟩).val]?
      = some ⟨.inr (.inr oCE), iCE⟩
    rw [List.getElem?_eq_getElem hlt, hspec']
    rfl

/-- **The redundant-trace corner of CO25 Lemma 5.12 (honest form) is FALSE**: dedup can
keep only the orientation swap of a raw inverse anchor, hiding `E_inv` from `E`.
Machine-checked counterexample over `StmtIn = Unit`, `U = UInt8`, `N = 2, R = 1`. -/
theorem lemma5_12HonestRedundantResidual_not_universal :
    ¬ ∀ (StmtIn U : Type) [SpongeUnit U] [SpongeSize],
        Lemma5_12HonestRedundantResidual StmtIn U := by
  intro hall
  exact hall Unit UInt8 trCE sCE SCE trCE_not_noRedundant trCE_not_E trCE_E_inv

/-- **The original M2a residual surface `Lemma5_12HonestResidual` is FALSE as stated**:
it quantifies honest backtracking over *raw* traces while `E` reads the *deduplicated*
trace. The honest repair is the redundancy-free statement, proven above as
`lemma5_12Honest_of_noRedundant` (which is also the CO25 setting: BackTrack and the §5.6
events run over the deduplicated trace). -/
theorem lemma5_12HonestResidual_not_universal :
    ¬ ∀ (StmtIn U : Type) [SpongeUnit U] [SpongeSize],
        Lemma5_12HonestResidual StmtIn U := by
  intro hall
  exact hall Unit UInt8 trCE sCE SCE trCE_not_E trCE_E_inv

end Counterexample

/-! ## Axiom audit -/

#print axioms lemma5_12Honest_of_noRedundant
#print axioms lemma5_14Honest_of_noRedundant
#print axioms lemma5_16Honest_of_noRedundant
#print axioms backtrackSequence_unique
#print axioms E_of_bwd_chain_entry
#print axioms lemma5_12HonestResidual_of_redundantResidual
#print axioms lemma5_14HonestResidual_of_redundantResidual
#print axioms lemma5_16HonestResidual_of_redundantResidual
#print axioms lemma5_12HonestRedundantResidual_not_universal
#print axioms lemma5_12HonestResidual_not_universal

end DuplexSpongeFS.BacktrackLemmas
