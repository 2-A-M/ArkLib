/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.BasicCompleteness
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
# Verified foundations for the basic Fiat-Shamir HVZK coupling (#116)

`FiatShamir/HVZKTransferReduction.lean` reduces the basic Fiat-Shamir HVZK transfer residual to a
single `coupling` identity — the honest Fiat-Shamir transcript distribution equals the interactive
honest transcript distribution projected to its messages. This file collects the verified building
blocks of that coupling (the proven atoms of the `runToRoundFS` ↔ `runToRound` prover-run induction):

* `fsChallengeUniformImpl` — the canonical uniformly-sampling Fiat-Shamir challenge implementation,
  mirroring the interactive `challengeQueryImpl`;
* `simulateQ_addLift_fsChallengeUniform_query_run` — a challenge-oracle query under it is a fresh
  uniform sample (per-round challenge atom);
* `evalDist_bind_comm` — independent draws commute at `evalDist`, UNCONDITIONALLY (the SPMF failure
  mass `P_p + P_q - P_p·P_q` is symmetric); reconciles the `V_to_P` round, where `processRoundFS`
  draws `receiveChallenge` then the challenge while interactive `processRound` draws them in the
  opposite order;
* `runToRoundFS_succ` — one-round decomposition of the Fiat-Shamir prover run.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- The canonical Fiat-Shamir challenge implementation for honest-verifier ZK: answer each
challenge-oracle query by a fresh uniform sample of the challenge type (ignoring the hash key and
the ambient state), exactly mirroring the interactive `challengeQueryImpl`. -/
@[reducible, inline, specialize]
def fsChallengeUniformImpl :
    QueryImpl (fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp) :=
  fun q => fun s => (fun c => (c, s)) <$> ($ᵗ (pSpec.Challenge q.1))

/-- Under the canonical uniform FS implementation, simulating a single challenge-oracle query is a
fresh uniform sample of the challenge type, leaving the ambient state unchanged. The HVZK analogue
of `ProtocolSpec.simulateQ_addLift_fsChallenge_query_run`. -/
theorem simulateQ_addLift_fsChallengeUniform_query_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (q : (fsChallengeOracle StmtIn pSpec).Domain) (s : σ) :
    StateT.run (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)))
      (query (spec := fsChallengeOracle StmtIn pSpec) q :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          ((fsChallengeOracle StmtIn pSpec).Range q))) s
        = StateT.run (fsChallengeUniformImpl (σ := σ) q) s := by
  rw [show (query (spec := fsChallengeOracle StmtIn pSpec) q :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          ((fsChallengeOracle StmtIn pSpec).Range q))
      = liftM (liftM (OracleSpec.query q) :
          OracleQuery (oSpec + fsChallengeOracle StmtIn pSpec)
            ((fsChallengeOracle StmtIn pSpec).Range q)) from rfl,
    simulateQ_query]
  simp [OracleQuery.liftM_add_right_def, QueryImpl.addLift_def, QueryImpl.liftTarget_self]

/-- Interactive analogue: under `impl.addLift challengeQueryImpl`, simulating a single challenge
query is a fresh uniform sample of the challenge type, leaving the ambient state unchanged. This is
the V_to_P twin of `simulateQ_addLift_fsChallengeUniform_query_run`; it matches the FS atom's reduced
form, so a V_to_P round's two challenge draws are the same `$ᵗ`. -/
theorem simulateQ_addLift_challengeQueryImpl_query_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (q : ([pSpec.Challenge]ₒ).Domain) (s : σ) :
    StateT.run (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec)))
      (query (spec := [pSpec.Challenge]ₒ) q :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (([pSpec.Challenge]ₒ).Range q))) s
        = (fun c => (c, s)) <$> (challengeQueryImpl (pSpec := pSpec) q) := by
  rw [show (query (spec := [pSpec.Challenge]ₒ) q :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (([pSpec.Challenge]ₒ).Range q))
      = liftM (liftM (OracleSpec.query q) :
          OracleQuery (oSpec + [pSpec.Challenge]ₒ) (([pSpec.Challenge]ₒ).Range q)) from rfl,
    simulateQ_query]
  simp [OracleQuery.liftM_add_right_def, QueryImpl.addLift_def, QueryImpl.liftTarget_self]

/-- `getChallenge`-form of the interactive challenge atom, matching exactly the `liftM (getChallenge
i)` shape that `Prover.processRound` draws at a V_to_P round (so it rewrites the coupling goal
directly). -/
theorem simulateQ_addLift_challengeQueryImpl_getChallenge_run
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (i : pSpec.ChallengeIdx) (s : σ) :
    StateT.run (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec)))
      (liftM (pSpec.getChallenge i) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i))) s
        = (fun c => (c, s)) <$> (challengeQueryImpl (pSpec := pSpec) ⟨i, ()⟩) := by
  rw [ProtocolSpec.getChallenge]
  exact simulateQ_addLift_challengeQueryImpl_query_run impl ⟨i, ()⟩ s

/-- **Independent-draw commutation at `evalDist`** (the gating fact for the per-round V_to_P coupling
step). Drawing `p` then `q` gives the same distribution as `q` then `p`. Holds UNCONDITIONALLY (the
SPMF/`OptionT PMF` failure mass `P_p + P_q - P_p·P_q` is symmetric), via the proven point-mass swap
`probOutput_bind_bind_swap` and `evalDist_ext`. `processRoundFS` (V_to_P) draws `receiveChallenge`
then the challenge; interactive `processRound` draws the challenge then `receiveChallenge` — this
lemma reconciles the two. -/
theorem evalDist_bind_comm {m : Type → Type} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {α' β' γ' : Type} (p : m α') (q : m β') (f : α' → β' → m γ') :
    evalDist (do let a ← p; let b ← q; f a b)
      = evalDist (do let b ← q; let a ← p; f a b) :=
  evalDist_ext fun x => probOutput_bind_bind_swap p q f x

variable (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- One-round decomposition of the Fiat-Shamir prover run: `runToRoundFS` at `j.succ` is the run up
to `j.castSucc` followed by one `processRoundFS j`. -/
theorem runToRoundFS_succ (stmt : StmtIn) (wit : WitIn) (j : Fin n) :
    P.runToRoundFS j.succ stmt (P.input (stmt, wit))
      = P.runToRoundFS j.castSucc stmt (P.input (stmt, wit)) >>=
        fun r => P.processRoundFS j (pure r) := by
  conv_lhs => rw [Prover.runToRoundFS, Fin.induction_succ]
  rw [Prover.processRoundFS]
  simp only [bind_pure_comp, Prover.runToRoundFS, map_eq_bind_pure_comp, bind_assoc]
  rfl

end Reduction
