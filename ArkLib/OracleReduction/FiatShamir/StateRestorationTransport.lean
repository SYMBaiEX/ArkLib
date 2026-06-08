/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.BasicCompleteness
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
# Basic Fiat-Shamir State-Restoration Pre-Transport Wrappers (#116)

`FiatShamir/Basic.lean` exposes wrappers that apply a discharged state-restoration transfer
residual and then weaken the Fiat-Shamir conclusion.  This companion file provides the dual
consumer shape: first transport the state-restoration hypothesis with
`Verifier.StateRestoration.*.mono_*`, then apply a transfer residual that is already stated at the
target parameters.

It also exposes the one-message Fiat-Shamir adversary payload as a state-restoration prover payload,
so the eventual coupled `simulateQ` proof can compare both games over the same transcript
derivation surface.

Most declarations here are API plumbing over the existing residual/coupling surfaces.  The
canonical shared-challenge-table soundness residual is discharged below; the knowledge-soundness
and zero-knowledge transfer content remains separate.
-/

noncomputable section

open ProtocolSpec OracleComp OracleSpec
open ArkLib.FiatShamir.CompletenessAux
open scoped NNReal

section TranscriptAliases

namespace ProtocolSpec

/-- The slow Fiat-Shamir challenge oracle is definitionally the state-restoration challenge
oracle. This is the structural coupling used by the #116 soundness-transfer reduction. -/
theorem fsChallengeOracle_eq_srChallengeOracle {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} :
    fsChallengeOracle Statement pSpec = srChallengeOracle Statement pSpec := by
  rfl

/-- The cached slow Fiat-Shamir challenge query implementation is definitionally the cached
state-restoration challenge query implementation. -/
theorem fsChallengeQueryImpl'_eq_srChallengeQueryImpl' {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    fsChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) =
      srChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) := by
  rfl

/-- Slow Fiat-Shamir challenge query implementation with the cached challenge table state written
directly over the Fiat-Shamir oracle alias.

The existing `fsChallengeQueryImpl'` alias unfolds through the state-restoration oracle name.  This
definition exposes the same cached-table behavior at the `fsChallengeOracle` type, so coupled
soundness proofs can use `QueryImpl.addLift` without asking Lean to lift between the alias-expanded
state monads. -/
@[reducible, inline, specialize, simp]
def fsChallengeQueryImplState {Statement : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl (fsChallengeOracle Statement pSpec)
      (StateT (QueryImpl (fsChallengeOracle Statement pSpec) Id) ProbComp) :=
  fun | ⟨i, t⟩ => fun f => pure (f ⟨i, t⟩, f)

/-- The FS-state implementation is definitionally the usual cached slow-Fiat-Shamir query
implementation after fixing the target state type to the Fiat-Shamir oracle alias. -/
theorem fsChallengeQueryImplState_eq_fsChallengeQueryImpl' {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    fsChallengeQueryImplState (Statement := Statement) (pSpec := pSpec) =
      (fsChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) :
        QueryImpl (fsChallengeOracle Statement pSpec)
          (StateT (QueryImpl (fsChallengeOracle Statement pSpec) Id) ProbComp)) := by
  rfl

/-- The FS-state implementation is also definitionally the cached state-restoration challenge
implementation. This is the normalized shared-table shape used by the canonical coupled soundness
proof below. -/
theorem fsChallengeQueryImplState_eq_srChallengeQueryImpl' {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    fsChallengeQueryImplState (Statement := Statement) (pSpec := pSpec) =
      srChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) := by
  rfl

namespace MessagesUpTo

/-- Partial transcript derivation for slow Fiat-Shamir is definitionally the state-restoration
transcript derivation. -/
theorem deriveTranscriptFS_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) :
    deriveTranscriptFS (oSpec := oSpec) stmt k messages =
      deriveTranscriptSR (oSpec := oSpec) stmt k messages := by
  rfl

end MessagesUpTo

namespace Messages

/-- Full transcript derivation for slow Fiat-Shamir is definitionally the state-restoration
transcript derivation. -/
theorem deriveTranscriptFS_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (messages : pSpec.Messages) :
    deriveTranscriptFS (oSpec := oSpec) stmt messages =
      deriveTranscriptSR (oSpec := oSpec) stmt messages := by
  rfl

end Messages

end ProtocolSpec

namespace Verifier

/-- The basic Fiat-Shamir verifier can be expanded using the state-restoration transcript
derivation, since `deriveTranscriptFS` and `deriveTranscriptSR` are aliases. -/
theorem fiatShamir_verify_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩) :
    (V.fiatShamir).verify stmtIn proof =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← messages.deriveTranscriptSR (oSpec := oSpec) stmtIn
        let v ← (V.verify stmtIn transcript).run
        v.getM) := by
  rfl

namespace StateRestoration

/-- The state-restoration soundness game can be read through the slow Fiat-Shamir transcript
derivation, since both derivations query the same challenge oracle. -/
theorem srSoundnessGame_eq_deriveTranscriptFS {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec) :
    srSoundnessGame P =
      (do
        let ⟨stmtIn, messages⟩ ← P
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn⟩) := by
  rfl

/-- The state-restoration knowledge-soundness game can likewise be read through the slow
Fiat-Shamir transcript derivation. -/
theorem srKnowledgeSoundnessGame_eq_deriveTranscriptFS {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut : Type}
    (P : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec) :
    srKnowledgeSoundnessGame P =
      (do
        let ⟨stmtIn, messages, witOut⟩ ← P
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn, witOut⟩) := by
  rfl

end StateRestoration

end Verifier

#print axioms ProtocolSpec.fsChallengeOracle_eq_srChallengeOracle
#print axioms ProtocolSpec.fsChallengeQueryImpl'_eq_srChallengeQueryImpl'
#print axioms ProtocolSpec.fsChallengeQueryImplState
#print axioms ProtocolSpec.fsChallengeQueryImplState_eq_fsChallengeQueryImpl'
#print axioms ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl'
#print axioms ProtocolSpec.MessagesUpTo.deriveTranscriptFS_eq_deriveTranscriptSR
#print axioms ProtocolSpec.Messages.deriveTranscriptFS_eq_deriveTranscriptSR
#print axioms Verifier.fiatShamir_verify_eq_deriveTranscriptSR
#print axioms Verifier.StateRestoration.srSoundnessGame_eq_deriveTranscriptFS
#print axioms Verifier.StateRestoration.srKnowledgeSoundnessGame_eq_deriveTranscriptFS

end TranscriptAliases

section FiatShamirAdversaryAdapter

namespace Prover

namespace StateRestoration

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type}

/-- View a fixed malicious one-message Fiat-Shamir prover execution as the corresponding
state-restoration soundness prover payload.

The adapter runs the Fiat-Shamir prover's single prover-to-verifier message round and then replays
`P.output`, discarding the result. The replay is needed for the coupled soundness proof: the
one-message Fiat-Shamir `Reduction.run` performs the prover output step before verifier queries,
so the state-restoration adversary must make the same shared-oracle queries to keep the simulated
oracle-table state aligned. -/
def soundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prover.StateRestoration.Soundness oSpec StmtIn pSpec := do
  let state := P.input (stmtIn, witIn)
  let ⟨proof, state⟩ ←
    P.sendMessage ⟨0, by simp⟩ state
  let _ctxOut ← P.output state
  let messages : pSpec.Messages := proof
  return ⟨stmtIn, messages⟩

/-- The state-restoration game for the Fiat-Shamir-prover adapter is exactly the single
Fiat-Shamir proof-message computation, the prover output replay, and the shared state-restoration
transcript derivation. Use `ProtocolSpec.Messages.deriveTranscriptFS_eq_deriveTranscriptSR` to
rewrite the final line through the slow Fiat-Shamir alias. -/
theorem srSoundnessGame_soundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    srSoundnessGame
        (soundnessOfFiatShamirProver (oSpec := oSpec) (pSpec := pSpec) P stmtIn witIn)
      =
      (do
        let state := P.input (stmtIn, witIn)
        let ⟨proof, state⟩ ←
          P.sendMessage ⟨0, by simp⟩ state
        let _ctxOut ← P.output state
        let messages : pSpec.Messages := proof
        let transcript ← messages.deriveTranscriptSR (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn⟩) := by
  simp [srSoundnessGame, soundnessOfFiatShamirProver]

/-- View a fixed malicious one-message Fiat-Shamir prover execution as the corresponding
state-restoration knowledge-soundness prover payload.

The adapter replays the Fiat-Shamir prover's output step after the proof-message round, preserving
the same final-state evolution while retaining only the output witness required by the
state-restoration knowledge game. -/
def knowledgeSoundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec := do
  let state := P.input (stmtIn, witIn)
  let ⟨proof, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
  let ctxOut ← P.output state
  let messages : pSpec.Messages := proof
  return ⟨stmtIn, messages, ctxOut.2⟩

/-- The state-restoration knowledge game for the Fiat-Shamir-prover adapter is exactly the single
Fiat-Shamir proof-message computation, followed by the prover output step and the shared
state-restoration transcript derivation. -/
theorem srKnowledgeSoundnessGame_knowledgeSoundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    srKnowledgeSoundnessGame
        (knowledgeSoundnessOfFiatShamirProver (oSpec := oSpec) (pSpec := pSpec) P stmtIn witIn)
      =
      (do
        let state := P.input (stmtIn, witIn)
        let ⟨proof, state⟩ ←
          P.sendMessage ⟨0, by simp⟩ state
        let ctxOut ← P.output state
        let messages : pSpec.Messages := proof
        let transcript ← messages.deriveTranscriptSR (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn, ctxOut.2⟩) := by
  simp [srKnowledgeSoundnessGame, knowledgeSoundnessOfFiatShamirProver]

end StateRestoration

end Prover

#print axioms Prover.StateRestoration.soundnessOfFiatShamirProver
#print axioms Prover.StateRestoration.srSoundnessGame_soundnessOfFiatShamirProver
#print axioms Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver
#print axioms Prover.StateRestoration.srKnowledgeSoundnessGame_knowledgeSoundnessOfFiatShamirProver

end FiatShamirAdversaryAdapter

section FiatShamirLiftPath

namespace Reduction

attribute [local instance] Reduction.fiatShamirChallengeOracleInterface

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι} {StmtIn α β : Type}

/-- Directly lifting a base Fiat-Shamir-oracle computation into the appended one-message
Fiat-Shamir protocol oracle spec is the same path as first lifting it into `OptionT` over the base
spec and then lifting that `OptionT` computation to the appended spec.

This names the lift-path coherence exposed by the #116 coupled soundness run expansion, where the
generic one-message `Reduction.run_of_prover_first` chooses the direct source-level path but
hand-written SR-transcript shapes naturally elaborate through the nested `OptionT` path. -/
theorem fiatShamir_liftM_base_to_append_eq_nested
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) :
    (liftM oa :
        OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
      (liftM
        ((liftM oa :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α)) :
        OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  rfl

/-- The inferred `liftM` path for an `OptionT` computation over the base Fiat-Shamir oracle spec
passes through the right-associated append before landing in the left-associated appended target.

This is the elaboration path exposed by the one-message `deriveTranscriptSR` run-shape expansion. -/
theorem fiatShamir_liftM_base_optionT_to_rightAssoc_to_append
    (oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    (liftM oa :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
    (liftM
        (liftM oa :
          OptionT (OracleComp
            (oSpec + (fsChallengeOracle StmtIn pSpec +
              [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))) α) :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  rfl

/-- Specialization of `OracleComp.liftM_OptionT_add_assoc_right` to the basic Fiat-Shamir appended
challenge spec. It collapses the right-associated lift path into the direct left-associated
`liftComp` path on the underlying `OptionT.run`. -/
theorem fiatShamir_liftM_rightAssoc_to_append_eq_direct
    (oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    (liftM
        (liftM oa :
          OptionT (OracleComp
            (oSpec + (fsChallengeOracle StmtIn pSpec +
              [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))) α) :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
      OptionT.mk (OracleComp.liftComp oa.run
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) := by
  exact OracleComp.liftM_OptionT_add_assoc_right (spec₁ := oSpec)
    (spec₂ := fsChallengeOracle StmtIn pSpec)
    (spec₃ := [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
    oa

/-- Combined Fiat-Shamir lift-path normalization for `OptionT` computations over the base
Fiat-Shamir oracle spec: the inferred append lift is the explicit direct `liftComp` of the
underlying `run`. -/
theorem fiatShamir_liftM_base_optionT_to_append_eq_direct
    (oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    (liftM oa :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
      OptionT.mk (OracleComp.liftComp oa.run
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) := by
  rw [fiatShamir_liftM_base_optionT_to_rightAssoc_to_append]
  exact fiatShamir_liftM_rightAssoc_to_append_eq_direct oa

/-- Running the direct append-lift of a base Fiat-Shamir oracle computation is the explicit
`some`-map over the direct `liftComp` path into the appended one-message challenge spec. -/
theorem fiatShamir_liftM_oracleComp_to_append_run
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) :
    ((liftM oa : OptionT (OracleComp
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α).run) =
      (some <$> OracleComp.liftComp oa
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) := by
  rw [fiatShamir_liftM_base_to_append_eq_nested oa]
  rw [fiatShamir_liftM_base_optionT_to_append_eq_direct
    (oa := (liftM oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α))]
  simp only [OptionT.run_mk]
  change OracleComp.liftComp (some <$> oa)
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ) =
    some <$> OracleComp.liftComp oa
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
  rw [OracleComp.liftComp_map]

/-- Appended-spec lift/getM collapse for a mapped base `OptionT` computation. This is the
right-associated analogue of the completeness helper used by the one-message run-shape proof. -/
theorem fiatShamir_lift_run_map_getM_to_append
    (X : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) β)
    (f : β → α) :
    ((liftM X.run :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) (Option β)) >>=
        fun o => f <$> (o.getM : OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) β)) =
      (f <$> (liftM X : OptionT (OracleComp
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) β) :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_map]
  rw [fiatShamir_liftM_oracleComp_to_append_run (oa := X.run)]
  rw [congrArg OptionT.run (fiatShamir_liftM_base_optionT_to_append_eq_direct X)]
  simp only [OptionT.run_mk, Option.elimM, bind_assoc, map_eq_pure_bind, pure_bind]
  refine bind_congr ?_
  intro x
  cases x <;> rfl

/-- Appended-spec lift/getM collapse for a base `OptionT` computation. -/
theorem fiatShamir_lift_run_bind_getM_to_append
    (X : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    ((liftM X.run :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) (Option α)) >>=
        fun o => (o.getM : OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)) =
      (liftM X : OptionT (OracleComp
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [OptionT.run_bind]
  rw [fiatShamir_liftM_oracleComp_to_append_run (oa := X.run)]
  rw [congrArg OptionT.run (fiatShamir_liftM_base_optionT_to_append_eq_direct X)]
  simp only [OptionT.run_mk, Option.elimM, bind_assoc, map_eq_pure_bind, pure_bind]
  conv_rhs =>
    rw [← bind_pure (OracleComp.liftComp X.run
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))]
  congr 1
  funext x
  cases x <;> rfl

/-- Same appended-spec `getM` collapse, with the continuation written as `Option.getM`. -/
theorem fiatShamir_lift_run_Option_getM_to_append
    (X : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    ((liftM X.run :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) (Option α)) >>=
        Option.getM) =
      (liftM X : OptionT (OracleComp
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  exact fiatShamir_lift_run_bind_getM_to_append X

end Reduction

#print axioms Reduction.fiatShamir_liftM_base_to_append_eq_nested
#print axioms Reduction.fiatShamir_liftM_base_optionT_to_rightAssoc_to_append
#print axioms Reduction.fiatShamir_liftM_rightAssoc_to_append_eq_direct
#print axioms Reduction.fiatShamir_liftM_base_optionT_to_append_eq_direct
#print axioms Reduction.fiatShamir_liftM_oracleComp_to_append_run
#print axioms Reduction.fiatShamir_lift_run_map_getM_to_append
#print axioms Reduction.fiatShamir_lift_run_bind_getM_to_append
#print axioms Reduction.fiatShamir_lift_run_Option_getM_to_append

end FiatShamirLiftPath

section CoupledQueryImpl

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- The concrete query implementation used by the coupled #116 soundness proof: original oracle
queries are interpreted by the state-restoration implementation, while Fiat-Shamir challenge
queries read the same cached challenge table that state restoration samples as its initial state. -/
def fiatShamirCoupledQueryImpl
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp)) :
    QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec)
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp) :=
  srImpl.addLift (ProtocolSpec.fsChallengeQueryImplState (Statement := StmtIn) (pSpec := pSpec))

/-- Original-oracle queries through the coupled Fiat-Shamir implementation are exactly the
state-restoration implementation queries. -/
@[simp]
theorem fiatShamirCoupledQueryImpl_apply_left
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (q : oSpec.Domain) :
    fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn)
        srImpl (.inl q) =
      srImpl q := by
  rfl

/-- Fiat-Shamir challenge queries through the coupled implementation read the cached challenge
table and leave it unchanged. -/
@[simp]
theorem fiatShamirCoupledQueryImpl_apply_right
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (q : (fsChallengeOracle StmtIn pSpec).Domain) :
    fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn)
        srImpl (.inr q) =
      (fun f => pure (f q, f)) := by
  rfl

/-- The coupled implementation is exactly the original-oracle implementation plus the fixed-state
cached Fiat-Shamir challenge implementation. This is the `addLift` form consumed by generic
simulation lemmas. -/
theorem fiatShamirCoupledQueryImpl_eq_addLift_fsChallengeQueryImplState
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp)) :
    fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl =
      srImpl.addLift
        (ProtocolSpec.fsChallengeQueryImplState (Statement := StmtIn) (pSpec := pSpec)) := by
  rfl

/-- Simulating a lifted original-oracle computation through the coupled Fiat-Shamir implementation
projects to the original state-restoration implementation. -/
theorem simulateQ_fiatShamirCoupled_liftComp_left
    {α : Type}
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (oa : OracleComp oSpec α) :
    simulateQ
        (fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (OracleComp.liftComp oa (oSpec + fsChallengeOracle StmtIn pSpec)) =
      simulateQ srImpl oa := by
  simpa [fiatShamirCoupledQueryImpl, QueryImpl.addLift_def] using
    (QueryImpl.simulateQ_add_liftComp_left
      (impl₁' := srImpl)
      (impl₂' := ProtocolSpec.fsChallengeQueryImplState
        (Statement := StmtIn) (pSpec := pSpec))
      (oa := oa))

/-- `liftM` form of `simulateQ_fiatShamirCoupled_liftComp_left`. -/
theorem simulateQ_fiatShamirCoupled_liftM_left
    {α : Type}
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (oa : OracleComp oSpec α) :
    simulateQ
        (fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (liftM oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) =
      simulateQ srImpl oa := by
  rw [show (liftM oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) =
      OracleComp.liftComp oa (oSpec + fsChallengeOracle StmtIn pSpec) by
        rw [OracleComp.liftComp_eq_liftM]]
  exact simulateQ_fiatShamirCoupled_liftComp_left srImpl oa

/-- Simulating a lifted Fiat-Shamir challenge-oracle computation through the coupled implementation
projects to the cached challenge-table implementation. This is the right-side companion to
`simulateQ_fiatShamirCoupled_liftComp_left`. -/
theorem simulateQ_fiatShamirCoupled_liftComp_right
    {α : Type}
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (oa : OracleComp (fsChallengeOracle StmtIn pSpec) α) :
    simulateQ
        (fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (OracleComp.liftComp oa (oSpec + fsChallengeOracle StmtIn pSpec)) =
      simulateQ
        (ProtocolSpec.fsChallengeQueryImplState (Statement := StmtIn) (pSpec := pSpec))
        oa := by
  simpa [fiatShamirCoupledQueryImpl, QueryImpl.addLift_def] using
    (QueryImpl.simulateQ_add_liftComp_right
      (impl₁' := srImpl)
      (impl₂' := ProtocolSpec.fsChallengeQueryImplState
        (Statement := StmtIn) (pSpec := pSpec))
      (ob := oa))

/-- `liftM` form of `simulateQ_fiatShamirCoupled_liftComp_right`. -/
theorem simulateQ_fiatShamirCoupled_liftM_right
    {α : Type}
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (oa : OracleComp (fsChallengeOracle StmtIn pSpec) α) :
    simulateQ
        (fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (liftM oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) =
      simulateQ
        (ProtocolSpec.fsChallengeQueryImplState (Statement := StmtIn) (pSpec := pSpec))
        oa := by
  rw [show (liftM oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) =
      OracleComp.liftComp oa (oSpec + fsChallengeOracle StmtIn pSpec) by
        rw [OracleComp.liftComp_eq_liftM]]
  exact simulateQ_fiatShamirCoupled_liftComp_right srImpl oa

end Reduction

#print axioms Reduction.fiatShamirCoupledQueryImpl
#print axioms Reduction.fiatShamirCoupledQueryImpl_apply_left
#print axioms Reduction.fiatShamirCoupledQueryImpl_apply_right
#print axioms Reduction.fiatShamirCoupledQueryImpl_eq_addLift_fsChallengeQueryImplState
#print axioms Reduction.simulateQ_fiatShamirCoupled_liftComp_left
#print axioms Reduction.simulateQ_fiatShamirCoupled_liftM_left
#print axioms Reduction.simulateQ_fiatShamirCoupled_liftComp_right
#print axioms Reduction.simulateQ_fiatShamirCoupled_liftM_right

end CoupledQueryImpl

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

attribute [local instance 10000] Reduction.fiatShamirNoChallengeSampleable

section CanonicalSoundness

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {WitIn' WitOut' : Type}

local instance fiatShamirProverOnlyCanonicalSoundness : ProtocolSpec.ProverOnly
    (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) where
  prover_first' := by simp

private theorem stateT_option_map_elim_some {σ α β : Type}
    (mx : StateT σ ProbComp (Option α)) (f : α → β) :
    (do
        let x ← some <$> mx
        x.elim (pure none) fun x => pure (Option.map f x)) =
      (Option.map f <$> mx) := by
  ext s
  simp only [StateT.run_bind, StateT.run_map]
  rw [map_eq_pure_bind]
  simp only [bind_assoc, pure_bind]
  conv_rhs => rw [map_eq_pure_bind]
  congr 1

private theorem simulateQ_optionT_map_monadLift_run
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ α β : Type}
    (impl : QueryImpl (spec₁ + spec₂) (StateT σ ProbComp))
    (X : OptionT (OracleComp spec₁) α) (f : α → β) :
    (do
        let x ← simulateQ impl
          (monadLift
            (some <$> (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α))) :
              OracleComp (spec₁ + spec₂) (Option (Option α)))
        x.elim (pure none) fun x => pure (Option.map f x)) =
      simulateQ impl
        ((f <$> (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α)).run) := by
  rw [show
      simulateQ impl
          (monadLift
            (some <$> (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α))) :
              OracleComp (spec₁ + spec₂) (Option (Option α))) =
        (some <$> simulateQ impl
          (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α))) by
    rw [← simulateQ_map]
    rfl]
  rw [stateT_option_map_elim_some]
  rw [OptionT.run_map, optionT_monadLift_run, simulateQ_map]

private theorem probEvent_optionT_stateT_init
    {σ α : Type} (init : ProbComp σ) (comp : StateT σ ProbComp (Option α))
    (p : α → Prop) :
    Pr[p | (do
        let s ← OptionT.mk (some <$> init)
        OptionT.mk ((fun x : Option α × σ => x.1) <$> comp.run s) : OptionT ProbComp α)] =
      Pr[fun o : Option α => o.elim False p |
        do
          let s ← init
          (fun x : Option α × σ => x.1) <$> comp.run s] := by
  rw [show
      (do
        let s ← OptionT.mk (some <$> init)
        OptionT.mk ((fun x : Option α × σ => x.1) <$> comp.run s) : OptionT ProbComp α) =
      OptionT.mk (do
        let s ← init
        (fun x : Option α × σ => x.1) <$> comp.run s) by
    apply OptionT.ext
    simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, bind_assoc, map_bind,
      Option.elim_some, pure_bind]
    rw [map_eq_pure_bind]
    simp only [bind_assoc, pure_bind, Option.elim_some]]
  exact Verifier.StateFunction.probEvent_optionT_mk_eq_elim _ _

private theorem probEvent_payload_option_eq_stmt
    {σ Payload StmtIn StmtOut : Type}
    (stmtIn : StmtIn) (langIn : Set StmtIn) (langOut : Set StmtOut)
    (hstmtIn : stmtIn ∉ langIn)
    (payload : Payload) (mx : StateT σ ProbComp (Option StmtOut)) (s : σ) :
    Pr[fun o : Option (Payload × StmtOut) =>
        o.elim False fun x => x.2 ∈ langOut |
      (fun x : Option (Payload × StmtOut) × σ => x.1) <$>
        ((Option.map (Prod.mk payload) <$> mx).run s)] =
    Pr[(fun x : StmtIn × Option StmtOut =>
        match x with
        | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
        | _ => False) |
      (fun x : Option StmtOut × σ => (stmtIn, x.1)) <$> mx.run s] := by
  simp only [StateT.run_map, probEvent_map, Function.comp_apply]
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator]
  apply tsum_congr
  intro x
  rcases x with ⟨stmtOut?, s'⟩
  cases stmtOut? with
  | none => simp
  | some stmtOut =>
      by_cases hOut : stmtOut ∈ langOut <;> simp [hOut, hstmtIn]

private theorem probEvent_stateT_bind_fst_mono_hetero
    {σ α β γ : Type}
    (mx : StateT σ ProbComp α) (my : α → StateT σ ProbComp (Option β))
    (oc : α → σ → ProbComp γ) (s : σ)
    (p : Option β → Prop) (q : γ → Prop)
    (h : ∀ a s', (a, s') ∈ support (mx.run s) →
      Pr[ p | (fun x : Option β × σ => x.1) <$> (my a).run s'] ≤
        Pr[ q | oc a s']) :
    Pr[ p | (fun x : Option β × σ => x.1) <$> (mx >>= my).run s] ≤
      Pr[ q | do
        let a ← mx.run s
        oc a.1 a.2] := by
  rw [StateT.run_bind, map_bind]
  exact Verifier.StateFunction.probEvent_bind_mono_heteroEvent
    (fun a ha => h a.1 a.2 ha)

/-- Explicit one-message Fiat-Shamir adversary execution after the empty transformed challenge
oracle has been collapsed. The payload retains the proof transcript and prover output context so
it can be compared directly with the state-restoration adapter. -/
def fiatShamirAdversaryExecution
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn' StmtOut WitOut'
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn') :
    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      (((Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut') ×
        StmtOut)) := do
  let state := P.input (stmtIn, witIn)
  let ⟨proofMessages, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
  let ctxOut ← P.output state
  let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => proofMessages
  let transcript ←
    (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofMessages) :
      OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
  let stmtOut ←
    (monadLift (V.verify stmtIn transcript) :
      OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
  return ⟨⟨proof, ctxOut⟩, stmtOut⟩

/-- Collapse the one-message transformed Fiat-Shamir reduction run to the explicit adversary
execution over `oSpec + fsChallengeOracle`. -/
theorem fiatShamirAdversary_runCollapse
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn' StmtOut WitOut'
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn') :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (Reduction.run stmtIn witIn { prover := P, verifier := V.fiatShamir }).run =
      simulateQ impl (fiatShamirAdversaryExecution P V stmtIn witIn).run := by
  rw [Reduction.run_of_prover_first
    (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))]
  unfold fiatShamirAdversaryExecution
  simp only [Verifier.fiatShamir, Verifier.run,
    liftComp_eq_liftM, bind_assoc, pure_bind, monadLift_bind, monadLift_pure, map_bind,
    bind_pure_comp, liftM_map, liftM_optionT_combined, bind_map_left,
    monadLift_optionT_lift_run_map_getM]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, optionT_monadLift_run,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    OptionT.simulateQ_addLift_liftM, Option.getM_map_run, Option.elimM,
    simulateQ_option_elim, bind_assoc, pure_bind, map_bind,
    simulateQ_getM_run_some, OptionT.simulateQ_getM_some, StateT.run_simulateQ_optiont_map,
    StateT.run_pure_some_bind_map, Option.map_comp_lambda, simulateQ_map_monadLift_getM_run,
    optionT_run_simulateQ_liftquery, OptionT.run_monadLift]
  have hVerify (td : pSpec.FullTranscript) :
      simulateQ impl (OptionT.run (simulateQ (fun t : oSpec.Domain =>
          (liftM (OracleSpec.query (spec := oSpec) t) :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
          (V.verify stmtIn td))) =
        simulateQ impl (liftM (V.verify stmtIn td).run) := by
    congr 1
  apply bind_congr
  intro proofState?
  cases proofState? with
  | none => rfl
  | some proofState =>
      apply bind_congr
      intro ctxOut?
      cases ctxOut? with
      | none => rfl
      | some ctxOut =>
          apply bind_congr
          intro transcript?
          cases transcript? with
          | none => rfl
          | some transcript =>
              let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
                | ⟨0, _⟩ => proofState.1
              simpa [liftM_eq_monadLift, proof] using
                (simulateQ_optionT_map_monadLift_run
                  (impl := impl)
                  (X := V.verify stmtIn transcript)
                  (f := fun stmtOut : StmtOut =>
                    Prod.mk (Prod.mk proof ctxOut) stmtOut))

set_option linter.flexible false in
/-- Canonical coupled state-restoration soundness implies basic Fiat-Shamir soundness when both
games use the same sampled cached Fiat-Shamir challenge table. -/
theorem fiatShamir_soundnessTransferResidual_canonical
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    fiatShamir_soundnessTransferResidual srInit srImpl srInit
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      langIn langOut soundnessError V := by
  intro hSR WitIn' WitOut' witIn prover stmtIn hstmtIn
  have h :=
    hSR (Prover.StateRestoration.soundnessOfFiatShamirProver
      (oSpec := oSpec) (pSpec := pSpec) prover stmtIn witIn)
  dsimp only
  rw [fiatShamirAdversary_runCollapse
    (impl := fiatShamirCoupledQueryImpl
      (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
    (P := prover) (V := V) (stmtIn := stmtIn) (witIn := witIn)]
  refine le_trans ?_ h
  simp [Verifier.soundness, Verifier.StateRestoration.soundness,
    fiatShamirAdversaryExecution, fiatShamirCoupledQueryImpl,
    ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl',
    probEvent_optionT_stateT_init,
    probEvent_payload_option_eq_stmt,
    Verifier.StateFunction.probEvent_optionT_mk_eq_elim, hstmtIn,
    probEvent_map, map_bind, Functor.map_map, Function.comp,
    StateT.run_bind, StateT.run_map, liftM_eq_monadLift,
    Prover.StateRestoration.soundnessOfFiatShamirProver,
    Verifier.StateRestoration.srSoundnessGame_eq_deriveTranscriptFS,
    Verifier.fiatShamir_verify_eq,
    Reduction.fiatShamir, Prover.fiatShamir, Verifier.fiatShamir,
    Reduction.run, Prover.run, Prover.runToRound, Prover.processRound]
  refine Verifier.StateFunction.probEvent_bind_mono_heteroEvent (fun table _ => ?_)
  rw [← ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl'
    (Statement := StmtIn) (pSpec := pSpec)]
  refine probEvent_stateT_bind_fst_mono_hetero
    (mx := simulateQ
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      (prover.sendMessage
        (⟨0, by simp⟩ :
          (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).MessageIdx)
        (prover.input (stmtIn, witIn))))
    (my := fun proofState => do
      let ctxOut ← simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (prover.output proofState.2)
      let transcript ← simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1)
      let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
        | ⟨0, _⟩ => proofState.1
      Option.map (Prod.mk (Prod.mk proof ctxOut)) <$>
        simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
    (oc := fun proofState table => do
      let ctxOut ← StateT.run (simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (prover.output proofState.2) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (StmtOut × WitOut')) table
      let transcript ← StateT.run (simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            pSpec.FullTranscript) ctxOut.2
      (fun a : Option StmtOut × QueryImpl (fsChallengeOracle StmtIn pSpec) Id =>
          (stmtIn, a.1)) <$>
        StateT.run (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript.1 V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (Option StmtOut)) transcript.2)
    (p := fun o :
        Option ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut')) × StmtOut) =>
      o.elim False fun x => x.2 ∈ langOut)
    (q := fun x : StmtIn × Option StmtOut =>
      match x with
      | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
      | _ => False)
    (s := table) ?_
  intro proofState table' _
  refine probEvent_stateT_bind_fst_mono_hetero
    (mx := simulateQ
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      (prover.output proofState.2))
    (my := fun ctxOut => do
      let transcript ← simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1)
      let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
        | ⟨0, _⟩ => proofState.1
      Option.map (Prod.mk (Prod.mk proof ctxOut)) <$>
        simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
    (oc := fun _ctxOut table => do
      let transcript ← StateT.run (simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            pSpec.FullTranscript) table
      (fun a : Option StmtOut × QueryImpl (fsChallengeOracle StmtIn pSpec) Id =>
          (stmtIn, a.1)) <$>
        StateT.run (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript.1 V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (Option StmtOut)) transcript.2)
    (p := fun o :
        Option ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut')) × StmtOut) =>
      o.elim False fun x => x.2 ∈ langOut)
    (q := fun x : StmtIn × Option StmtOut =>
      match x with
      | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
      | _ => False)
    (s := table') ?_
  intro ctxOut table'' _
  refine probEvent_stateT_bind_fst_mono_hetero
    (mx := simulateQ
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1))
    (my := fun transcript => do
      let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
        | ⟨0, _⟩ => proofState.1
      Option.map (Prod.mk (Prod.mk proof ctxOut)) <$>
        simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
    (oc := fun transcript table => do
      (fun a : Option StmtOut × QueryImpl (fsChallengeOracle StmtIn pSpec) Id =>
          (stmtIn, a.1)) <$>
        StateT.run (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (Option StmtOut)) table)
    (p := fun o :
        Option ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut')) × StmtOut) =>
      o.elim False fun x => x.2 ∈ langOut)
    (q := fun x : StmtIn × Option StmtOut =>
      match x with
      | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
      | _ => False)
    (s := table'') ?_
  intro transcript table''' _
  let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => proofState.1
  have hVerify :
      (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))) :
        StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp (Option StmtOut)) =
        (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
        StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp (Option StmtOut)) := by
    congr 1
  exact le_of_eq (by
    simpa [proof, hVerify.symm] using
      (probEvent_payload_option_eq_stmt
        (stmtIn := stmtIn) (langIn := langIn) (langOut := langOut)
        (hstmtIn := hstmtIn) (payload := (proof, ctxOut))
        (mx := simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
        (s := table''')))

#print axioms Reduction.fiatShamirAdversary_runCollapse
#print axioms Reduction.fiatShamir_soundnessTransferResidual_canonical

/-- Direct canonical basic Fiat-Shamir soundness transfer for the shared cached challenge table. -/
theorem fiatShamir_soundness_of_stateRestoration_canonical
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError) :
    Verifier.soundness srInit
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      langIn langOut V.fiatShamir soundnessError := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl srInit
    (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
    langIn langOut soundnessError V
    (fiatShamir_soundnessTransferResidual_canonical srInit srImpl langIn langOut
      soundnessError V)
    hSR

#print axioms Reduction.fiatShamir_soundness_of_stateRestoration_canonical

end CanonicalSoundness

section CanonicalKnowledgeSoundnessSupport

/-- Canonical straightline extractor for the transformed one-message Fiat-Shamir verifier, induced
by a state-restoration extractor for the underlying interactive verifier.

The transformed proof transcript contains exactly the underlying protocol messages.  The adapter
derives the shared slow-Fiat-Shamir/state-restoration transcript from those messages and then calls
the state-restoration extractor with the default query logs used by the current
state-restoration knowledge-soundness game. -/
def fiatShamirStraightlineExtractorOfStateRestoration
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec) :
    Extractor.Straightline (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn WitOut (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) :=
  fun stmtIn witOut proof _proveQueryLog _verifyQueryLog => do
    let messages : pSpec.Messages := proof 0
    let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
    liftM (srExtractor stmtIn witOut transcript default default)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Unfolding equation for
`fiatShamirStraightlineExtractorOfStateRestoration`, exposing the proof-message replay and
state-restoration extractor call. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_apply
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (proveQueryLog verifyQueryLog :
      QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor
        stmtIn witOut proof proveQueryLog verifyQueryLog =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        liftM (srExtractor stmtIn witOut transcript default default)) := by
  rfl

#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_apply

end CanonicalKnowledgeSoundnessSupport

/-- Basic Fiat-Shamir soundness from a transfer residual at the target error, after first relaxing
the state-restoration soundness hypothesis to that target error. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError₂ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError₂ := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn langOut
    soundnessError₂ V hTransfer
    (Verifier.StateRestoration.soundness.mono_error srInit srImpl hSR
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir soundness from a transfer residual at the target languages, after first
transporting the state-restoration soundness hypothesis to those languages. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_languages
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn' langOut' soundnessError V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn' langOut'
    soundnessError V hTransfer
    (Verifier.StateRestoration.soundness.mono_languages srInit srImpl hSR hIn hOut)

/-- Basic Fiat-Shamir soundness from a transfer residual at the target languages/error, after first
transporting the state-restoration soundness hypothesis to those target parameters. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn' langOut' soundnessError₂ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError₂ := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn' langOut'
    soundnessError₂ V hTransfer
    (Verifier.StateRestoration.soundness.mono_languages_error srInit srImpl hSR hIn hOut
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target error, after first
relaxing the state-restoration knowledge-soundness hypothesis to that target error. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError₂ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError₂ := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn relOut
    knowledgeError₂ V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_error srInit srImpl hSR
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target relations, after
first transporting the state-restoration knowledge-soundness hypothesis to those relations. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn' relOut' knowledgeError V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir knowledgeError := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn' relOut'
    knowledgeError V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_relations srInit srImpl hSR hIn hOut)

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target relations/error,
after first transporting the state-restoration knowledge-soundness hypothesis to those target
parameters. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn' relOut' knowledgeError₂ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir
      knowledgeError₂ := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn' relOut'
    knowledgeError₂ V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_relations_error srInit srImpl hSR hIn hOut
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir soundness with both SR-side pretransport and FS-side posttransport around the
explicit state-restoration transfer residual. -/
theorem fiatShamir_soundness_of_stateRestoration_prepost_mono_languages_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langInSR langInTransfer langInFS : Set StmtIn}
    {langOutSR langOutTransfer langOutFS : Set StmtOut}
    {soundnessErrorSR soundnessErrorTransfer soundnessErrorFS : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langInTransfer langOutTransfer soundnessErrorTransfer V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langInSR langOutSR V soundnessErrorSR)
    (hInPre : langInSR ⊆ langInTransfer)
    (hOutPre : langOutTransfer ⊆ langOutSR)
    (hlePre : soundnessErrorSR ≤ soundnessErrorTransfer)
    (hInPost : langInTransfer ⊆ langInFS)
    (hOutPost : langOutFS ⊆ langOutTransfer)
    (hlePost : soundnessErrorTransfer ≤ soundnessErrorFS) :
    Verifier.soundness fsInit fsImpl langInFS langOutFS V.fiatShamir
      soundnessErrorFS := by
  classical
  have hMid :
      Verifier.soundness fsInit fsImpl langInTransfer langOutTransfer V.fiatShamir
        soundnessErrorTransfer :=
    fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
      srInit srImpl fsInit fsImpl V hTransfer hSR hInPre hOutPre hlePre
  have hLang :
      Verifier.soundness fsInit fsImpl langInFS langOutFS V.fiatShamir
        soundnessErrorTransfer :=
    Verifier.soundness.mono_languages fsInit fsImpl hMid hInPost hOutPost
  exact Verifier.soundness.mono_error fsInit fsImpl hLang hlePost

/-- Basic Fiat-Shamir knowledge soundness with both SR-side pretransport and FS-side posttransport
around the explicit state-restoration transfer residual. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_prepost_mono_relations_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relInSR relInTransfer relInFS : Set (StmtIn × WitIn)}
    {relOutSR relOutTransfer relOutFS : Set (StmtOut × WitOut)}
    {knowledgeErrorSR knowledgeErrorTransfer knowledgeErrorFS : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relInTransfer relOutTransfer knowledgeErrorTransfer V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relInSR relOutSR V knowledgeErrorSR)
    (hInPre : relInSR ⊆ relInTransfer)
    (hOutPre : relOutTransfer ⊆ relOutSR)
    (hlePre : knowledgeErrorSR ≤ knowledgeErrorTransfer)
    (hInPost : relInTransfer ⊆ relInFS)
    (hOutPost : relOutFS ⊆ relOutTransfer)
    (hlePost : knowledgeErrorTransfer ≤ knowledgeErrorFS) :
    Verifier.knowledgeSoundness fsInit fsImpl relInFS relOutFS V.fiatShamir
      knowledgeErrorFS := by
  classical
  have hMid :
      Verifier.knowledgeSoundness fsInit fsImpl relInTransfer relOutTransfer V.fiatShamir
        knowledgeErrorTransfer :=
    fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
      srInit srImpl fsInit fsImpl V hTransfer hSR hInPre hOutPre hlePre
  have hRel :
      Verifier.knowledgeSoundness fsInit fsImpl relInFS relOutFS V.fiatShamir
        knowledgeErrorTransfer :=
    Verifier.knowledgeSoundness.mono_relations fsInit fsImpl hMid hInPost hOutPost
  exact Verifier.knowledgeSoundness.mono_error fsInit fsImpl hRel hlePost

#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_error
#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_languages
#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
#print axioms fiatShamir_soundness_of_stateRestoration_prepost_mono_languages_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_prepost_mono_relations_error

end Reduction
