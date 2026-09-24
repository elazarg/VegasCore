/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Communication
import Interaction.CommunicationHistory
import VegasTests.SequentialValidationHistories

/-! # Disclosure evidence without changing publication results

Instantiate the communication semantics with the actual deferred-guard source
game. Its failed opening still returns plain failure, while Bob receives
evidence of the binding. Every compatible extended history has that binding.
An additional legal history discloses it privately before any game commitment
or publication step.
-/

noncomputable section

namespace VegasTests.CommunicationDisclosure

open Vegas Vegas.SourceProgram Interaction Interaction.Communication
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open SequentialValidation

def channel := sourceSetup.communicationInterface sourceAdmission Bool

def secretFact (bit : Bool) : CommitmentEvidence Bool simpleExpr := ⟨false, 1, .bool, bit⟩
def dummyFact : CommitmentEvidence Bool simpleExpr := ⟨false, 3, .bool, false⟩

def publicHistory (bit : Bool) : (channel.protocol []).History :=
  channel.liftHistory (SourcePath.secretPublished bit (.success false) true true).history

theorem public_game_history (bit : Bool) :
    (publicHistory bit).state.history =
      (SourcePath.secretPublished bit (.success false) true true).history := rfl

/-- The exact existing source publication result is still failure. -/
theorem rejected_result (bit : Bool) :
    (secretConfig bit (.success false) true true).state.get .here = .failure := by
  rw [secret_publication]
  rfl

theorem public_transcript (bit : Bool) : (publicHistory bit).state.transcript =
    [⟨false, .broadcast, .evidence dummyFact⟩,
      ⟨false, .broadcast, .evidence (secretFact bit)⟩] := by
  simp [publicHistory, channel, CommunicationInterface.liftHistory,
    CommunicationInterface.liftedState, CommunicationInterface.emittedTranscript,
    SourcePath.history, SourcePath.trace, SourcePath.state, Setup.communicationInterface,
    Setup.disclosedEvidence, ProtocolState.disclosedEvidence, sourceProgram, sourceSetup,
    sourceJoint, OwnAction.disclosure, secretFact, dummyFact]
  rfl

theorem public_received (bit : Bool) (who : Bool) :
    ∃ message ∈ ((channel.informationModel []).infoOf who
      (publicHistory bit).trace).current.transcript,
      message.content = .evidence (secretFact bit) := by
  rw [channel.information_current]
  change ∃ message ∈ (publicHistory bit).state.transcript.observe who, _
  refine ⟨⟨false, .broadcast, .evidence (secretFact bit)⟩, ?_, rfl⟩
  rw [Transcript.mem_observe, public_transcript]
  exact ⟨by simp, Or.inr (Or.inl rfl)⟩

/-- Knowledge is a property of the complete information fiber. This includes
histories outside prescribed play and does not choose convenient beliefs. -/
theorem public_knows_binding (bit : Bool) (who : Bool) :
    (channel.informationModel []).Knows who
      ((channel.informationModel []).infoOf who (publicHistory bit).trace)
      (fun history => sourceSetup.evidenceValid history.state.history.state (secretFact bit)) :=
  channel.knows_of_received [] who _ (secretFact bit) (public_received bit who)

def privateStart : (channel.protocol [false]).History :=
  channel.communicateHistory [false] (channel.protocol [false]).initHistory
    false [] rfl (by exact id) none trivial

def privateDraw (bit : Bool) : (channel.protocol [false]).History :=
  channel.advanceHistory [false] privateStart rfl (fun _ => none) source_draw_legal
    (SourcePath.drawn bit).state (by
      change (SourcePath.drawn bit).state ∈ (sourceSetup.initialLaw.map _).support
      rw [FinDist.support_map]
      refine ⟨initialState bit, ?_, rfl⟩
      change initialState bit ∈ ((FinDist.uniformOfFintype (α := Bool)).map initialState).support
      rw [FinDist.support_map]
      exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩)

theorem private_draw_history (bit : Bool) :
    (privateDraw bit).state.history = (SourcePath.drawn bit).history := by
  simp [privateDraw, privateStart, CommunicationInterface.advanceHistory,
    CommunicationInterface.communicateHistory, History.extend,
    CommunicationInterface.advance, CommunicationInterface.communicate,
    SourcePath.history, SourcePath.trace, SourcePath.state, CommunicationInterface.protocol,
    initHistory]

theorem owner_can_disclose (bit : Bool) :
    channel.allowed false (channel.observe (privateDraw bit).state false)
      (.direct true, .evidence (secretFact bit)) := by
  change sourceSetup.possessesEvidence false
    (sourceModel.infoOf false (privateDraw bit).state.history.trace) (secretFact bit) ∨ _
  rw [private_draw_history]
  left
  have view : sourceModel.infoOf false (SourcePath.drawn bit).history.trace =
      some (.inl ((startConfig bit).view false)) :=
    sourceSetup.protocol_info sourceAdmission false (SourcePath.drawn bit).history.trace
  rw [view]
  exact ⟨rfl, .there .here, rfl⟩

/-- Alice supplies a certificate at a communication opportunity; she has not
executed the first source command yet. -/
def privateHistory (bit : Bool) : (channel.protocol [false]).History :=
  channel.communicateHistory [false] (privateDraw bit) false [] rfl (by exact id)
    (some (.direct true, .evidence (secretFact bit))) (owner_can_disclose bit)

theorem private_game_history (bit : Bool) :
    (privateHistory bit).state.history = (SourcePath.drawn bit).history :=
  private_draw_history bit

theorem private_transcript (bit : Bool) : (privateHistory bit).state.transcript =
    [⟨false, .direct true, .evidence (secretFact bit)⟩] := rfl

theorem private_received (bit : Bool) :
    ∃ message ∈ ((channel.informationModel [false]).infoOf true
      (privateHistory bit).trace).current.transcript,
      message.content = .evidence (secretFact bit) := by
  rw [channel.information_current]
  change ∃ message ∈ (privateHistory bit).state.transcript.observe true, _
  refine ⟨⟨false, .direct true, .evidence (secretFact bit)⟩, ?_, rfl⟩
  rw [Transcript.mem_observe, private_transcript]
  exact ⟨by simp, Or.inr (Or.inr rfl)⟩

theorem private_knows_binding (bit : Bool) :
    (channel.informationModel [false]).Knows true
      ((channel.informationModel [false]).infoOf true (privateHistory bit).trace)
      (fun history => sourceSetup.evidenceValid history.state.history.state (secretFact bit)) :=
  channel.knows_of_received [false] true _ (secretFact bit) (private_received bit)

def sourceType : sourceArena.State → Option Bool
  | none => none
  | some (.inl config) => some (config.state.get .here)
  | some (.inr (.inl config)) => some (config.state.get (.there .here))
  | some (.inr (.inr (.inl config))) => some (config.state.get (.there (.there .here)))
  | some (.inr (.inr (.inr (.inl config)))) =>
      some (config.state.get (.there (.there (.there .here))))
  | some (.inr (.inr (.inr (.inr config)))) =>
      some (config.state.get (.there (.there (.there (.there .here)))))

private theorem binding_identifies_type {Γ : SourceCtx Bool simpleExpr}
    (state : State simpleExpr Γ) (names : (Γ.map Prod.fst).Nodup)
    (ref : HasVar Γ 1 (.commitment false .bool)) (actual disclosed : Bool)
    (stored : state.get ref = .success actual)
    (known : (secretFact disclosed).Holds state) : actual = disclosed := by
  obtain ⟨other, value⟩ := known
  rw [HasVar.eq_of_nodup names other ref, stored] at value
  exact PublicationResult.success.inj value

/-- The setup correlation, rather than the certificate interface alone,
identifies the persistent private input. -/
theorem certificate_identifies_type (history : sourceArena.History) (bit : Bool)
    (known : sourceSetup.evidenceValid history.state (secretFact bit)) :
    sourceType history.state = some bit := by
  obtain ⟨path, same⟩ := source_history_complete history.trace
  change history = path.history at same
  subst history
  cases path with
  | root => exact known.elim
  | drawn actual =>
      exact congrArg some (binding_identifies_type (startConfig actual).state (by decide)
        (.there .here) actual bit rfl known)
  | bound actual dummy =>
      exact congrArg some (binding_identifies_type (boundConfig actual dummy).state (by decide)
        (.there (.there .here)) actual bit rfl known)
  | dummyPublished actual dummy first =>
      exact congrArg some (binding_identifies_type (dummyConfig actual dummy first).state
        (by decide) (.there (.there (.there .here))) actual bit rfl known)
  | secretPublished actual dummy first second =>
      exact congrArg some (binding_identifies_type (secretConfig actual dummy first second).state
        (by decide) (.there (.there (.there (.there .here)))) actual bit rfl known)
  | done actual dummy first second guess =>
      exact congrArg some (binding_identifies_type
        (finalConfig actual dummy first second guess).state (by decide)
        (.there (.there (.there (.there (.there .here))))) actual bit rfl known)

/-- At either a private or public certificate observation, no belief can retain
the old uniform uncertainty about the bit. -/
theorem belief_type (roster : List Bool) (who bit : Bool)
    (view : (channel.informationModel roster).InfoState who)
    (received : ∃ message ∈ view.current.transcript, message.content = .evidence (secretFact bit))
    (belief : FinDist ((channel.informationModel roster).InformationHistory who view)) :
    belief.map (fun history => sourceType history.1.state.history.state) =
      FinDist.pure (some bit) := by
  have known := channel.knows_of_received roster who view (secretFact bit) received
  have typed := known.mono (fun history evidence =>
    certificate_identifies_type history.state.history bit evidence)
  exact typed.belief_map_eq_pure _ _ belief

/-- The bound is for every legal play, including arbitrary communication. -/
theorem finite_horizon : (channel.protocol [false, true]).BoundedHorizon 15 :=
  channel.bounded [false, true] 5 (sourceSetup.protocol_bounded sourceAdmission)

end VegasTests.CommunicationDisclosure
