/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDebtFreeResponse
import Vegas.Game.OnePacketCanonicalSafety
import Vegas.Game.OnePacketClearRegularity

/-! # First public failures exclude actual source-main counted responses

The argument depends on the native callback deadline and protected fresh-call
settlement facts. Concrete service contracts are supplied in separate adapters.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A source-main response cannot precede a public failure when its actual native
callback fits the original deadline and its recorded fresh calls settle. -/
theorem firstResponse_not_main_of_publicFailure_of_settles
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      (some (execution.recall who, execution.observe (application setup leaks) who)))
    (response : (application setup leaks).Action) (selected : choice.1 = some response)
    (after : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none,
        execution.respond (application setup leaks) who response⟩))
    (next : (application setup leaks).Execution)
    (settles : SettlesFreshCalls setup leaks who event bound next)
    (control : (application setup leaks).Control) (nextExecution : control.execution = next)
    (target : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (isPrefix : TracePrefix after target)
    (failed : next.application.PublicFailure event) :
    choice ∉ (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source who
      (some (execution.recall who, execution.observe (application setup leaks) who))).support := by
  intro supported
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal trace clear regular notOwed
  have forced : ForcedState setup leaks who (some ⟨remaining, some who, execution⟩) :=
    (forcedState_iff_decodedPoint _).mpr
      ⟨point, decoded, forcedPoint_of_intended who intended⟩
  have responderNotOwed : ∀ found, decodedPoint setup execution.application.config = some found →
      ¬ ProtocolState.OwesFailure who setup.program found := by
    intro found foundDecoded
    have same := Option.some.inj (decoded.symm.trans foundDecoded)
    subst found
    exact ProtocolState.Intended.not_owesFailure who setup.program point intended
  have turn := (pendingEvent_spec pending).1
  obtain ⟨action, material, chosen, submits, bindSuccess⟩ :=
    honestChoice_canonical_of_debtFree wellFormed covers capacity source trace who forced
      responderNotOwed event pending bound fits choice supported
  have sameResponse := Option.some.inj (selected.symm.trans chosen)
  subst response
  have safe := canonical_firstResponse_succeeds_of_settles bounds horizon scheduler bound trace
    event turn fits action material submits bindSuccess after control target isPrefix next
    nextExecution settles
  exact safe.2 failed


end Vegas
