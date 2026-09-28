/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMenu
import Vegas.Compile.EventGraphResolutionFields
import Vegas.Pending.ReactiveResolutionEvidence
import Vegas.Pending.ReactiveAssociationEvidence

/-! # Fresh full-source disclosures use owned certificate evidence

Source publication accounting gives each binding field one resolution event.
Actual retained histories associate every carried certificate with an earlier
owner response at that resolution. Thus an unsent resolution has no forwarding
alias for its own certificate, including for dynamically allocated bindings.
The resulting equality preserves the physical response in private recall.

The certificate and handle arguments use the existing ideal native ownership
capabilities. They do not add an authentication oracle, a key-sharing theorem,
or a restriction on the full raw target's actions.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every legal retained prefix has a genuine resolution origin for all known
certificates, independently of the prescribed source profile. -/
theorem sourceService_resolutionEvidence
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      horizon scheduler).Trace (some control)) :
    (runtime setup).ResolutionEvidenceOrigins leaks control.execution := by
  exact (runtime setup).resolutionEvidenceOrigins_history leaks bounds
    (sourceServiceMenu setup leaks bounds rosters)
    (sourceServiceMenu_in_compiled setup leaks bounds rosters) (initialLaw setup) horizon
    scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact State.initial_bindingInvariant (graph := graph setup) (setup.eventInputs initial)) trace

/-- The first opening of any source binding is already the exact native normal
form. No absence-of-evidence hypothesis is imposed on a source assessment. -/
theorem sourceService_opening_normal
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      horizon scheduler).Trace (some control))
    (event : (graph setup).EventId) (field : (graph setup).Field)
    (resolves : ((graph setup).nodes event).resolutionField? = some field)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (associated : control.execution.application.accepted field = some candidate)
    (owned : candidate.1 = who)
    (fixed : control.execution.application.candidates.lookup candidate = .openable raw)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false) :
    ((runtime setup).reactiveNormalization leaks).action who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)
        ((runtime setup).windowOpening leaks event candidate raw) =
      (runtime setup).windowOpening leaks event candidate raw := by
  have rawTrace := (sourceServiceMenu setup leaks bounds rosters).toRawTrace
    (initialLaw setup) horizon scheduler trace
  have valid := ((runtime setup).reactiveBindingInvariant leaks).history
    (initialLaw setup) horizon scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact State.initial_bindingInvariant (graph := graph setup) (setup.eventInputs initial))
    rawTrace
  have recalled := (application setup leaks).history_inputRecall
    (initialLaw setup) horizon scheduler rawTrace
  exact (sourceService_resolutionEvidence setup leaks bounds rosters horizon scheduler
    control trace).opening_normal (runtime setup) leaks
      (resolution_field_injective setup.program) control.execution valid recalled who event field
        resolves candidate raw associated owned fixed unsent

/-- Successful compiler disclosure at an actual fresh retained input equals
the raw owned-evidence response used by the scheduled opening window. -/
theorem sourceService_successful_opening
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      horizon scheduler).Trace (some control))
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (candidate : Handle (graph setup)) (value : L.Val payload)
    (associated : control.execution.application.accepted binding.field = some candidate)
    (resolved : EventCode.resolveOutput? binding checks true
      control.execution.application.config.store = some (.success value))
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false) :
    (runtime setup).serviceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event
        (cast (congrArg EventField.Action outputEq.symm) true) =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩ := by
  let app := application setup leaks
  have rawTrace := (sourceServiceMenu setup leaks bounds rosters).toRawTrace
    (initialLaw setup) horizon scheduler trace
  have valid := ((runtime setup).reactiveBindingInvariant leaks).history
    (initialLaw setup) horizon scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact State.initial_bindingInvariant (graph := graph setup) (setup.eventInputs initial))
    rawTrace
  have recalled := app.history_inputRecall (initialLaw setup) horizon scheduler rawTrace
  have stored := EventCode.binding_success_of_resolve_success binding checks true
    control.execution.application.config.store value resolved
  obtain ⟨actual, accepted, owned, fixed⟩ := valid.success_provenance binding value stored
  cases Option.some.inj (accepted.symm.trans associated)
  have resolves : ((graph setup).nodes event).resolutionField? = some binding.field := by
    have field := congrArg EventCode.resolutionField? codeEq
    rw [EventCode.resolutionField?_cast outputEq] at field
    exact field
  have normal := sourceService_opening_normal setup leaks bounds rosters horizon scheduler who
    control trace event binding.field resolves candidate ⟨payload, value⟩ associated owned fixed
      unsent
  have canonical := (runtime setup).serviceDecision_successful_opening leaks control.execution
    recalled who event payload binding checks outputEq codeEq node candidate value associated
      owned fixed resolved
  have known : ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
      (control.execution.observe app who) = control.execution.network.known who :=
    (app.known_from_recall control.execution who recalled).symm
  calc
    _ = ((runtime setup).reactiveNormalization leaks).action who
        (control.execution.recall who) (control.execution.observe app who)
          ((runtime setup).windowOpening leaks event candidate ⟨payload, value⟩) := by
      rw [canonical]
      change (⟨some (.submit
        ((disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
          who _ (control.execution.network.known who)))⟩ : app.Action) = _
      rw [← known]
      rfl
    _ = _ := normal

end Vegas
