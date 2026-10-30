/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveProvenance
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveAllocation
import Interaction.ReactiveReceipts

/-! # Raw initialized service-history facts

Readiness, fixed binding meanings, authentic evidence, recall and packet identities follow
from the native operations at every initialized history. They require no reserved schedule,
source policy, factorization or successful public guards.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The initial native law is the image of the existing typed setup inputs. -/
theorem serviceInitialLaw_eq_inputs :
    serviceInitialLaw setup mode =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)) := by
  rw [PMF.map_comp]
  rfl

/-- The native facts used to transport acceptable recorded calls. -/
structure LegalFacts (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  stable : EntryStable (serviceRuntime setup mode deadline) leaks execution
  eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution
  storeStable : EntryStoreStable (serviceRuntime setup mode deadline) leaks execution
  binding : execution.application.BindingInvariant
  evidence : ((serviceRuntime setup mode deadline).packetEvidence leaks).Sound execution
  receipts : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True)
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  provenance : execution.Provenance (serviceApplication setup mode deadline leaks)
  inputs : execution.InputRecall (serviceApplication setup mode deadline leaks)
  quiescent : ∀ event, ¬ execution.application.AutomaticReady event

/-- Every initialized raw history supplies these facts under arbitrary responses and scheduler. -/
theorem legalFacts (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) :
    LegalFacts setup leaks control.execution := by
  let app := serviceApplication setup mode deadline leaks
  have nativeTrace := trace
  rw [serviceInitialLaw_eq_inputs setup] at nativeTrace
  have receipts := (app.receiptServiceInvariant (fun _ => True) (fun _ => True)
    ⟨by intros; trivial, by intros; trivial, by intros; trivial⟩
    (by intros; trivial) scheduler).history (serviceInitialLaw setup mode) horizon
      (fun state _ => ⟨trivial, app.receiptsSound_initial (fun _ => True) state⟩) trace
  exact {
    stable := entryStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    eventStable := entryEventStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    storeStable := entryStoreStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    binding := (serviceRuntime setup mode deadline).reactiveBindingInvariant_history leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace
    evidence := ((serviceRuntime setup mode deadline).packetEvidence leaks).history_sound
      (serviceInitialLaw setup mode) horizon scheduler trace
    receipts := receipts.2
    serials := app.serialsBeforeNext_history scheduler (serviceInitialLaw setup mode) horizon trace
    unique := app.uniqueIds_history scheduler (serviceInitialLaw setup mode) horizon control trace
    provenance := app.history_provenance (serviceInitialLaw setup mode) horizon scheduler trace
    inputs := app.history_inputRecall (serviceInitialLaw setup mode) horizon scheduler trace
    quiescent := (serviceRuntime setup mode deadline).reactive_history_quiescent leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace }

end Vegas
