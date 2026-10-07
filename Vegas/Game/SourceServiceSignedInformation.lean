/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskExtension
import Vegas.Pending.ReactiveResponseRecall
import Interaction.ReactiveSubmissionSerial

/-! # One witnessed signed breach classifies a native information site

Own recall reconstructs the sender counter and, together with the current
view, the known packets. The same submission therefore emits the
same entire signed envelope at every hidden history of one information site.

A constructor breach witnessed at one such history consequently supplies the
information-local auditable classification used by collection. No new player
observation, menu gate, prescribed policy or global clear-history premise is
introduced.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Actual own recall and current view determine the entire next signed
envelope, including sender serial, even for arbitrary private material. -/
theorem sourceService_response_envelope_eq
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (left right : (serviceApplication setup mode deadline leaks).Execution) (who : Player)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup
      mode) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, left⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup
      mode) horizon scheduler).Trace
      (some ⟨rightRemaining, some who, right⟩))
    (past : left.recall who = right.recall who)
    (view : left.observe (serviceApplication setup mode deadline leaks) who =
      right.observe (serviceApplication setup mode deadline leaks) who) :
    (⟨(who, left.network.nextSerial who), (serviceApplication setup mode deadline leaks).packet
      ((serviceApplication setup mode deadline leaks).submit left.application who material) who
        (left.network.known who) material⟩ : Message Player (WitnessedPacket (serviceGraph setup
          mode))) =
      ⟨(who, right.network.nextSerial who), (serviceApplication setup mode deadline leaks).packet
        ((serviceApplication setup mode deadline leaks).submit right.application who material) who
          (right.network.known who) material⟩ := by
  let app := serviceApplication setup mode deadline leaks
  have leftRecall : left.InputRecall app :=
    app.history_inputRecall (serviceInitialLaw setup mode) horizon scheduler leftTrace
  have rightRecall : right.InputRecall app :=
    app.history_inputRecall (serviceInitialLaw setup mode) horizon scheduler rightTrace
  have known := (serviceRuntime setup mode deadline).known_eq_of_input_eq leaks left right who
    leftRecall rightRecall
    past view
  have packet := (serviceRuntime setup mode deadline).response_packet_eq_of_input_eq leaks left
    right who material
    view known
  have leftSerial : left.SerialRecall app :=
    app.serialRecall_history scheduler (serviceInitialLaw setup mode) horizon leftTrace
  have rightSerial : right.SerialRecall app :=
    app.serialRecall_history scheduler (serviceInitialLaw setup mode) horizon rightTrace
  have serial : left.network.nextSerial who = right.network.nextSerial who :=
    (leftSerial who).trans ((congrArg app.submissionCount past).trans (rightSerial who).symm)
  exact congrArg₂ Message.mk (congrArg (fun counter => (who, counter)) serial) packet

namespace AsyncServiceSpec

variable [Fintype Player]

variable (service : AsyncServiceSpec Player L)

/-- One actual constructor breach supplies the broader information-local
auditable classification. Legal recall reconstructs its signed envelope;
no uniform hidden-history breach premise is assumed. -/
theorem auditableBreachAtSite_of_signed_witness
    (who : Player)
    (site : ((service.bounds.riskMenu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks
      service.bound).information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).InformationSite who)
    (action : ((service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks).information
      (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).Choice who
        ((service.riskRestriction.site who site).1))
    (witness : ((service.bounds.riskMenu (serviceRuntime service.setup service.mode
      service.deadline) service.leaks
      service.bound).information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).InformationHistory who site.1)
    (remaining : Nat) (execution : (serviceApplication service.setup service.mode service.deadline
      service.leaks).Execution)
    (current : witness.1.state = some ⟨remaining, some who, execution⟩)
    (material : (serviceApplication service.setup service.mode service.deadline
      service.leaks).Submission)
    (selected : action.1 = some ⟨some material⟩)
    (breach : SignedContentBreach (⟨(who, execution.network.nextSerial who),
      (serviceApplication service.setup service.mode service.deadline service.leaks).packet
        ((serviceApplication service.setup service.mode service.deadline service.leaks).submit
          execution.application who material)
          who (execution.network.known who) material⟩ :
            Message Player (WitnessedPacket (serviceGraph service.setup service.mode)))) :
    service.auditableBreachAtSite who site action := by
  let app := serviceApplication service.setup service.mode service.deadline service.leaks
  let menu := service.bounds.riskMenu (serviceRuntime service.setup service.mode service.deadline)
    service.leaks service.bound
  have input : (service.riskRestriction.site who site).1 =
      some (execution.recall who, execution.observe app who) := by
    change site.1 = _
    calc
      site.1 = (menu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).infoOf who witness.1.trace := witness.2.symm
      _ = app.observe who witness.1.state :=
        menu.info (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler
          who witness.1.trace
      _ = some (execution.recall who, execution.observe app who) := by
        rw [current]
        simp only [ReactiveApplication.observe, ↓reduceIte]
  have rawTrace : (app.protocol (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ menu.toRawTrace (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler
      witness.1.trace
  refine Or.inl ⟨execution.recall who, execution.observe app who, ⟨some material⟩, input,
    selected, material, rfl, Or.inl ?_⟩
  rw [localEnvelope_actual rawTrace who material]
  exact breach

end AsyncServiceSpec
end Vegas
