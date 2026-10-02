/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskExtension
import Vegas.Pending.ReactiveResponseRecall
import Interaction.ReactiveSubmissionSerial

/-! # One witnessed signed breach classifies a native information site

Every legal initialized response history retains the same empty application
intention table. Own recall reconstructs the sender counter and, together with
the current view, the known packets. The same submission therefore emits the
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
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The reactive application never writes the intention table, including
arbitrary raw deviations and commands from the scheduler. -/
theorem sourceService_history_remembered_empty
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    control.execution.application.remembered = fun _ => none := by
  exact ((runtime setup).reactiveRememberedInvariant leaks
    (fun table => table = fun _ => none)).history (initialLaw setup) horizon scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl) trace

/-- Actual own recall and current view determine the entire next signed
envelope, including sender serial, even for arbitrary private material. -/
theorem sourceService_response_envelope_eq
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (left right : (application setup leaks).Execution) (who : Player)
    (material : (application setup leaks).Submission)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, left⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, some who, right⟩))
    (past : left.recall who = right.recall who)
    (view : left.observe (application setup leaks) who =
      right.observe (application setup leaks) who) :
    (⟨(who, left.network.nextSerial who), (application setup leaks).packet
      ((application setup leaks).submit left.application who material) who
        (left.network.known who) material⟩ : Message Player (WitnessedPacket (graph setup))) =
      ⟨(who, right.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit right.application who material) who
          (right.network.known who) material⟩ := by
  let app := application setup leaks
  have leftRecall : left.InputRecall app :=
    app.history_inputRecall (initialLaw setup) horizon scheduler leftTrace
  have rightRecall : right.InputRecall app :=
    app.history_inputRecall (initialLaw setup) horizon scheduler rightTrace
  have known := (runtime setup).known_eq_of_input_eq leaks left right who leftRecall rightRecall
    past view
  have remembered := (sourceService_history_remembered_empty setup leaks leftTrace).trans
    (sourceService_history_remembered_empty setup leaks rightTrace).symm
  have packet := (runtime setup).response_packet_eq_of_input_eq leaks left right who material
    view remembered known
  have leftSerial : left.SerialRecall app :=
    app.serialRecall_history scheduler (initialLaw setup) horizon leftTrace
  have rightSerial : right.SerialRecall app :=
    app.serialRecall_history scheduler (initialLaw setup) horizon rightTrace
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
    (site : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).information (initialLaw service.setup) service.horizon
        service.scheduler).InformationSite who)
    (action : ((service.bounds.menu (runtime service.setup) service.leaks).information
      (initialLaw service.setup) service.horizon service.scheduler).Choice who
        ((service.riskRestriction.site who site).1))
    (witness : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).information (initialLaw service.setup) service.horizon
        service.scheduler).InformationHistory who site.1)
    (remaining : Nat) (execution : (application service.setup service.leaks).Execution)
    (current : witness.1.state = some ⟨remaining, some who, execution⟩)
    (material : (application service.setup service.leaks).Submission)
    (selected : action.1 = some ⟨some material⟩)
    (breach : SignedContentBreach (⟨(who, execution.network.nextSerial who),
      (application service.setup service.leaks).packet
        ((application service.setup service.leaks).submit execution.application who material)
          who (execution.network.known who) material⟩ :
            Message Player (WitnessedPacket (graph service.setup)))) :
    service.auditableBreachAtSite who site action := by
  let app := application service.setup service.leaks
  let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
  have input : (service.riskRestriction.site who site).1 =
      some (execution.recall who, execution.observe app who) := by
    change site.1 = _
    calc
      site.1 = (menu.information (initialLaw service.setup) service.horizon
          service.scheduler).infoOf who witness.1.trace := witness.2.symm
      _ = app.observe who witness.1.state :=
        menu.info (initialLaw service.setup) service.horizon service.scheduler who witness.1.trace
      _ = some (execution.recall who, execution.observe app who) := by
        rw [current]
        simp only [ReactiveApplication.observe, ↓reduceIte]
  have rawTrace : (app.protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ menu.toRawTrace (initialLaw service.setup) service.horizon service.scheduler
      witness.1.trace
  refine ⟨execution.recall who, execution.observe app who, ⟨some material⟩, input, selected,
    material, rfl, Or.inl ?_⟩
  rw [localServiceEnvelope_actual service.setup service.leaks rawTrace who material]
  exact breach

end AsyncServiceSpec
end Vegas
