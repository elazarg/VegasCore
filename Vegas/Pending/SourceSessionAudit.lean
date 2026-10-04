/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.SourceSession
import Vegas.Pending.ReactiveSettledVerdict
import Interaction.ReactiveReceipts

/-! # Public misconduct verdicts and native report settlement

Canonical contents and historical phase evidence are checked against the
sealed public source record. A missing phase token is forbidden even when
cancellation leaves its event unfinished. Two distinct signed identifiers
for one author and phase establish equivocation. Lateness alone is not a
signed offense.

Settlement reads only the bodies of accepted watcher reports in the public
ledger, using the runner's actual receipts. Each source player pays at most
one misconduct fine. Observation and timely report inclusion remain service
obligations; settlement neither samples evidence nor reads unseen traffic.
-/

noncomputable section

namespace Vegas.SourceSession

open Interaction GameTheory.Math.Probability EventGraph
open EventGraphRuntime (Raw nodeView)

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [R : IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Validity of the attached historical credential, independent of whether
its phase is still active at settlement. Provenance comes from `emit`. -/
def GamePacket.tokenValid (packet : GamePacket graph) : Bool :=
  packet.call.phase?.any fun phase => packet.token = some phase

/-- Canonical source wire contents, checked without private candidates,
send time, current authorization or accepting gameplay receipts. -/
def PublicView.permitsGamePacket (view : PublicView graph) (who : Player)
    (packet : GamePacket graph) : Bool :=
  packet.tokenValid && match packet.call with
  | .binding event handle =>
      match nodeView graph event with
      | .bind owner .. => decide (who = owner ∧
          handle = (owner, .prepared (view.source.bindingCountBefore who event)) ∧
          packet.certificates = [])
      | .resolve .. | .sample .. => false
  | .admission event handle =>
      match nodeView graph event with
      | .resolve owner .. =>
          decide (who = owner ∧ handle = (owner, event) ∧ packet.certificates = [])
      | .bind .. | .sample .. => false
  | .opening event handle raw =>
      match nodeView graph event with
      | .resolve owner payload binding checks .. =>
          decide (who = owner ∧ handle = (owner, event) ∧
            (view.admissions event).map Admission.handle = some handle) &&
          (view.openingDecision? owner payload binding checks handle raw
            packet.certificates).isSome
      | .bind .. | .sample .. => false
  | .giveUp (.source event kind) =>
      match nodeView graph event, kind with
      | .bind owner .., .binding
      | .resolve owner .., .admission
      | .resolve owner .., .opening => decide (who = owner ∧ packet.certificates = [])
      | _, _ => false
  | .giveUp .reporting | .malformed _ => false

/-- Source players cannot use the reporter's wire format for communication. -/
def PublicView.permitsPacket (view : PublicView graph) (who : Player) : Packet graph → Bool
  | .gameplay packet => view.permitsGamePacket who packet
  | .report .. => false

def Packet.phase? : Packet graph → Option (PhaseKey graph)
  | .gameplay packet => packet.call.phase?
  | .report .. => some .reporting

/-- Different native phases of one source event do not form a duplicate pair.
Repeating the same signed identifier is not a second authored packet. -/
def equivocation (first second : Message (Principal Player) (Packet graph)) : Bool :=
  decide (first.sender = second.sender ∧ first.id ≠ second.id) &&
    first.payload.phase?.any fun phase => second.payload.phase? = some phase

/-- The collected misconduct charge is a Boolean, so additional witnesses
cannot replenish or multiply an already collected fine. -/
def misconductCharge (view : PublicView graph)
    (evidence : List (Message (Principal Player) (Packet graph))) (who : Player) : Bool :=
  evidence.any (fun message =>
    decide (message.sender = .player who) && !view.permitsPacket who message.payload) ||
  evidence.any (fun first => decide (first.sender = .player who) &&
    evidence.any (fun second => equivocation first second))

/-- Only an actually accepted watcher report contributes its signed bodies. -/
def acceptedReportEvidence (message : Message (Principal Player) (Packet graph))
    (accepted : Bool) : List (Message (Principal Player) (Packet graph)) :=
  if accepted = true ∧ message.sender = .watcher then
    match message.payload with
    | .report evidence _ => evidence
    | .gameplay _ => []
  else []

/-- Public ledger positions are paired with the runner's actual receipts. -/
def reportedEvidence (ledger : List (Message (Principal Player) (Packet graph)))
    (receipts : List (MessageId (Principal Player) × Bool)) :
    List (Message (Principal Player) (Packet graph)) :=
  (ledger.zip receipts).flatMap fun entry => acceptedReportEvidence entry.1 entry.2.2

/-- The cancellation vector already includes the public cancellation
deduction. Misconduct is collected once from the same upfront escrow. -/
def settlement (normal : graph.Outcome → Player → ℝ) (cancelled fine : Player → ℝ)
    (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution) : Principal Player → ℝ
  | .player who => State.baseUtility normal cancelled execution.application (.player who) -
      if misconductCharge execution.application.publicView
        (reportedEvidence execution.network.ledger execution.receipts) who then fine who else 0
  | .watcher => 0

theorem GamePacket.tokenValid_eq_false_of_none (packet : GamePacket graph)
    (missing : packet.token = none) : packet.tokenValid = false := by
  cases named : packet.call.phase? <;> simp [tokenValid, named, missing]

/-- This verdict persists through cancellation without requiring the
addressed source event to complete. -/
theorem PublicView.permitsGamePacket_eq_false_of_invalid_token
    (view : PublicView graph) (who : Player) (packet : GamePacket graph)
    (invalid : packet.tokenValid = false) : view.permitsGamePacket who packet = false := by
  simp only [permitsGamePacket, invalid, Bool.false_and]

theorem misconductCharge_of_unary (view : PublicView graph)
    (evidence : List (Message (Principal Player) (Packet graph))) (who : Player)
    (message : Message (Principal Player) (Packet graph)) (present : message ∈ evidence)
    (authored : message.sender = .player who)
    (forbidden : view.permitsPacket who message.payload = false) :
    misconductCharge view evidence who = true := by
  apply Bool.or_eq_true_iff.mpr
  exact Or.inl (List.any_eq_true.mpr ⟨message, present, by simp [authored, forbidden]⟩)

theorem misconductCharge_of_pair (view : PublicView graph)
    (evidence : List (Message (Principal Player) (Packet graph))) (who : Player)
    (first second : Message (Principal Player) (Packet graph))
    (first_present : first ∈ evidence) (second_present : second ∈ evidence)
    (authored : first.sender = .player who) (duplicate : equivocation first second = true) :
    misconductCharge view evidence who = true := by
  apply Bool.or_eq_true_iff.mpr
  exact Or.inr (List.any_eq_true.mpr ⟨first, first_present, by
    simp only [authored, decide_true, Bool.true_and]
    exact List.any_eq_true.mpr ⟨second, second_present, duplicate⟩⟩)

@[simp] theorem misconductCharge_nil (view : PublicView graph) (who : Player) :
    misconductCharge view [] who = false := rfl

@[simp] theorem reportedEvidence_nil :
    reportedEvidence (graph := graph) [] [] = [] := rfl

theorem reportedEvidence_append (ledger : List (Message (Principal Player) (Packet graph)))
    (receipts : List (MessageId (Principal Player) × Bool))
    (aligned : ledger.length = receipts.length)
    (message : Message (Principal Player) (Packet graph))
    (receipt : MessageId (Principal Player) × Bool) :
    reportedEvidence (ledger ++ [message]) (receipts ++ [receipt]) =
      reportedEvidence ledger receipts ++ acceptedReportEvidence message receipt.2 := by
  simp [reportedEvidence, List.zip_append aligned]

@[simp] theorem settlement_watcher (normal : graph.Outcome → Player → ℝ)
    (cancelled fine : Player → ℝ) (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution) :
    settlement normal cancelled fine runtime leaks execution .watcher = 0 := rfl

private theorem finish_report (state : State graph) : state.finish.report = state.report := by
  unfold State.finish
  split <;> rfl

private theorem openDecision_report (state next : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (handle : DecisionHandle graph) (raw : Raw L) (certificates : List (Certificate graph))
    (accepted : openDecision state event ready owner payload binding checks outputEq
      handle raw certificates = some next) : next.report = state.report := by
  unfold openDecision at accepted
  cases decoded : state.publicView.openingDecision? owner payload binding checks
      handle raw certificates with
  | none => simp [decoded] at accepted
  | some result =>
      simp only [decoded, Option.bind_eq_bind, Option.pure_def,
        Option.bind_some, Option.some.injEq] at accepted
      subst next
      rfl

private theorem handleGame_report (runtime : Runtime graph) (state next : State graph)
    (id : MessageId (Principal Player)) (packet : GamePacket graph)
    (accepted : handleGame runtime state id packet = some next) :
    next.report = state.report := by
  rcases packet with ⟨call, certificates, token⟩
  cases call with
  | binding event handle =>
      simp only [handleGame, Call.phase?, Option.bind_eq_bind,
        Option.pure_def, Option.bind_some] at accepted
      split at accepted
      · split at accepted
        · cases node : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              simp only [node] at accepted
              split at accepted
              · cases Option.some.inj accepted
                exact finish_report _
              · cases accepted
          | resolve owner payload binding checks outputEq codeEq => simp [node] at accepted
          | sample payload value outputEq codeEq => simp [node] at accepted
        · cases accepted
      · cases accepted
  | admission event handle =>
      simp only [handleGame, Call.phase?, Option.bind_eq_bind,
        Option.bind_some] at accepted
      split at accepted
      · cases node : nodeView graph event with
        | resolve owner payload binding checks outputEq codeEq =>
            simp only [node] at accepted
            split at accepted
            · cases Option.some.inj accepted
              rfl
            · cases accepted
        | bind owner payload outputEq codeEq => simp [node] at accepted
        | sample payload value outputEq codeEq => simp [node] at accepted
      · cases accepted
  | opening event handle raw =>
      simp only [handleGame, Call.phase?, Option.bind_eq_bind,
        Option.pure_def, Option.bind_some] at accepted
      split at accepted
      · split at accepted
        · rename_i ready
          cases node : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [node] at accepted
              split at accepted
              · cases opened : openDecision state event ready owner payload binding checks
                  outputEq handle raw certificates with
                | none => simp [opened] at accepted
                | some middle =>
                    simp only [opened, Option.bind_some, Option.some.injEq] at accepted
                    subst next
                    rw [finish_report]
                    exact openDecision_report state middle event ready owner payload binding
                      checks outputEq handle raw certificates opened
              · cases accepted
          | bind owner payload outputEq codeEq => simp [node] at accepted
          | sample payload value outputEq codeEq => simp [node] at accepted
        · cases accepted
      · cases accepted
  | giveUp phase =>
      simp only [handleGame, Call.phase?, Option.bind_eq_bind,
        Option.pure_def, Option.bind_some] at accepted
      split at accepted
      · cases phase with
        | reporting => cases accepted
        | source event kind =>
            cases node : nodeView graph event with
            | bind owner payload outputEq codeEq
            | resolve owner payload binding checks outputEq codeEq =>
                simp only [node] at accepted
                split at accepted
                · cases Option.some.inj accepted
                  rfl
                · cases accepted
            | sample payload value outputEq codeEq => simp [node] at accepted
      · cases accepted
  | malformed raw => simp [handleGame, Call.phase?] at accepted

private theorem reporting_token_clear (state : State graph)
    (ready : state.tokenFor .reporting = some .reporting) : state.report = none := by
  simp only [State.tokenFor] at ready
  split at ready
  · rename_i allowed
    exact Option.isNone_iff_eq_none.mp allowed.2
  · cases ready

private theorem environment_report (runtime : Runtime graph) (state next : State graph)
    (command : EnvironmentCommand graph)
    (reached : next ∈ (environment runtime state command).support) :
    next.report.getD [] = state.report.getD [] := by
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | executeSample event =>
      simp only [environment] at reached
      split at reached
      · obtain ⟨source, _, rfl⟩ := PMF.support_map .. ▸ reached
        rw [finish_report]
      · cases (PMF.mem_support_pure_iff _ _).mp reached
        rfl
  | expire phase =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      split
      · rename_i due
        cases phase with
        | source event kind => rfl
        | reporting => simp [reporting_token_clear state due.1]
      · rfl

private def ReportRecord (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution) : Prop :=
  execution.ReceiptsSound (application runtime leaks) (fun _ => True) ∧
    execution.application.report.getD [] =
      (reportedEvidence execution.network.ledger execution.receipts).map Message.id

private theorem reportRecord_includePending (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution) (id : MessageId (Principal Player))
    (valid : ReportRecord runtime leaks execution) :
    ReportRecord runtime leaks (execution.includePending (application runtime leaks) id) := by
  refine ⟨(application runtime leaks).receiptsSound_includePending (fun _ => True)
    execution id valid.1 (fun _ _ _ => trivial), ?_⟩
  have aligned : execution.network.ledger.length = execution.receipts.length := valid.1.length_eq
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact valid.2
  | some message =>
      change ((handle runtime execution.application message).getD
        execution.application).report.getD [] =
        (reportedEvidence (execution.network.ledger ++ [message])
          (execution.receipts ++ [(id, (handle runtime execution.application message).isSome)])).map
            Message.id
      rw [reportedEvidence_append _ _ aligned]
      cases accepted : handle runtime execution.application message with
      | none => simpa [acceptedReportEvidence] using valid.2
      | some next =>
          cases body : message.payload with
          | gameplay packet =>
              have preserved := handleGame_report runtime execution.application next
                message.id packet
                (by simpa [handle, body] using accepted)
              simpa [acceptedReportEvidence, body, preserved] using valid.2
          | report evidence token =>
              simp only [handle, body] at accepted
              split at accepted
              · rename_i allowed
                obtain ⟨authored, _, ready, _⟩ := allowed
                have clear := reporting_token_clear execution.application ready
                have empty : reportedEvidence execution.network.ledger execution.receipts = [] := by
                  simpa [clear] using valid.2.symm
                cases Option.some.inj accepted
                simp [acceptedReportEvidence, authored, body, empty]
              · cases accepted

private theorem reportServiceInvariant (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (scheduler : (application runtime leaks).Scheduler) :
    (application runtime leaks).ServiceInvariant scheduler (ReportRecord runtime leaks) where
  respond execution who action valid := by
    refine ⟨(application runtime leaks).receiptsSound_respond (fun _ => True)
      execution who action valid.1, ?_⟩
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid.2
    | some submission =>
        change (submit execution.application who submission).report.getD [] =
          (reportedEvidence execution.network.ledger execution.receipts).map Message.id
        have same := congrArg PublicView.report
          (submit_publicView execution.application who submission)
        change (submit execution.application who submission).report = execution.application.report
          at same
        rw [same]
        exact valid.2
  environment execution next command valid _ reached := by
    cases command with
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact valid
    | activate who =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact valid
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact reportRecord_includePending runtime leaks execution id valid
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ supported
        refine ⟨valid.1, ?_⟩
        change state.report.getD [] = _
        rw [environment_report runtime execution.application state command moved]
        exact valid.2

/-- At every initialized native history, the contract's recorded report IDs
are exactly those carried by its actual accepted watcher report. Expired or
absent reports contribute no evidence. No honest-play or coverage premise is
needed to identify the settlement mechanism. -/
theorem history_reportedEvidence (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (application runtime leaks).Scheduler)
    (control : (application runtime leaks).Control)
    (trace : ((application runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) :
    control.execution.application.report.getD [] =
      (reportedEvidence control.execution.network.ledger control.execution.receipts).map
        Message.id := by
  have valid := (reportServiceInvariant runtime leaks scheduler).history
    (inputs.map State.initial) horizon (by
      intro state supported
      obtain ⟨setup, _, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨ReactiveApplication.receiptsSound_initial _ _ _, ?_⟩
      change (State.initial setup).report.getD [] = []
      rw [State.initial, finish_report]
      rfl) trace
  exact valid.2

/-- Before report acceptance, and after a reporting timeout, known or pending
offenses alone cannot produce a settlement charge. -/
theorem history_reportedEvidence_eq_nil (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (application runtime leaks).Scheduler)
    (control : (application runtime leaks).Control)
    (trace : ((application runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (empty : control.execution.application.report.getD [] = []) :
    reportedEvidence control.execution.network.ledger control.execution.receipts = [] := by
  simpa only [empty, List.map_eq_nil_iff] using
    (history_reportedEvidence runtime leaks inputs horizon scheduler control trace).symm

end Vegas.SourceSession
