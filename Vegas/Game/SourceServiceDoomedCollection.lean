/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAuditableCollection

/-! # Responses that doom their author, and their collection

A transmitting response that is not a conformant first submission dooms its
author: either its envelope, which own recall and the current view
reconstruct, fails the public send-time check, and the breach machinery marks
the author; or it is a second call for an event the author has already
called, and the two emitted identifiers for one event mark the author. The
classification reads only the owner's recall, view and chosen response.

A doomed author stays doomed under every later response and scheduler command,
and every complete settlement then forbids some actual packet of that author,
so authentic final-record coverage bounds the collection after committing such
a response, under arbitrary later policies.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section Emissions

variable (setup leaks) in
/-- Every recorded submission emitted an envelope carrying its call. -/
def RecalledEmissions (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ material, entry.action.transmission = some material →
    ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet

theorem recalledEmissions_respond
    (execution : (serviceApplication setup mode deadline leaks).Execution) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action)
    (valid : RecalledEmissions setup leaks execution) :
    RecalledEmissions setup leaks
      (execution.respond (serviceApplication setup mode deadline leaks) who action) := by
  intro observer entry member material sent
  by_cases same : observer = who
  · subst observer
    rcases action with ⟨transmission⟩
    cases transmission with
    | none =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
          List.mem_singleton] at member
        rcases member with prior | rfl
        · exact valid _ entry prior material sent
        · cases sent
    | some chosen =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
          List.mem_singleton] at member
        rcases member with prior | rfl
        · exact valid _ entry prior material sent
        · cases Option.some.inj sent
          exact ⟨_, rfl, rfl⟩
  · rw [(serviceApplication setup mode deadline leaks).respond_recall_other execution who
      observer same action] at member
    exact valid observer entry member material sent

variable (setup leaks) in
theorem recalledEmissionsInvariant
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) :
    (serviceApplication setup mode deadline leaks).ServiceInvariant scheduler
      (RecalledEmissions setup leaks) where
  respond execution who action valid := recalledEmissions_respond execution who action valid
  environment execution next command valid _ reached := by
    intro who entry member
    rw [(serviceApplication setup mode deadline leaks).environmentStep_recall execution next
      command reached] at member
    exact valid who entry member

/-- At every legal history every recorded submission emitted an envelope with
its call, under arbitrary responses and every scheduler. -/
theorem history_recalledEmissions {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) :
    RecalledEmissions setup leaks control.execution :=
  (recalledEmissionsInvariant setup leaks scheduler).history (serviceInitialLaw setup mode)
    horizon (fun _ _ _ _ member => False.elim (List.not_mem_nil member)) trace

/-- A recalled call for an event left an emitted envelope of its author naming
that event. -/
theorem recalled_call_emitted {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (control.execution.recall who) event = true) :
    ∃ message, Emitted setup leaks control.execution message ∧ message.sender = who ∧
      message.payload.call.event? (serviceGraph setup mode) = some event := by
  let app := serviceApplication setup mode deadline leaks
  unfold EventGraphRuntime.eventRecorded at recorded
  obtain ⟨entry, member, named⟩ := List.any_eq_true.mp recorded
  have named : (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action =
      some event := of_decide_eq_true named
  cases sent : entry.action.transmission with
  | none =>
      simp only [EventGraphRuntime.submittedEvent?, sent, reduceCtorEq] at named
  | some material =>
      simp only [EventGraphRuntime.submittedEvent?, sent] at named
      obtain ⟨message, emitted, call⟩ := history_recalledEmissions trace who entry member
        material sent
      have input : control.execution.InputRecall app :=
        app.history_inputRecall (serviceInitialLaw setup mode) horizon scheduler trace
      have output : message ∈ app.outputs (control.execution.recall who) :=
        List.mem_filterMap.mpr ⟨entry, member, emitted⟩
      rw [← input who] at output
      obtain ⟨carried, authored⟩ := List.mem_filter.mp output
      refine ⟨message, carried, of_decide_eq_true authored, ?_⟩
      rw [call]
      exact named

end Emissions

section Doom

/-- The response transmits, and is not a conformant first submission. -/
def DoomingResponse (who : Player)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (response : (serviceApplication setup mode deadline leaks).Action) : Prop :=
  (∃ material, response.transmission = some material) ∧
    ¬ (serviceRuntime setup mode deadline).ConformantResponse leaks who past view response

/-- **A nonconformant transmission dooms its author.** At every legal active
history, a transmitting response that is not a conformant first submission
leaves its author doomed: a second call for a recorded event leaves two
identifiers for that event, and a failed send-time check is a breach. -/
theorem respond_doomed {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {execution : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩))
    (response : (serviceApplication setup mode deadline leaks).Action)
    (dooming : DoomingResponse who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) response) :
    Doomed setup leaks (execution.respond (serviceApplication setup mode deadline leaks) who
      response) who := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨⟨material, sent⟩, nonconformant⟩ := dooming
  have facts := settledFacts_history (serviceInitialLaw setup mode) horizon scheduler trace
  let message : Message Player (WitnessedPacket (serviceGraph setup mode)) :=
    ⟨(who, execution.network.nextSerial who), app.packet
      (app.submit execution.application who material) who (execution.network.known who)
        material⟩
  have responseEq : response = ⟨some material⟩ := by
    cases response with
    | mk transmission =>
        change transmission = some material at sent
        cases sent
        rfl
  subst responseEq
  have emitted : Emitted setup leaks (execution.respond app who ⟨some material⟩) message := by
    unfold Emitted
    simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit, List.mem_append,
      List.mem_singleton]
    exact Or.inr rfl
  have envelope := localEnvelope_actual trace who material
  by_cases first : (serviceRuntime setup mode deadline).firstSubmission leaks
      (execution.recall who) ⟨some material⟩ = true
  · have breach : ¬ (serviceRuntime setup mode deadline).freshServiceEnvelope
        execution.application.publicView message := by
      intro fresh
      apply nonconformant
      refine ⟨material, rfl, first, ?_⟩
      change (serviceRuntime setup mode deadline).freshServiceEnvelope
        (execution.observe app who).application.publicView _
      rw [envelope]
      exact fresh
    have unpublished : message.id ∉ execution.network.ledger.map Message.id := by
      intro published
      obtain ⟨other, member, same⟩ := List.mem_map.mp published
      have bound := facts.serials.ledger other member
      rw [same] at bound
      exact Nat.lt_irrefl _ bound
    have rejected : (serviceRuntime setup mode deadline).permittedServiceEnvelope
        execution.application.publicView execution.network.ledger message = false := by
      apply Bool.eq_false_of_not_eq_true
      intro permitted
      exact breach (((serviceRuntime setup mode deadline).permittedServiceEnvelope_unpublished_iff
        _ _ message unpublished).mp permitted).2
    exact doomed_of_breach execution facts who ⟨some material⟩ message emitted rejected
  · obtain ⟨event, named, recorded⟩ : ∃ event,
        material.call.packet.event? (serviceGraph setup mode) = some event ∧
        (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who) event =
          true := by
      cases addressed : material.call.packet.event? (serviceGraph setup mode) with
      | none =>
          exfalso
          apply first
          simp only [EventGraphRuntime.firstSubmission, EventGraphRuntime.submittedEvent?,
            addressed]
      | some event =>
          refine ⟨event, rfl, ?_⟩
          simp only [EventGraphRuntime.firstSubmission, EventGraphRuntime.submittedEvent?,
            addressed, Bool.not_eq_eq_eq_not, Bool.not_true] at first
          exact Bool.eq_true_of_not_eq_false first
    obtain ⟨earlier, earlierEmitted, earlierSender, earlierNamed⟩ :=
      recalled_call_emitted trace who event recorded
    have below := facts.emitted_serial earlierEmitted
    rw [show earlier.id.1 = who from earlierSender] at below
    refine ⟨message, emitted, rfl, Or.inr ⟨earlier, respond_emitted_mono execution who _
      earlierEmitted, earlierSender, fun same => ?_, event, named, earlierNamed⟩⟩
    rw [same] at below
    exact Nat.lt_irrefl _ below

/-- Doom of `who` together with the facts that carry it forward. -/
def DoomedAt (who : Player) :
    (serviceApplication setup mode deadline leaks).ProtocolState → Prop
  | none => False
  | some control => SettledFacts setup leaks control.execution ∧
      Doomed setup leaks control.execution who ∧ ActivationKept control.execution.application

theorem doomedAt_transition {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} (who : Player)
    (before after : (serviceApplication setup mode deadline leaks).ProtocolState)
    (joint : Player → Option (serviceApplication setup mode deadline leaks).Action)
    (held : DoomedAt who before)
    (reached : after ∈ ((serviceApplication setup mode deadline leaks).transition
        (serviceInitialLaw setup mode) horizon scheduler before joint).support) :
    DoomedAt who after := by
  cases before with
  | none => exact held.elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      obtain ⟨facts, doomed, kept⟩ := held
      cases actor with
      | some responder =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact ⟨settledFacts_respond execution facts responder _, doomed.respond responder _,
            activationKept_respond execution responder _ kept⟩
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact ⟨facts, doomed, kept⟩
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              exact ⟨settledFacts_environment execution next command facts supported,
                doomed.environment facts supported kept,
                (environmentStep_handlerTables supported).2.2.2 kept⟩

theorem doomedAt_reaches {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} (who : Player)
    {first last : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).History} {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin fuel first last)
    (held : DoomedAt who first.state) : DoomedAt who last.state := by
  induction path with
  | refl => exact held
  | step joint legal reached rest ih =>
      exact ih (doomedAt_transition who _ _ joint held reached)

/-- At every complete settlement reachable after a doomed state, some actual
packet of the doomed author is forbidden. -/
theorem doomedAt_forbidden_reaches {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} (who : Player)
    {first last : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).History} {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin fuel first last)
    (held : DoomedAt who first.state)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (lastState : last.state = some control)
    (lastTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (complete : control.execution.application.config.cut.Terminal) :
    ∃ record ∈ (serviceApplication setup mode deadline leaks).executionTraffic
        control.execution,
      record.envelope.sender = who ∧
      ((serviceRuntime setup mode deadline).settledRecord leaks control.execution).permits
        record.envelope = false := by
  have final := doomedAt_reaches who path held
  rw [lastState] at final
  obtain ⟨facts, doomed, _⟩ := final
  obtain ⟨message, emitted, authored, forbidden⟩ := doomed.forbidden facts complete
  have inputs := (serviceApplication setup mode deadline leaks).stateTraffic_inputs
    (serviceInitialLaw setup mode) horizon scheduler lastTrace
  have inputMember : message ∈ control.execution.network.inputs := emitted
  change ((serviceApplication setup mode deadline leaks).executionTraffic
    control.execution).map ReactiveApplication.TrafficRecord.envelope =
      control.execution.network.inputs at inputs
  rw [← inputs] at inputMember
  obtain ⟨record, recordMember, rfl⟩ := List.mem_map.mp inputMember
  exact ⟨record, recordMember, authored, forbidden⟩

end Doom

section Collection

variable [Fintype Player]

variable (setup leaks) in
/-- The dooming classification of one information state and available choice.
Its response and all data used to classify it are owner-local. -/
def doomingServiceChoice (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (who : Player)
    (info : (menu.information (serviceInitialLaw setup mode) horizon scheduler).InfoState who)
    (choice : (menu.information (serviceInitialLaw setup mode) horizon scheduler).Choice who
      info) : Prop :=
  ∃ past view response, info = some (past, view) ∧ choice.1 = some response ∧
    DoomingResponse who past view response

open Classical in
/-- Committing an information-local dooming choice gives the final-record
backend's collection bound under arbitrary later policies. -/
theorem doomingServiceChoice_collection_committed
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (completes : CompletesPlay (serviceRuntime setup mode deadline) leaks (serviceInitialLaw setup
      mode) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup mode))
    (profile : ∀ player,
      (menu.information (serviceInitialLaw setup mode) horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol (serviceInitialLaw setup mode) horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : (serviceApplication setup mode deadline
      leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information (serviceInitialLaw setup mode) horizon scheduler).InfoState who)
    (choice : (menu.information (serviceInitialLaw setup mode) horizon scheduler).Choice who info)
    (observed : (menu.information (serviceInitialLaw setup mode) horizon scheduler).infoOf who
      history.trace = info)
    (classified : doomingServiceChoice setup leaks menu horizon scheduler who info choice)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information (serviceInitialLaw setup mode) horizon
        scheduler).runBehavioralTerminalFrom
        (menu.bounded (serviceInitialLaw setup mode) horizon scheduler).wellFoundedHistories
        (Profile.update
          (sig := (menu.information (serviceInitialLaw setup mode) horizon
            scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge ((serviceRuntime setup mode
          deadline).serviceAuditObservation leaks)
          (serviceSourceAudit setup mode deadline leaks backend.sample) final.state who) := by
  classical
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨past, view, response, inputEq, chosen, dooming⟩ := classified
  have observedInput : info = app.observe who history.state :=
    observed.symm.trans (menu.info (serviceInitialLaw setup mode) horizon scheduler who
      history.trace)
  rw [current] at observedInput
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedInput
  have same := Option.some.inj (inputEq.symm.trans observedInput)
  have pastEq := congrArg Prod.fst same
  have viewEq := congrArg Prod.snd same
  dsimp only at pastEq viewEq
  rw [pastEq, viewEq] at dooming
  obtain ⟨material, sent⟩ := dooming.1
  have responseEq : response = ⟨some material⟩ := by
    cases response with
    | mk transmission =>
        change transmission = some material at sent
        cases sent
        rfl
  have selected : choice.1 = some ⟨some material⟩ :=
    chosen.trans (congrArg some responseEq)
  rw [responseEq] at dooming
  have rawTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    current ▸ menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler history.trace
  have facts := settledFacts_history (serviceInitialLaw setup mode) horizon scheduler rawTrace
  have kept : ActivationKept execution.application :=
    (activationKeptInvariant setup leaks).history (serviceInitialLaw setup mode) horizon
      scheduler (fun state member => by
        obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
        exact activationKept_initial _) rawTrace
  apply forbiddenTraffic_collection_committed setup leaks menu horizon scheduler completes backend
    profile history who remaining execution current info choice observed material selected ?_
    observationRate deliveryRate delivery_nonnegative coverage
  intro fuel next final nextState path control finalState complete
  have held : DoomedAt who next.state := by
    rw [nextState]
    have facts : SettledFacts setup leaks execution := facts
    exact ⟨settledFacts_respond execution facts who ⟨some material⟩,
      respond_doomed rawTrace _ dooming, activationKept_respond execution who _ kept⟩
  exact doomedAt_forbidden_reaches who path held control finalState (finalState ▸ final.trace)
    complete

end Collection

end Vegas
