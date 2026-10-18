/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedWindowBayes
import Interaction.ReactiveSchedulerSeedSupport
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveSchedulerFinishSeed
import Vegas.Pending.PhaseOwnCommitments
import Vegas.Pending.PhaseSeedProtectedResolution

/-! # Actual posterior responses under the original all-event seeds -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (delay bound : graph.EventId → Nat)
  (priority : RestSeed → List (phaseApplication runtime leaks).EnvironmentEntry →
    (phaseApplication runtime leaks).EnvironmentView → Nat)
  (laws : PhaseSeedAddress graph → PMF (Seed runtime delay)) (restLaw : PMF RestSeed)
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "driver" => controller runtime leaks delay bound priority
local notation "mixture" => ReactiveApplication.AddressedScheduler.coordinateImplementation
  (controller runtime leaks delay bound priority) laws restLaw
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information menu initial horizon
  (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "SeedAt" => ReactiveApplication.AddressedScheduler.CoordinateSeed
  (Address := PhaseSeedAddress graph) (LocalSeed := Seed runtime delay) (RestSeed := RestSeed)
local notation "prior" => independentProduct
  (ReactiveApplication.AddressedScheduler.coordinateLaws laws restLaw)
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => prior
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
      (ReactiveApplication.Execution.environmentRecall
        (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (PhaseCount.onePacketMenu runtime leaks bounds)
    (PMF.map (PhaseRuntimeState.initial plan) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.AddressedScheduler.coordinateImplementation
        (controller runtime leaks delay bound priority) laws restLaw))))]

/-- Every supported original seed at an actual owner Bayes atom reconstructs
that same activation from an initialized, legal, fixed-seed history. -/
theorem bayes_original_activation
    (profile : ∀ who, (model).BehavioralPolicy who)
    (owner : Player) (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : (app).Control) (acting : current.actor = some owner)
    (supported : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
        positive).map (fun history => history.1.state)).support)
    (values : (index : Option (PhaseSeedAddress graph)) → SeedAt index)
    (valueSupport : values ∈ ((mixture).posterior current.execution.environmentRecall).support) :
    ∃ (input : graph.Inputs) (used : Nat) (before : (app).Execution),
      input ∈ inputs.support ∧ used < horizon ∧ current.remaining + 1 + used = horizon ∧
      values ∈ (prior).support ∧
      before ∈ ((app).runRounds ((driver).family
        (ReactiveApplication.AddressedScheduler.unpack values))
        ((menu).decodeProfile initial horizon (mixture).scheduler profile) used
          (ReactiveApplication.Execution.initial app
            (PhaseRuntimeState.initial plan input))).support ∧
      (.activate owner : (app).Command) ∈
        (((driver).family (ReactiveApplication.AddressedScheduler.unpack values))
          before.environmentRecall (before.observeEnvironment app)).support ∧
      current.execution ∈ (before.environmentStep app (.activate owner)).support ∧
      Nonempty (((menu).protocol initial horizon ((driver).family
        (ReactiveApplication.AddressedScheduler.unpack values))).Trace
          (some ⟨current.remaining, some owner, current.execution⟩)) := by
  classical
  have horizonPositive := (menu).informationSite_horizon_pos initial horizon
    (mixture).scheduler owner site
  let : NeZero horizon := ⟨ne_of_gt horizonPositive⟩
  let players := (menu).decodeProfile initial horizon (mixture).scheduler profile
  let occupied := (app).occupationControlLaw (mixture).scheduler players initial horizon
  have present := (menu).occupation_observation_support initial horizon (mixture).scheduler
    profile owner site positive
  have beliefsEq := (menu).bayesBelief_state_eq_occupationPosterior initial horizon
    (mixture).scheduler profile owner site
    ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site) positive
  have conditioned : some current ∈
      (fiberPosterior occupied ((app).observe owner) site.1).support := by
    rw [← beliefsEq]
    exact supported
  have actual := (mem_support_fiberPosterior present conditioned).2
  unfold ReactiveApplication.occupationControlLaw at actual
  obtain ⟨time, _timeSupport, actual⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
  unfold ReactiveApplication.commandControlLaw at actual
  obtain ⟨inputState, inputStateSupport, actual⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
  obtain ⟨input, inputSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp inputStateSupport
  obtain ⟨previous, reached, actual⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
  obtain ⟨command, chosen, actual⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
  obtain ⟨active, observed, controlEq⟩ := (PMF.mem_support_map_iff _ _ _).mp actual
  have currentEq := Option.some.inj controlEq
  have executionEq := congrArg ReactiveApplication.Control.execution currentEq
  have actorEq := (congrArg ReactiveApplication.Control.actor currentEq).trans acting
  have remainingEq := congrArg ReactiveApplication.Control.remaining currentEq
  change active = current.execution at executionEq
  change command.actor? app = some owner at actorEq
  change horizon - time.val - 1 = current.remaining at remainingEq
  have commandEq : command = .activate owner := by
    cases command with
    | activate acting =>
        exact congrArg ReactiveApplication.Command.activate (Option.some.inj actorEq)
    | wait => cases actorEq
    | «include» identifier => cases actorEq
    | application command => cases actorEq
  subst command
  rw [executionEq] at observed
  have original := (app).schedulerMixture_decision_of_posterior_support prior
    (fun seeds => (driver).family (ReactiveApplication.AddressedScheduler.unpack seeds)) players
    time.val (PhaseRuntimeState.initial plan input) previous current.execution (.activate owner)
    values reached chosen observed valueSupport
  obtain ⟨originalSupport, before, beforeSupport, selected, activated⟩ := original
  have countEq : current.remaining + 1 + time.val = horizon := by
    omega
  have covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (menu).actions who past view := by
    intro who past view action available
    exact (menu).decode_embedPolicy_covered initial horizon (mixture).scheduler who
      (profile who) past view action available
  let fixed := (driver).family (ReactiveApplication.AddressedScheduler.unpack values)
  obtain ⟨initialTrace⟩ := (menu).trace_initial initial horizon fixed
    (PhaseRuntimeState.initial plan input)
    ((PMF.mem_support_map_iff _ _ _).mpr ⟨input, inputSupport, rfl⟩)
  obtain ⟨beforeTrace⟩ := (menu).trace_runRounds initial horizon fixed players covered
    (current.remaining + 1) time.val _ before (by simpa only [countEq] using initialTrace)
    beforeSupport
  obtain ⟨activeTrace⟩ := (menu).trace_environment initial horizon fixed current.remaining before
    current.execution (.activate owner) beforeTrace selected activated
  exact ⟨input, time.val, before, inputSupport, time.isLt, countEq, originalSupport,
    beforeSupport, selected, activated, ⟨activeTrace⟩⟩

omit [Fintype Player] in
private theorem activation_application_eq (before active : (app).Execution) (owner : Player)
    (moved : active ∈ (before.environmentStep app (.activate owner)).support) :
    active.application = before.application := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
  obtain ⟨selected, _supported, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

private theorem callback_selected (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (before : (app).Execution) {input : graph.Inputs}
    (valid : before.application.Invariant input) (ordered : graph.RevealRelaxedOrdered)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (requested : before.application.SeedRequest owner coordinate.1)
    (chosen : .activate owner ∈ ((driver).family seeds before.environmentRecall
      (before.observeEnvironment app)).support) :
    selectedAt runtime leaks priority seeds.1 before = some coordinate ∧
      (queryAt runtime leaks before coordinate owner).elapsed <
        runtime.deadline coordinate.1.event := by
  have actual := (PMF.mem_support_pure_iff _ _).mp chosen
  have callback := callback_request runtime leaks delay bound priority seeds before valid ordered
    coordinate owner requested actual.symm
  have requestedAt : (selectedAt runtime leaks priority seeds.1 before).bind
      (fun selected => (graph.actor? selected.1.event).map fun acting =>
        (selected, queryAt runtime leaks before selected acting)) =
          some (coordinate, queryAt runtime leaks before coordinate owner) := callback
  obtain ⟨selected, selectedEq, queryEq⟩ := Option.bind_eq_some_iff.mp requestedAt
  obtain ⟨acting, _actor, same⟩ := Option.map_eq_some_iff.mp queryEq
  have coordinateEq : selected = coordinate := congrArg Prod.fst same
  have selectedCurrent : selectedAt runtime leaks priority seeds.1 before = some coordinate := by
    simpa only [coordinateEq] using selectedEq
  refine ⟨selectedCurrent, ?_⟩
  have replyEq : reply runtime leaks delay bound coordinate (seeds.2 coordinate)
      (queryAt runtime leaks before coordinate owner) = .activate owner := by
    rw [choose_eq_reply runtime leaks delay bound priority seeds before coordinate selectedCurrent
      owner requested.2.2.2.1] at actual
    exact actual.symm
  by_contra due
  have pastDeadline : runtime.deadline coordinate.1.event ≤
      (queryAt runtime leaks before coordinate owner).elapsed := Nat.le_of_not_gt due
  simp only [reply, decision, ite_eq_left pastDeadline] at replyEq
  cases replyEq

theorem response_envelope_recorded
    (current : (app).Execution) {input : graph.Inputs}
    (valid : current.application.Invariant input) (owner : Player)
    (coordinate : PhaseSeedAddress graph)
    (requested : current.application.SeedRequest owner coordinate.1)
    (material : WitnessedSubmission graph)
    (names : material.call.packet.event? graph = some coordinate.1.event)
    (entered : Nat)
    (stamp : current.application.current.native.activatedAt coordinate.1.event = some entered)
    (words : PhaseSeedScheduler.WordRecall runtime leaks
      (current.respond app owner ⟨some material⟩)) :
    ∃ message : Message Player (CommitAttemptPacket graph),
      message.id = (owner, current.network.nextSerial owner) ∧
      (current.application.current.native.clock - entered, message) ∈
        (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner
          (current.respond app owner ⟨some material⟩).environmentRecall
          ((current.respond app owner ⟨some material⟩).observeEnvironment app)).emissions := by
  classical
  let state := current.application.submit owner material
  let packet := state.emit owner (current.network.known owner) material
  let message := (current.network.submit owner packet).1
  have authored : message.sender = owner ∧ message.payload.attempt = coordinate.1.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.1.event := by
    refine ⟨rfl, ?_, ?_⟩
    · change state.attempt = coordinate.1.attempt
      exact requested.1.symm
    · change (state.emit owner (current.network.known owner) material).packet.call.event? graph = _
      rw [phase_emit_call]
      exact names
  have recalled : (current.respond app owner ⟨some material⟩).recall owner =
      current.recall owner ++ [⟨current.observe app owner, ⟨some material⟩, some message⟩] := by
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
    rfl
  refine ⟨message, rfl, ?_⟩
  rw [PhaseSeedScheduler.localInput_word, words owner coordinate.1, recalled]
  apply List.mem_flatMap.mpr
  let record := (current.application.current.native.clock - entered, [message])
  refine ⟨record, ?_, by simp only [record, List.mem_map, List.mem_singleton]; exact ⟨_, rfl, rfl⟩⟩
  apply List.mem_map.mpr
  refine ⟨⟨current.observe app owner, ⟨some material⟩, some message⟩, ?_, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨List.mem_append_right _ (by simp only [List.mem_singleton]), ?_⟩
    exact decide_eq_true ((PhaseRuntimeState.requests_publicView current.application valid
      owner coordinate.1).mpr requested)
  · simp only [record, Option.toList_some, List.filter_cons, List.filter_nil]
    have selected : PhaseSeedScheduler.ownPacket coordinate.1 owner message = true :=
      decide_eq_true authored
    rw [selected]
    change (current.application.current.native.clock -
      (current.application.current.native.activatedAt coordinate.1.event).getD
        current.application.current.native.clock, if true = true then [message] else []) =
          (current.application.current.native.clock - entered, [message])
    rw [stamp]
    rfl

open Classical in
/-- The conditional original seed realizes the exact receipt kernel of an
actual permitted response. All callback, provenance and completion hypotheses
are reconstructed from the original positive Bayes atom. -/
theorem bayes_response_receipt_runRounds
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (enough : serviceHorizon runtime ≤ horizon)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (owner : Player) (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : (app).Control) (acting : current.actor = some owner)
    (supported : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
        positive).map (fun history => history.1.state)).support)
    (values : (index : Option (PhaseSeedAddress graph)) → SeedAt index)
    (valueSupport : values ∈ ((mixture).posterior current.execution.environmentRecall).support)
    (coordinate : PhaseSeedAddress graph)
    (requestView : PhaseRuntimeState.requests (current.execution.observe app owner).application.2
      owner coordinate.1)
    (material : WitnessedSubmission graph)
    (names : material.call.packet.event? graph = some coordinate.1.event)
    (permitted : (⟨some material⟩ : (app).Action) ∈ (menu).actions owner
      (current.execution.recall owner) (current.execution.observe app owner))
    (future : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (future who past view).support →
      action ∈ (menu).actions who past view) :
    ((((app).runRounds ((driver).family
      (ReactiveApplication.AddressedScheduler.unpack values)) future current.remaining
        (current.execution.respond app owner ⟨some material⟩)).map fun final =>
          decide (((owner, current.execution.network.nextSerial owner), true) ∈ final.receipts))) =
      PMF.pure (decide (InclusionWindow runtime delay bound coordinate (values (some coordinate))
        (current.execution.application.current.native.clock -
          (current.execution.application.current.native.activatedAt coordinate.1.event).getD
            current.execution.application.current.native.clock))) := by
  obtain ⟨input, used, before, _inputSupport, _usedBound, _remaining, _priorSupport,
      _beforeSupport, chosen, moved, activeTrace⟩ := bayes_original_activation runtime leaks delay
        bound priority laws restLaw bounds plan inputs horizon profile owner site positive current
          acting supported values valueSupport
  obtain ⟨activeTrace⟩ := activeTrace
  let seeds := ReactiveApplication.AddressedScheduler.unpack values
  let fixed := (driver).family seeds
  have raw := (menu).toRawTrace initial horizon fixed activeTrace
  obtain ⟨actualInput, calendar, _exhaustion⟩ := history_calendar_state runtime leaks delay bound
    priority seeds plan ordered maximal inputs horizon raw
      ⟨current.remaining, some owner, current.execution⟩ rfl
  have valid := calendar.safe.invariant
  have requested : current.execution.application.SeedRequest owner coordinate.1 :=
    (PhaseRuntimeState.requests_publicView current.execution.application valid owner
      coordinate.1).mp
      requestView
  have applicationEq := activation_application_eq runtime leaks before current.execution owner
    moved
  have beforeValid : before.application.Invariant actualInput := by
    rw [← applicationEq]
    exact valid
  have beforeRequest : before.application.SeedRequest owner coordinate.1 := by
    rw [← applicationEq]
    exact requested
  obtain ⟨selected, timely⟩ := callback_selected runtime leaks delay bound priority seeds before
    beforeValid ordered coordinate owner beforeRequest chosen
  obtain ⟨postTrace⟩ := (menu).trace_respond initial horizon fixed current.remaining
    current.execution owner ⟨some material⟩ activeTrace permitted
  let post := current.execution.respond app owner ⟨some material⟩
  have postWords := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks menu initial horizon
    fixed current.remaining post postTrace
  have postClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds fixed).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) postTrace
  have postValid := (phaseApplication_invariant runtime leaks actualInput).respond current.execution
    owner ⟨some material⟩ valid
  have postOrder := (phaseApplication_seedOrder runtime leaks).respond current.execution owner
    ⟨some material⟩ calendar.safe.ordered
  have postRequest := respond_request runtime leaks current.execution owner ⟨some material⟩ owner
    coordinate.1 requested
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff coordinate.1.event).mpr
      ⟨requested.2.2.1, by rw [requested.2.2.2.1]; rfl⟩)
  have postStamp : post.application.current.native.activatedAt coordinate.1.event = some entered :=
    (current.execution.application.submit_progress owner material valid.active).activated
      coordinate.1.event entered activated postRequest.2.2.1.1
  have postClock := respond_clock runtime leaks current.execution valid owner ⟨some material⟩
  have started : entered ≤ post.application.current.native.clock := by
    rw [postClock]
    exact valid.active.activated_le coordinate.1.event entered activated
  have postTimely : post.application.current.native.clock - entered <
      runtime.deadline coordinate.1.event := by
    change before.application.current.native.clock -
      (before.application.current.native.activatedAt coordinate.1.event).getD
        before.application.current.native.clock < _ at timely
    rw [← applicationEq, activated, Option.getD_some] at timely
    rwa [postClock]
  have unclosed := callback_tick_unclosed runtime leaks priority seeds.1 before current.execution
    beforeValid owner ⟨some material⟩ coordinate selected moved
  obtain ⟨message, messageId, recorded⟩ := response_envelope_recorded runtime leaks
    current.execution valid owner coordinate requested material names entered activated postWords
  have postRecorded : (post.application.current.native.clock - entered, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner post.environmentRecall
        (post.observeEnvironment app)).emissions := by
    rwa [postClock]
  have law := receipt_runRounds_law runtime leaks delay bound priority seeds bounds plan ordered
    maximal inputs horizon enough future current.remaining post postTrace covered postValid
    postOrder
    postWords postClean owner coordinate postRequest entered postStamp started unclosed message
    postRecorded postTimely
  rw [messageId] at law
  have elapsed : (current.execution.application.current.native.activatedAt
      coordinate.1.event).getD current.execution.application.current.native.clock = entered := by
    rw [activated]
    rfl
  simpa only [post, seeds, ReactiveApplication.AddressedScheduler.unpack, postClock, elapsed]
    using law

omit [Fintype Player] in
open Classical in
/-- The actual future receipt of the envelope authored now; absence of a
controlled state is represented by absence of a response readout. -/
def authoredReceiptLaw (scheduler : (app).Scheduler) (future : Player → (app).Policy)
    (owner : Player) (material : WitnessedSubmission graph) :
    (app).ProtocolState → PMF (Option Bool)
  | none => PMF.pure none
  | some current =>
      ((app).runRounds scheduler future current.remaining
        (current.execution.respond app owner ⟨some material⟩)).map fun final =>
          some (decide (((owner, current.execution.network.nextSerial owner), true) ∈
            final.receipts))

omit [Fintype Player] in
private theorem mixture_rounds {S : Type} (law : PMF S) (family : S → (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution) :
    (((app).schedulerMixture law family).posterior execution.environmentRecall).bind
      (fun seed => (app).runRounds (family seed) players count execution) =
        (app).runRounds ((app).schedulerMixture law family).scheduler players count execution := by
  have realized := ((app).schedulerMixture law family).realize players count execution
  simp only [ReactiveApplication.schedulerMixture_runJoint, PMF.map_bind, PMF.map_comp,
    Function.comp_def] at realized
  have identity (p : PMF (app).Execution) : p.map (fun value => value) = p := PMF.map_id p
  simpa only [identity] using realized

open Classical in
/-- The actual future receipt kernel at a supported owner control is the original
conditional seed window, with all remaining physical history retained. -/
theorem bayes_authored_receipt_kernel
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (enough : serviceHorizon runtime ≤ horizon)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (owner : Player) (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (coordinate : PhaseSeedAddress graph)
    (current : (app).Control) (acting : current.actor = some owner)
    (stateSupport : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
        positive).map (fun history => history.1.state)).support)
    (sameInfo : (current.execution.recall owner, current.execution.observe app owner) =
      (past, view))
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate.1)
    (material : WitnessedSubmission graph)
    (names : material.call.packet.event? graph = some coordinate.1.event)
    (permitted : (⟨some material⟩ : (app).Action) ∈ (menu).actions owner past view)
    (future : Player → (app).Policy)
    (covered : ∀ who previous current action, action ∈ (future who previous current).support →
      action ∈ (menu).actions who previous current) :
    authoredReceiptLaw runtime leaks (mixture).scheduler future owner material (some current) =
      (((mixture).posterior current.execution.environmentRecall).map fun values :
        (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
          some (decide (InclusionWindow runtime delay bound coordinate (values (some coordinate))
            (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past
              view).elapsed))) := by
  let sent :=
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past view).elapsed
  have pastEq : current.execution.recall owner = past := congrArg Prod.fst sameInfo
  have viewEq : current.execution.observe app owner = view := congrArg Prod.snd sameInfo
  have requestView : PhaseRuntimeState.requests
      (current.execution.observe app owner).application.2 owner coordinate.1 := by
    erw [viewEq]
    exact request
  have available : (⟨some material⟩ : (app).Action) ∈ (menu).actions owner
      (current.execution.recall owner) (current.execution.observe app owner) := by
    erw [pastEq, viewEq]
    exact permitted
  have elapsedEq : current.execution.application.current.native.clock -
      (current.execution.application.current.native.activatedAt coordinate.1.event).getD
        current.execution.application.current.native.clock = sent := by
    change _ = view.application.2.native.clock -
      (view.application.2.native.activatedAt coordinate.1.event).getD
        view.application.2.native.clock
    have publicEq :=
      congrArg (fun observed : (app).PlayerView => observed.application.2) viewEq
    have clockEq : current.execution.application.current.native.clock =
        view.application.2.native.clock :=
      congrArg (fun visible => visible.native.clock) publicEq
    have stampEq :
        current.execution.application.current.native.activatedAt coordinate.1.event =
        view.application.2.native.activatedAt coordinate.1.event :=
      congrArg (fun visible => visible.native.activatedAt coordinate.1.event) publicEq
    rw [clockEq, stampEq]
  let post := current.execution.respond app owner ⟨some material⟩
  have seeded := mixture_rounds runtime leaks prior
    (fun values => (driver).family (ReactiveApplication.AddressedScheduler.unpack values))
    future current.remaining post
  change ((app).runRounds (mixture).scheduler future current.remaining post).map _ = _
  erw [← seeded, PMF.map_bind]
  apply bind_congr_on_support ((mixture).posterior current.execution.environmentRecall)
  intro values valueSupport
  have kernel := bayes_response_receipt_runRounds runtime leaks delay bound priority laws
    restLaw bounds plan inputs horizon ordered maximal enough profile owner site positive
    current acting stateSupport values valueSupport coordinate requestView material names
    available future covered
  have mapped := congrArg (fun law : PMF Bool => law.map some) kernel
  simpa only [PMF.map_comp, Function.comp_def, PMF.pure_map, elapsedEq] using mapped

open Classical in
/-- The original full owner Bayes belief, followed by the actual response and
continuation, has precisely the original delay-filtered local coin-window law.
The continuation policies and priority may use their full retained observations. -/
theorem bayes_authored_receipt_law
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (enough : serviceHorizon runtime ≤ horizon)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (owner : Player) (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (siteInfo : site.1 = some (past, view)) (coordinate : PhaseSeedAddress graph)
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs past,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (material : WitnessedSubmission graph)
    (names : material.call.packet.event? graph = some coordinate.1.event)
    (permitted : (⟨some material⟩ : (app).Action) ∈ (menu).actions owner past view)
    (future : Player → (app).Policy)
    (covered : ∀ who previous current action, action ∈ (future who previous current).support →
      action ∈ (menu).actions who previous current) :
    ∃ (firstClock : Nat)
      (localPositive : ∃ seed ∈ {seed : Seed runtime delay | seed.1.val = firstClock},
        seed ∈ (laws coordinate).support),
      firstClock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view ∧
      (∀ clock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view,
        firstClock ≤ clock) ∧
      ((((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
          positive).map (fun history => history.1.state)).bind
        (authoredReceiptLaw runtime leaks (mixture).scheduler future owner material)) =
      ((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
        localPositive).map fun seed => some (decide (InclusionWindow runtime delay bound coordinate
          seed (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past
            view).elapsed))
      := by
  let belief := (((model).bayesBelief profile owner site
    ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
      positive).map fun history => history.1.state)
  let sent :=
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past view).elapsed
  obtain ⟨firstClock, localPositive, member, least, windowLaw⟩ := bayesBelief_original_window_law
    runtime leaks delay bound priority laws restLaw bounds plan inputs horizon ordered maximal
      profile owner site positive past view siteInfo coordinate request unsent sent
  refine ⟨firstClock, localPositive, member, least, ?_⟩
  have rows : belief.bind
      (authoredReceiptLaw runtime leaks (mixture).scheduler future owner material) =
      belief.bind (fun state => (draws state).map fun
          values : (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
        some (decide (InclusionWindow runtime delay bound coordinate
          (values (some coordinate)) sent))) := by
    apply bind_congr_on_support belief
    intro state stateSupport
    obtain ⟨history, _historySupport, stateEq⟩ := (PMF.mem_support_map_iff _ _ _).mp stateSupport
    have observed : (app).observe owner state = some (past, view) := by
      rw [← stateEq]
      exact ((menu).info initial horizon (mixture).scheduler owner history.1.trace).symm.trans
        (history.2.trans siteInfo)
    cases state with
    | none => cases observed
    | some current =>
        have acting : current.actor = some owner := by
          apply ((app).observe_isSome owner (some current)).mp
          rw [observed]
          rfl
        have sameInfo : (current.execution.recall owner, current.execution.observe app owner) =
            (past, view) := by
          change (if current.actor = some owner then
            some (current.execution.recall owner, current.execution.observe app owner) else none) =
              some (past, view) at observed
          rw [ite_eq_left acting] at observed
          exact Option.some.inj observed
        exact bayes_authored_receipt_kernel runtime leaks delay bound priority laws restLaw
          bounds plan inputs horizon ordered maximal enough profile owner site positive past view
          coordinate current acting stateSupport sameInfo request material names permitted future
          covered
  have mapped := congrArg (fun law : PMF Bool => law.map some) windowLaw
  calc
    _ = _ := rows
    _ = _ := by
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
      exact mapped

end Vegas.EventGraphRuntime.PhaseSeedCalendar
