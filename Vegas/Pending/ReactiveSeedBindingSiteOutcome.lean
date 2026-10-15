/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSeedBindingOutcome

/-! # Original-seed binding outputs from actual unsent information sites -/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- A completed original-seed continuation from an actual clean unsent site
has its first resolving transcript and exact typed physical output. All
initial recall, immutable handle and genuine-priorSupported domain facts are derived. -/
theorem bayesBelief_first_binding_output
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : (app).Control) (acting : current.actor = some owner)
    (supported : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
        (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
          (fun history => history.1.state)).support)
    (values : (side : Bool) → A side)
    (valueSupport : values ∈ ((mixture).posterior current.execution.environmentRecall).support)
    (ready : current.execution.application.publicView.EventReady event)
    (unmissed : current.execution.application.publicView.missedBindingBy owner = false)
    (unsent : (runtime.ownerSeedInput leaks event (current.execution.recall owner)
      (current.execution.observe app owner)).emitted = [])
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (bounded : ∀ value, result = .success value → (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (admissible : ∀ clocks slot, choose clocks = some slot → slot < bounds.candidateCount ∧
      slot ∉ runtime.submittedCandidateSlots leaks (current.execution.recall owner))
    (future : Player → (app).Policy)
    (focal : future owner = fun past view => PMF.pure
      (runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose
        past view))
    (coveredFuture : ∀ who past view action, action ∈ (future who past view).support →
      action ∈ (menu).actions who past view)
    (next : (app).Execution)
    (reached : next ∈ ((app).runRounds (family values) future current.remaining
      (current.execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (current.execution.recall owner) (current.execution.observe app owner)))).support)
    (completed : event ∈ next.application.config.cut.completed) :
    let start := current.execution.respond app owner (runtime.bindingServiceResponse leaks owner
      event payload result choose (current.execution.recall owner)
        (current.execution.observe app owner))
    let memory := fun execution : (app).Execution => controller.replay remainder
      (initialMemory (values false) (values true)) execution.environmentRecall
    ∃ (used : Nat) (before final : (app).Execution)
      (query : CurrentSeedQuery graph) (command : (app).Command),
      used < current.remaining ∧
        before ∈ ((app).runRounds (family values) future used start).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch future
          (controller.step remainder (memory before) before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        CountedQueryLog ((memory before).log ++ [⟨query, .resolution command⟩]) ∧
        (∀ entry ∈ (memory before).log,
          entry.reply = .activation ∨ entry.reply = .exhausted) ∧
        (∀ entry ∈ (memory before).log ++ [⟨query, .resolution command⟩],
          controller.reply (values false) entry.query = entry.reply ∧
          entry.query.input.emitted =
            bindingEmissionWord (controller.calendar (values false)) choose
            (runtime.readyActivationCount leaks event (current.execution.recall owner)) owner event
            (current.execution.network.nextSerial owner)
            entry.query.activationIndex) ∧
        (memory final).log = (memory before).log ++ [⟨query, .resolution command⟩] ∧
        (∃ ready : before.application.config.cut.Ready event,
          final.application.config = before.application.config.complete event ready
            (cast (congrArg EventField.Action outputEq.symm)
              (runtime.bindingResolutionResult leaks command result))
            (cast (congrArg EventField.Value outputEq.symm)
              (runtime.bindingResolutionResult leaks command result))) ∧
        next.application.config.outputs event = some
          (cast (congrArg EventField.Value outputEq.symm)
            (runtime.bindingResolutionResult leaks command result)) := by
  classical
  let response := runtime.bindingServiceResponse leaks owner event payload result choose
    (current.execution.recall owner) (current.execution.observe app owner)
  let after := current.execution.respond app owner response
  let memory := fun execution : (app).Execution => controller.replay remainder
    (initialMemory (values false) (values true)) execution.environmentRecall
  have binding : bindingOwnedBy graph owner event = true := by
    simp only [bindingOwnedBy, outputEq, decide_true]
  obtain ⟨sourceHistory, _, sourceState⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have sourceTrace : ((menu).protocol (inputs.map State.initial) horizon
      (mixture).scheduler).Trace (some current) := sourceState ▸ sourceHistory.1.trace
  have rawSourceTrace := (menu).toRawTrace (inputs.map State.initial) horizon
    (mixture).scheduler sourceTrace
  have responseEq := runtime.guardedBindingServiceResponse_eq_at_history leaks bounds inputs horizon
    (mixture).scheduler current rawSourceTrace (current.execution.recall owner) owner event payload
      result choose binding bounded admissible
        (runtime.bindingServiceEpisode_initial leaks owner event payload result current.execution)
          (current.execution.observe app owner) rfl
  have permitted : response ∈ (menu).actions owner (current.execution.recall owner)
      (current.execution.observe app owner) := by
    change runtime.bindingServiceResponse leaks owner event payload result choose
      (current.execution.recall owner) (current.execution.observe app owner) ∈ _
    rw [← responseEq]
    exact runtime.guardedBindingServiceResponse_available leaks bounds owner event payload result
      choose (current.execution.recall owner) (current.execution.observe app owner)
  obtain ⟨used, before, final, query, command, within, priorSupported, incomplete, complete, moved,
      counted, unresolved, words, logged, suffix⟩ :=
    controller.bayesBelief_first_binding_resolution remainder laws bounds inputs horizon ordered
      domainEq owned profile site positive current acting supported values valueSupport ready
        unmissed unsent payload result choose binding bounded admissible future focal coveredFuture
          next
          reached
          completed
  obtain ⟨setup, entered, _, valid, _, genuine, activated, _⟩ :=
    controller.bayesBelief_response_log_signature remainder laws bounds inputs horizon ordered
      domainEq owned profile site positive current acting supported values valueSupport ready
        unmissed response permitted
  have joint : (before, memory before) ∈
      ((controller.implementation (PMF.pure (values false))
        (PMF.pure (values true)) remainder).runJoint
        future used after (memory after)).support := by
    rw [controller.runJoint_replay]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨before, priorSupported, rfl⟩
  have sourceDomain : runtime.CountedSeedDomain leaks bounds inputs owner after := by
    rw [← domainEq]
    exact genuine
  have beforeDomain := controller.runJoint_countedSeedDomain_survives (PMF.pure (values false))
    (PMF.pure (values true)) remainder bounds inputs ordered owned future coveredFuture setup
      entered used after (memory after) before (memory before) valid activated sourceDomain
        incomplete joint
  obtain ⟨history, _, stateEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have activeTrace : ((menu).protocol (inputs.map State.initial) horizon
      (mixture).scheduler).Trace (some ⟨current.remaining, some owner, current.execution⟩) := by
    have trace := stateEq ▸ history.1.trace
    convert trace using 1
    cases current
    simp_all only
  obtain ⟨afterTrace⟩ := (menu).trace_respond (inputs.map State.initial) horizon
    (mixture).scheduler current.remaining current.execution owner response activeTrace permitted
  obtain ⟨beforeScheduler, ⟨beforeTrace⟩⟩ := controller.runJoint_trace (PMF.pure (values false))
    (PMF.pure (values true)) remainder menu (inputs.map State.initial) future coveredFuture used
      horizon (mixture).scheduler current.remaining after (memory after) before (memory before)
        afterTrace joint
  have replayEq : memory final =
      (controller.step remainder (memory before) before.environmentRecall
        (before.observeEnvironment app)).2 := by
    change controller.replay remainder (initialMemory (values false) (values true))
      final.environmentRecall = _
    rw [(app).dispatch_environmentRecall future _ before final moved]
    exact controller.replay_snoc remainder (initialMemory (values false) (values true))
      before.environmentRecall _
  have stepLog : (controller.step remainder (memory before) before.environmentRecall
      (before.observeEnvironment app)).2.log = (memory before).log ++
        [⟨query, .resolution command⟩] := by
    rw [← replayEq]
    exact logged
  obtain ⟨issued, resolving, _⟩ := controller.step_resolution_of_log remainder (memory before)
    before query command (by rw [domainEq]; exact beforeDomain) stepLog
  have output := runtime.bindingServiceResponse_resolution_result leaks bounds inputs
    (horizon + used)
    beforeScheduler ⟨current.remaining, none, before⟩ beforeTrace owner event payload result choose
      current.execution unsent (family values) future used focal priorSupported outputEq codeEq node
        command
        final resolving incomplete complete (by
          change final ∈ ((app).dispatch future (controller.step remainder (memory before)
            before.environmentRecall (before.observeEnvironment app)).1 before).support at moved
          rw [issued] at moved
          exact moved)
  obtain ⟨readyNow, produced⟩ := output
  have stored : final.application.config.store (.inr event) = some
      (cast (congrArg EventField.Value outputEq.symm)
        (runtime.bindingResolutionResult leaks command result)) := by
    rw [Config.store_output, produced, Config.complete_output_same]
  have preserved := ReactiveApplication.Invariant.policyInvariant app
    (runtime.reactiveStoreInvariant leaks (.inr event)
      (cast (congrArg EventField.Value outputEq.symm)
        (runtime.bindingResolutionResult leaks command result))) future
  have retained := preserved.runRounds (family values) (current.remaining - used - 1)
    final next stored suffix
  exact ⟨used, before, final, query, command, within, priorSupported, incomplete, complete, moved,
    counted, unresolved, words, logged, ⟨readyNow, produced⟩, retained⟩

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- For one original local seed and pure clock/handle rule at one actual
unsent information site, the first physical binding output uses the same
resolving command across all supported remainder states and seeds. Hidden
well-typed results can differ, and no success-law factorization is assumed. -/
theorem bayesBelief_first_binding_output_common
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : Bool → (app).Control)
    (acting : ∀ side, (current side).actor = some owner)
    (supported : ∀ side, some (current side) ∈
      (((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
          (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
            (fun history => history.1.state)).support)
    (values : Bool → (side : Bool) → A side)
    (valueSupport : ∀ side, values side ∈
      ((mixture).posterior (current side).execution.environmentRecall).support)
    (sameSeed : values false false = values true false)
    (ready : ∀ side, (current side).execution.application.publicView.EventReady event)
    (unmissed : ∀ side,
      (current side).execution.application.publicView.missedBindingBy owner = false)
    (unsent : ∀ side, (runtime.ownerSeedInput leaks event
      ((current side).execution.recall owner)
      ((current side).execution.observe app owner)).emitted = [])
    (payload : L.Ty) (result : Bool → PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (bounded : ∀ side value, result side = .success value →
      (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (admissible : ∀ side clocks slot, choose clocks = some slot →
      slot < bounds.candidateCount ∧
        slot ∉ runtime.submittedCandidateSlots leaks ((current side).execution.recall owner))
    (future : Bool → Player → (app).Policy)
    (focal : ∀ side, future side owner = fun past view => PMF.pure
      (runtime.guardedBindingServiceResponse leaks bounds owner event
        payload (result side) choose past view))
    (coveredFuture : ∀ side who past view action,
      action ∈ (future side who past view).support → action ∈ (menu).actions who past view)
    (next : Bool → (app).Execution)
    (reached : ∀ side, next side ∈ ((app).runRounds (family (values side)) (future side)
      (current side).remaining ((current side).execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event payload (result side) choose
          ((current side).execution.recall owner)
          ((current side).execution.observe app owner)))).support)
    (completed : ∀ side, event ∈ (next side).application.config.cut.completed) :
    ∃ command : (app).Command,
      ∀ side, ∃ (used : Nat) (before final : (app).Execution)
        (ready : before.application.config.cut.Ready event),
        used < (current side).remaining ∧
        before ∈ ((app).runRounds (family (values side)) (future side) used
          ((current side).execution.respond app owner
            (runtime.bindingServiceResponse leaks owner event payload (result side) choose
              ((current side).execution.recall owner)
              ((current side).execution.observe app owner)))).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch (future side)
          (controller.step remainder
            (controller.replay remainder (initialMemory (values side false) (values side true))
              before.environmentRecall) before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        final.application.config = before.application.config.complete event ready
          (cast (congrArg EventField.Action outputEq.symm)
            (runtime.bindingResolutionResult leaks command (result side)))
          (cast (congrArg EventField.Value outputEq.symm)
            (runtime.bindingResolutionResult leaks command (result side))) ∧
        (next side).application.config.outputs event = some
          (cast (congrArg EventField.Value outputEq.symm)
            (runtime.bindingResolutionResult leaks command (result side))) := by
  classical
  have genuine : ∀ side,
      (app).observe owner (some (current side)) = site.1 ∧
      (current side).execution.SerialRecall app := by
    intro side
    obtain ⟨history, _, stateEq⟩ := (PMF.mem_support_map_iff _ _ _).mp (supported side)
    have observed := (menu).info (inputs.map State.initial) horizon
      (mixture).scheduler owner history.1.trace
    have infoEq : (app).observe owner history.1.state = site.1 :=
      observed.symm.trans history.2
    have trace := stateEq ▸ history.1.trace
    refine ⟨?_, ?_⟩
    · exact stateEq ▸ infoEq
    · exact (runtime.countRecall_history leaks
        ((menu).toRawTrace (inputs.map State.initial) horizon (mixture).scheduler trace)).2.1
  have inputEq :
      ((current false).execution.recall owner, (current false).execution.observe app owner) =
      ((current true).execution.recall owner, (current true).execution.observe app owner) := by
    have same := (genuine false).1.trans (genuine true).1.symm
    simpa only [ReactiveApplication.observe, acting, ite_eq_left, Option.some.injEq] using same
  have recallEq : (current false).execution.recall owner =
      (current true).execution.recall owner := congrArg Prod.fst inputEq
  have serialEq : (current false).execution.network.nextSerial owner =
      (current true).execution.network.nextSerial owner := by
    rw [(genuine false).2 owner, (genuine true).2 owner, recallEq]
  obtain ⟨leftUsed, leftBefore, leftFinal, leftQuery, leftCommand,
      leftWithin, leftReached, leftIncomplete, leftComplete, leftMoved, leftCounted,
      leftUnresolved, leftWords, leftLog, leftOutput, leftReadout⟩ :=
    controller.bayesBelief_first_binding_output remainder laws bounds inputs horizon
      ordered domainEq owned profile site positive (current false) (acting false)
        (supported false) (values false) (valueSupport false) (ready false) (unmissed false)
          (unsent false) payload (result false) choose outputEq codeEq node
            (bounded false) (admissible false) (future false) (focal false) (coveredFuture false)
              (next false) (reached false) (completed false)
  obtain ⟨rightUsed, rightBefore, rightFinal, rightQuery, rightCommand,
      rightWithin, rightReached, rightIncomplete, rightComplete, rightMoved, rightCounted,
      rightUnresolved, rightWords, rightLog, rightOutput, rightReadout⟩ :=
    controller.bayesBelief_first_binding_output remainder laws bounds inputs horizon
      ordered domainEq owned profile site positive (current true) (acting true)
        (supported true) (values true) (valueSupport true) (ready true) (unmissed true)
          (unsent true) payload (result true) choose outputEq codeEq node
            (bounded true) (admissible true) (future true) (focal true) (coveredFuture true)
              (next true) (reached true) (completed true)
  have sameLog := CountedQueryLog.eq_at_resolution controller (values false false)
    (bindingEmissionWord (controller.calendar (values false false)) choose
      (runtime.readyActivationCount leaks event ((current false).execution.recall owner))
      owner event ((current false).execution.network.nextSerial owner))
    leftQuery rightQuery leftCommand rightCommand leftCounted rightCounted
    (fun entry member => (leftWords entry member).1)
    (fun entry member => by rw [sameSeed]; exact (rightWords entry member).1)
    (fun entry member => (leftWords entry member).2)
    (fun entry member => by
      rw [sameSeed, recallEq, serialEq]
      exact (rightWords entry member).2) leftUnresolved rightUnresolved
  have entries := List.singleton_inj.mp (List.append_inj' sameLog rfl).2
  have commandEq : leftCommand = rightCommand :=
    LocalSeedReply.resolution.inj (congrArg LocalSeedEntry.reply entries)
  obtain ⟨leftReady, leftOutput⟩ := leftOutput
  obtain ⟨rightReady, rightOutput⟩ := rightOutput
  refine ⟨leftCommand, ?_⟩
  intro side
  cases side with
  | false =>
      exact ⟨leftUsed, leftBefore, leftFinal, leftReady, leftWithin, leftReached,
        leftIncomplete, leftComplete, leftMoved, leftOutput, leftReadout⟩
  | true =>
      refine ⟨rightUsed, rightBefore, rightFinal, rightReady, rightWithin, rightReached,
        rightIncomplete, rightComplete, rightMoved, ?_, ?_⟩
      · rw [commandEq]
        exact rightOutput
      · rw [commandEq]
        exact rightReadout

end Vegas.EventGraphRuntime.LocalSeedController

end
