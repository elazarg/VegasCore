/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecordedResponse
import Vegas.Pending.ReactiveSeedBindingReadout
import Vegas.Pending.ReactiveSeedBindingService
import Vegas.Pending.ReactiveOnePacketFreshness

/-! # Actual output of pure event-local binding service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- Every recorded canonical preparation in the actual menu history retains
its exact declared result, with freshness derived at its real active origin. -/
theorem onePacket_recorded_binding_result
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (owner : Player) (entry : (app).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (slot : Nat)
    (declared : entry.action = runtime.reactiveBinding leaks owner event payload result slot) :
    control.execution.application.bindingResult (owner, .prepared slot) payload = result := by
  obtain ⟨before, prior, _prefix, _, viewed, permitted, _⟩ :=
    (bounds.onePacketMenu runtime leaks).recorded_response_prefix (inputs.map State.initial)
      horizon scheduler control trace owner entry recorded
  rw [declared] at permitted
  have fresh : before.execution.application.candidates.lookup (owner, .prepared slot) = .fresh := by
    cases result with
    | failure =>
        exact bounds.onePacket_binding_fresh runtime leaks inputs horizon scheduler prior owner
          event slot none permitted
    | success value =>
        exact bounds.onePacket_binding_fresh runtime leaks inputs horizon scheduler prior owner
          event slot (some ⟨payload, value⟩) permitted
  have rememberedFresh : entry.beforeView.application.candidates (.prepared slot) = .fresh := by
    rw [viewed]
    exact fresh
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (inputs.map State.initial)
    horizon scheduler trace
  exact (runtime.recordedBindingMeaning_history leaks (inputs.map State.initial) horizon scheduler
    control rawTrace owner entry recorded event payload result slot declared rememberedFresh).2

/-- Selected-event packets in own recall use the chosen hidden typed result. -/
def BindingServiceRecall (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (execution : (app).Execution) : Prop :=
  ∀ entry ∈ execution.recall owner, ∀ message, entry.emitted = some message →
    message.payload.call.event? graph = some event →
      ∃ slot, entry.action = runtime.reactiveBinding leaks owner event payload result slot

omit [Fintype Player] in
/-- Before the first selected-event packet, no earlier private response needs
to be assigned a new binding meaning. -/
theorem bindingServiceRecall_of_unsent
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (execution : (app).Execution)
    (unsent : ((app).outputs (execution.recall owner)).filter
      (fun message => message.payload.call.event? graph = some event) = []) :
    runtime.BindingServiceRecall leaks owner event payload result execution := by
  intro entry recorded message emitted named
  have output : message ∈ (app).outputs (execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
  have selected : message ∈ ((app).outputs (execution.recall owner)).filter
      (fun packet => packet.payload.call.event? graph = some event) :=
    List.mem_filter.mpr ⟨output, by simpa only [decide_eq_true_eq] using named⟩
  rw [unsent] at selected
  cases selected

omit [Fintype Player] in
/-- The pure local rule either waits or submits its chosen handle; no hidden
preparation enters the packet-word choice. -/
theorem bindingServiceResponse_cases
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    runtime.bindingServiceResponse leaks owner event payload result choose past view = ⟨none⟩ ∨
      ∃ slot, runtime.bindingServiceResponse leaks owner event payload result choose past view =
        runtime.reactiveBinding leaks owner event payload result slot := by
  unfold bindingServiceResponse
  split
  · cases choice : choose _ with
    | none => exact Or.inl rfl
    | some slot => exact Or.inr ⟨slot, rfl⟩
  · exact Or.inl rfl

omit [Fintype Player] in
/-- Silence and a canonical selected binding preserve the physical recall grammar. -/
theorem BindingServiceRecall.respond
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (execution : (app).Execution)
    (response : (app).Action)
    (valid : runtime.BindingServiceRecall leaks owner event payload result execution)
    (shape : response = ⟨none⟩ ∨
      ∃ slot, response = runtime.reactiveBinding leaks owner event payload result slot) :
    runtime.BindingServiceRecall leaks owner event payload result
      (execution.respond app owner response) := by
  intro entry recorded message emitted named
  rw [runtime.respond_recall leaks execution owner owner response, ite_eq_left rfl] at recorded
  rcases List.mem_append.mp recorded with earlier | new
  · exact valid entry earlier message emitted named
  · cases List.mem_singleton.mp new
    rcases shape with silent | canonical
    · rw [silent] at emitted
      cases emitted
    · exact canonical

/-- Arbitrary foreign play and environment service preserve the selected
binding result under the globally legal local clock/handle implementation. -/
theorem bindingServiceRecall_policyInvariant
    (bounds : MessageBounds graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (players : Player → (app).Policy)
    (focal : players owner = fun past view => PMF.pure
      (runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose
        past view)) :
    (app).PolicyInvariant players
      (runtime.BindingServiceRecall leaks owner event payload result) := by
  refine ⟨?_, ?_⟩
  · intro execution who response valid chosen
    by_cases same : owner = who
    · subst who
      have responseEq : response = runtime.guardedBindingServiceResponse leaks bounds owner event
          payload result choose (execution.recall owner) (execution.observe app owner) := by
        rw [focal] at chosen
        exact (PMF.mem_support_pure_iff _ _).mp chosen
      apply BindingServiceRecall.respond runtime leaks owner event payload result execution response
        valid
      rw [responseEq]
      exact runtime.guardedBindingServiceResponse_cases leaks bounds owner event payload result
        choose (execution.recall owner) (execution.observe app owner)
    · intro entry recorded message emitted named
      rw [(app).respond_recall_other execution who owner same response] at recorded
      exact valid entry recorded message emitted named
  · intro execution next command valid moved entry recorded message emitted named
    rw [(app).environmentStep_recall execution next command moved] at recorded
    exact valid entry recorded message emitted named

/-- After arbitrary actual waiting and competing traffic, an event-local pure
binding service writes its declared result on inclusion and failure on expiry.
All response freshness and accepted-handle meaning come from the actual menu
trace, rather than being assumptions about success or payoffs. -/
theorem bindingServiceResponse_resolution_result
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (historyScheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon historyScheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (execution : (app).Execution)
    (unsent : ((app).outputs (execution.recall owner)).filter
      (fun message => message.payload.call.event? graph = some event) = [])
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (rounds : Nat)
    (focal : players owner = fun past view => PMF.pure
      (runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose
        past view))
    (continued : control.execution ∈ ((app).runRounds scheduler players rounds
      (execution.respond app owner (runtime.bindingServiceResponse leaks owner event payload result
        choose (execution.recall owner) (execution.observe app owner)))).support)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (command : (app).Command) (next : (app).Execution)
    (resolving : runtime.ResolvingSeedCommand leaks event control.execution command)
    (unfinished : event ∉ control.execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : next ∈ ((app).dispatch players command control.execution).support) :
    ∃ ready : control.execution.application.config.cut.Ready event,
      next.application.config = control.execution.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (runtime.bindingResolutionResult leaks command result))
        (cast (congrArg EventField.Value outputEq.symm)
          (runtime.bindingResolutionResult leaks command result)) := by
  have invariant := runtime.bindingServiceRecall_policyInvariant leaks bounds owner event payload
    result
    choose players focal
  have initial := runtime.bindingServiceRecall_of_unsent leaks owner event payload result execution
    unsent
  have responded := BindingServiceRecall.respond runtime leaks owner event payload result execution
    (runtime.bindingServiceResponse leaks owner event payload result choose (execution.recall owner)
      (execution.observe app owner)) initial (runtime.bindingServiceResponse_cases leaks owner event
        payload
        result choose (execution.recall owner) (execution.observe app owner))
  have grammar := invariant.runRounds scheduler rounds _ control.execution responded continued
  rcases runtime.resolvingSeedCommand_binding_readout leaks players control.execution next event
      owner payload outputEq codeEq node command resolving unfinished completed reached with
    expired | included
  · obtain ⟨commandEq, ready, configEq⟩ := expired
    subst command
    exact ⟨ready, configEq⟩
  · obtain ⟨id, message, candidate, ready, commandEq, found, call, sender, _, _, configEq⟩ :=
      included
    have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (inputs.map State.initial)
      horizon historyScheduler trace
    have provenance := (app).history_provenance (inputs.map State.initial) horizon historyScheduler
      rawTrace
    obtain ⟨entry, recorded, _, _, emitted, _⟩ := provenance.pending message
      (List.mem_of_find?_eq_some found)
    rw [sender] at recorded
    have named : message.payload.call.event? graph = some event := by rw [call]; rfl
    obtain ⟨slot, declared⟩ := grammar entry recorded message emitted named
    have signed := runtime.signedCommitments_history leaks (inputs.map State.initial)
      (fun state supported => by
        obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact ⟨initial, rfl⟩) horizon historyScheduler rawTrace
    obtain ⟨_, material, submitted, materialCall⟩ := signed.emissions owner entry recorded message
      emitted
    rw [declared] at submitted
    cases Option.some.inj submitted
    have candidateEq : candidate = (owner, .prepared slot) :=
      (Payload.commitment.inj (call.symm.trans materialCall)).2
    subst candidate
    have meaning := runtime.onePacket_recorded_binding_result leaks bounds inputs horizon
      historyScheduler control trace owner entry recorded event payload result slot declared
    rw [meaning] at configEq
    subst command
    exact ⟨ready, configEq⟩

end Vegas.EventGraphRuntime

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Every actual surviving prefix of an activated selected-event run remains
in the concrete counted domain; arbitrary covered foreign policies persist. -/
theorem runJoint_countedSeedDomain_survives
    (localLaw : PMF Seed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (ordered : graph.RevealRelaxedOrdered) (owned : graph.actor? event = some owner)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (setup : graph.Inputs) (entered : Nat) (count : Nat)
    (execution : (app).Execution) (memory : LocalSeedMemory runtime leaks Seed RestSeed)
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks Seed RestSeed)
    (valid : execution.application.Invariant setup)
    (activated : execution.application.activatedAt event = some entered)
    (genuine : runtime.CountedSeedDomain leaks bounds inputs owner execution)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    runtime.CountedSeedDomain leaks bounds inputs owner next := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact genuine
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have first := runtime.reactive_dispatch_progress leaks setup players execution middle _
        valid moved
      obtain ⟨ticks, rest⟩ := controller.runJoint_progress localLaw remainderLaw remainder setup
        players count middle _ next after first.invariant later
      have middleUnfinished : event ∉ middle.application.config.cut.completed :=
        fun completed => unfinished (rest.completed completed)
      have middleDomain := runtime.countedSeedDomain_dispatch_of_activated_survives leaks bounds
        inputs ordered players covered owner event owned execution middle genuine setup valid
          entered activated _ moved middleUnfinished
      exact ih middle _ first.invariant
        (first.activated event entered activated middleUnfinished) middleDomain later

end Vegas.EventGraphRuntime.LocalSeedController

end
