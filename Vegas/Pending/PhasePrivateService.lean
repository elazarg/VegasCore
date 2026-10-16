/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhaseResolutionPersistence
import Vegas.Pending.PhaseSeedEmissionUnique

/-! # Physical event-private service on original counted histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction GameTheory.Protocol.ExecutionProtocol

variable {Player LocalSeed RestSeed : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "Seeds" => RestSeed × (PhaseSeedAddress graph → LocalSeed)
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

/-- Original coordinate-relative emission clocks remain recoverable after
the namespace retires. Transport identifiers are not part of this word. -/
def bindingEmissionClocks (coordinate : CommitAttemptEvent graph) (owner : Player)
    (execution : (app).Execution) : List Nat :=
  (PhaseSeedScheduler.localInput runtime leaks coordinate owner execution.environmentRecall
    (execution.observeEnvironment app)).emissions.map Prod.fst


/-- Genuine counted own recall detects every coordinate emission. With no own
packet for the coordinate, its retained physical emission clock word is empty. -/
theorem bindingEmissionClocks_eq_nil_of_unsent
    (scheduler : (app).Scheduler) (remaining : Nat) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate) :
    bindingEmissionClocks runtime leaks coordinate owner execution = [] := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have recalled := (app).history_inputRecall initial horizon scheduler raw
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks menu initial horizon
    scheduler remaining execution trace
  cases emissionsEq : (PhaseSeedScheduler.localInput runtime leaks coordinate owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions with
  | nil => simp only [bindingEmissionClocks, emissionsEq, List.map_nil]
  | cons emitted rest =>
      have authentic := PhaseSeedScheduler.localInput_emission_authentic runtime leaks execution
        coordinate owner words recalled emitted.1 emitted.2 (by
          rw [emissionsEq]; exact List.mem_cons_self)
      have ownOutput : emitted.2 ∈ (app).outputs (execution.recall owner) := by
        rw [← recalled owner]
        exact List.mem_filter.mpr ⟨authentic.1, by simp only [authentic.2.1, decide_true]⟩
      apply False.elim
      apply unsent emitted.2 ownOutput
      simp only [PhaseCount.event?, authentic.2.2.1, authentic.2.2.2, Option.map_some]

/-- An accepting receipt for this original physical binding. Both inputs and
receipts are retained through normalization, rollback and exhausted restore. -/
def BindingAccepted (coordinate : CommitAttemptEvent graph) (owner : Player)
    (execution : (app).Execution) : Prop :=
  ∃ message ∈ execution.network.inputs,
    message.sender = owner ∧ message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event ∧
        (message.id, true) ∈ execution.receipts

/-- The observable unsent local activation record is private to its original
coordinate seed. This constrains physical histories, not policy likelihoods. -/
def UnsentActivationPrivacy (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler) : Prop :=
  ∀ firstSeeds ∈ seedLaw.support, ∀ secondSeeds ∈ seedLaw.support,
    ∀ firstRemaining secondRemaining owner (first second : (app).Execution),
    ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨firstRemaining, some owner, first⟩) →
    ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨secondRemaining, some owner, second⟩) →
    ∀ coordinate : PhaseSeedAddress graph,
    first.application.SeedRequest owner coordinate.1 →
    second.application.SeedRequest owner coordinate.1 →
    firstSeeds.2 coordinate = secondSeeds.2 coordinate →
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner (first.recall owner)).length =
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (second.recall owner)).length →
    (∀ message ∈ (app).outputs (first.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1) →
    (∀ message ∈ (app).outputs (second.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1) →
    PhaseSeedScheduler.serviceClocks runtime leaks coordinate.1 owner
        (first.recall owner) (first.observe (app) owner) =
      PhaseSeedScheduler.serviceClocks runtime leaks coordinate.1 owner
        (second.recall owner) (second.observe (app) owner)

/-- A seed fixes a potential relative activation calendar. Every genuine
callback is its prefix; a resolved episode that never sends exhausts it.
The latter clause rules out suppressing a future activation through foreign
traffic. Automatically skipped events are excluded by the genuine ready prefix. -/
def PrivateActivationCalendar (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler) : Prop :=
  ∃ calendar : PhaseSeedAddress graph → LocalSeed → List Nat,
    (∀ seeds ∈ seedLaw.support, ∀ remaining owner (execution : (app).Execution),
      ((menu).protocol initial horizon (family seeds)).Trace
        (some ⟨remaining, some owner, execution⟩) →
      ∀ coordinate : PhaseSeedAddress graph,
      execution.application.SeedRequest owner coordinate.1 →
      (∀ message ∈ (app).outputs (execution.recall owner),
        PhaseCount.event? message.payload ≠ some coordinate.1) →
      PhaseSeedScheduler.serviceClocks runtime leaks coordinate.1 owner
          (execution.recall owner) (execution.observe (app) owner) <+:
        calendar coordinate (seeds.2 coordinate)) ∧
    (∀ seeds ∈ seedLaw.support, ∀ (last : (app).Control)
      (lastTrace : ((menu).protocol initial horizon (family seeds)).Trace (some last)),
      ∀ (coordinate : PhaseSeedAddress graph) owner,
      (∃ (before : (app).Control)
        (beforeTrace : ((menu).protocol initial horizon (family seeds)).Trace (some before)),
        TracePrefix beforeTrace lastTrace ∧
          before.execution.application.SeedRequest owner coordinate.1) →
      coordinate.1.Resolved last.execution.application →
      bindingEmissionClocks runtime leaks coordinate.1 owner last.execution = [] →
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (last.execution.recall owner)).map Prod.fst = calendar coordinate (seeds.2 coordinate))

theorem PrivateActivationCalendar.unsentPrivacy
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateCalendar : PrivateActivationCalendar runtime leaks bounds plan inputs horizon
      seedLaw family) :
    UnsentActivationPrivacy runtime leaks bounds plan inputs horizon seedLaw family := by
  obtain ⟨calendar, callbacks, _exhausted⟩ := privateCalendar
  intro firstSeeds firstSupport secondSeeds secondSupport firstRemaining secondRemaining owner
    first second firstTrace secondTrace coordinate firstRequest secondRequest sameSeed sameIndex
      firstUnsent secondUnsent
  have firstPrefix := callbacks firstSeeds firstSupport firstRemaining owner first firstTrace
    coordinate firstRequest firstUnsent
  have secondPrefix := callbacks secondSeeds secondSupport secondRemaining owner second secondTrace
    coordinate secondRequest secondUnsent
  have lengths : (PhaseSeedScheduler.serviceClocks runtime leaks coordinate.1 owner
      (first.recall owner) (first.observe (app) owner)).length =
      (PhaseSeedScheduler.serviceClocks runtime leaks coordinate.1 owner
        (second.recall owner) (second.observe (app) owner)).length := by
    simpa only [PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput,
      List.length_append, List.length_map, List.length_singleton] using
        congrArg (fun count : Nat => count + 1) sameIndex
  rw [List.prefix_iff_eq_take, sameSeed] at firstPrefix
  rw [List.prefix_iff_eq_take] at secondPrefix
  exact firstPrefix.trans ((congrArg (fun count =>
    (calendar coordinate (secondSeeds.2 coordinate)).take count) lengths).trans secondPrefix.symm)

/-- Among actual counted binding histories, resolved success depends only on
the original local seed and relative emission clocks. Exact inclusion times,
foreign traffic, private results and transport identifiers may differ. -/
def PrivateBindingSuccess (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler) : Prop :=
  ∀ firstSeeds ∈ seedLaw.support, ∀ secondSeeds ∈ seedLaw.support,
    ∀ (first second : (app).Control),
    ((menu).protocol initial horizon (family firstSeeds)).Trace (some first) →
    ((menu).protocol initial horizon (family secondSeeds)).Trace (some second) →
    ∀ (coordinate : PhaseSeedAddress graph) owner payload,
    graph.outputLayout coordinate.1.event = .binding owner payload →
    coordinate.1.Resolved first.execution.application →
    coordinate.1.Resolved second.execution.application →
    firstSeeds.2 coordinate = secondSeeds.2 coordinate →
    bindingEmissionClocks runtime leaks coordinate.1 owner first.execution =
      bindingEmissionClocks runtime leaks coordinate.1 owner second.execution →
    (BindingAccepted runtime leaks coordinate.1 owner first.execution ↔
      BindingAccepted runtime leaks coordinate.1 owner second.execution)

/-- Actual counted histories contain only one packet for this physical binding.
Consequently the strong service packet quotient compares any two permitted
first envelopes emitted at the same relative clock, including different
prepared handles, transport identifiers and private preparations. -/
theorem PrivateBindingSuccess.accepted_iff_of_emission_clock
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateSuccess : PrivateBindingSuccess runtime leaks bounds plan inputs horizon seedLaw family)
    (firstSeeds : Seeds) (firstSupport : firstSeeds ∈ seedLaw.support)
    (secondSeeds : Seeds) (secondSupport : secondSeeds ∈ seedLaw.support)
    (firstRemaining secondRemaining : Nat) (first second : (app).Execution)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨firstRemaining, none, first⟩))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨secondRemaining, none, second⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player) (payload : L.Ty)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (firstResolved : coordinate.1.Resolved first.application)
    (secondResolved : coordinate.1.Resolved second.application)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (clock : Nat) (firstMessage secondMessage : Message Player (CommitAttemptPacket graph))
    (firstEmission : (clock, firstMessage) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner first.environmentRecall
        (first.observeEnvironment app)).emissions)
    (secondEmission : (clock, secondMessage) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner second.environmentRecall
        (second.observeEnvironment app)).emissions) :
    BindingAccepted runtime leaks coordinate.1 owner first ↔
      BindingAccepted runtime leaks coordinate.1 owner second := by
  have singleton (seeds : Seeds) (remaining : Nat) (execution : (app).Execution)
      (trace : ((menu).protocol initial horizon (family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
      (message : Message Player (CommitAttemptPacket graph))
      (emitted : (clock, message) ∈
        (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
          (execution.observeEnvironment app)).emissions) :
      bindingEmissionClocks runtime leaks coordinate.1 owner execution = [clock] := by
    have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks menu initial horizon
      (family seeds) remaining execution trace
    have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds (family seeds)).history
      initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
    have raw := (menu).toRawTrace initial horizon (family seeds) trace
    have unique := (app).input_identifier_injective_history initial horizon (family seeds)
      ⟨remaining, none, execution⟩ raw
    have packets := PhaseSeedScheduler.localInput_emissions_eq_singleton runtime leaks execution
      coordinate.1 owner words clean
      (fun first firstInput second secondInput same =>
        unique first second firstInput secondInput same) clock message emitted
    simp only [bindingEmissionClocks, packets, List.map_cons, List.map_nil]
  have clocks : bindingEmissionClocks runtime leaks coordinate.1 owner first =
      bindingEmissionClocks runtime leaks coordinate.1 owner second :=
    (singleton firstSeeds firstRemaining first firstTrace firstMessage firstEmission).trans
      (singleton secondSeeds secondRemaining second secondTrace secondMessage secondEmission).symm
  exact privateSuccess firstSeeds firstSupport secondSeeds secondSupport
    ⟨firstRemaining, none, first⟩ ⟨secondRemaining, none, second⟩ firstTrace secondTrace coordinate
      owner payload output firstResolved secondResolved sameSeed clocks

/-- Permitted first packets emitted at corresponding unsent callbacks have
identical resolved success. The calendar derives their clock equality;
counted uniqueness removes every handle, preparation and nonce from the
physical success comparison. Endpoints retain the original attempt's receipts. -/
theorem PrivateActivationCalendar.accepted_iff_of_callbacks
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateCalendar : PrivateActivationCalendar runtime leaks bounds plan inputs horizon
      seedLaw family)
    (privateSuccess : PrivateBindingSuccess runtime leaks bounds plan inputs horizon seedLaw family)
    (firstSeeds : Seeds) (firstSupport : firstSeeds ∈ seedLaw.support)
    (secondSeeds : Seeds) (secondSupport : secondSeeds ∈ seedLaw.support)
    (firstRemaining secondRemaining firstFinalRemaining secondFinalRemaining : Nat)
    (owner : Player) (first second firstFinal secondFinal : (app).Execution)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨firstRemaining, some owner, first⟩))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨secondRemaining, some owner, second⟩))
    (firstFinalTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨firstFinalRemaining, none, firstFinal⟩))
    (secondFinalTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨secondFinalRemaining, none, secondFinal⟩))
    (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (firstRequest : first.application.SeedRequest owner coordinate.1)
    (secondRequest : second.application.SeedRequest owner coordinate.1)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (sameIndex : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.recall owner)).length = (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1
        owner (second.recall owner)).length)
    (firstUnsent : ∀ message ∈ (app).outputs (first.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1)
    (secondUnsent : ∀ message ∈ (app).outputs (second.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1)
    (firstResolved : coordinate.1.Resolved firstFinal.application)
    (secondResolved : coordinate.1.Resolved secondFinal.application)
    (firstMessage secondMessage : Message Player (CommitAttemptPacket graph))
    (firstEmission :
      ((PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (first.recall owner) (first.observe app owner)).elapsed, firstMessage) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner firstFinal.environmentRecall
        (firstFinal.observeEnvironment app)).emissions)
    (secondEmission :
      ((PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (second.recall owner) (second.observe app owner)).elapsed, secondMessage) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner secondFinal.environmentRecall
        (secondFinal.observeEnvironment app)).emissions) :
    BindingAccepted runtime leaks coordinate.1 owner firstFinal ↔
      BindingAccepted runtime leaks coordinate.1 owner secondFinal := by
  have sameClocks := PrivateActivationCalendar.unsentPrivacy runtime leaks bounds plan inputs
    horizon
    seedLaw family privateCalendar firstSeeds firstSupport secondSeeds secondSupport
      firstRemaining secondRemaining owner first second firstTrace secondTrace coordinate
        firstRequest secondRequest sameSeed sameIndex firstUnsent secondUnsent
  have elapsed := congrArg List.getLast? sameClocks
  simp only [PhaseSeedScheduler.serviceClocks, List.getLast?_append_cons, List.getLast?_singleton,
    Option.some.injEq] at elapsed
  rw [← elapsed] at secondEmission
  exact PrivateBindingSuccess.accepted_iff_of_emission_clock runtime leaks bounds plan inputs
    horizon
    seedLaw family privateSuccess firstSeeds firstSupport secondSeeds secondSupport
      firstFinalRemaining secondFinalRemaining firstFinal secondFinal firstFinalTrace
        secondFinalTrace
        coordinate owner payload output firstResolved secondResolved sameSeed _ firstMessage
          secondMessage firstEmission secondEmission

/-- The actual normalized reference has the same SEND/WAIT law at two genuine
unsent callbacks with the same local seed and activation index. Original typed
source laws and all foreign/private physical state may be different. -/
theorem bindingServiceReference_transmission_eq
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateCalendar :
      PrivateActivationCalendar runtime leaks bounds plan inputs horizon seedLaw family)
    (capacity : horizon ≤ bounds.candidateCount)
    (firstSeeds : Seeds) (firstSupport : firstSeeds ∈ seedLaw.support)
    (secondSeeds : Seeds) (secondSupport : secondSeeds ∈ seedLaw.support)
    (firstRemaining secondRemaining : Nat) (owner : Player) (first second : (app).Execution)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨firstRemaining, some owner, first⟩))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨secondRemaining, some owner, second⟩))
    (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (firstRequest : first.application.SeedRequest owner coordinate.1)
    (secondRequest : second.application.SeedRequest owner coordinate.1)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (sameIndex : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.recall owner)).length = (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1
        owner (second.recall owner)).length)
    (firstUnsent : ∀ message ∈ (app).outputs (first.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1)
    (secondUnsent : ∀ message ∈ (app).outputs (second.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (firstValues secondValues : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool)
    (failure timing : ℝ) (firstNonnegative : 0 ≤ failure + timing)
    (firstBounded : failure + timing ≤ 1) (timingNonnegative : 0 ≤ timing)
    (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1) :
    (PhaseCount.bindingServiceReference runtime leaks bounds owner coordinate.1 payload
        firstValues choose failure timing firstNonnegative firstBounded timingNonnegative
          timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative
            rawBounded (first.recall owner) (first.observe (app) owner)).map
        (fun response => response.transmission.isSome) =
      (PhaseCount.bindingServiceReference runtime leaks bounds owner coordinate.1 payload
        secondValues choose failure timing firstNonnegative firstBounded timingNonnegative
          timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative
            rawBounded (second.recall owner) (second.observe (app) owner)).map
        (fun response => response.transmission.isSome) := by
  have privateActivations := PrivateActivationCalendar.unsentPrivacy runtime leaks bounds plan
    inputs horizon seedLaw family privateCalendar
  have clocks := privateActivations firstSeeds firstSupport secondSeeds secondSupport
    firstRemaining secondRemaining owner first second firstTrace secondTrace coordinate
      firstRequest secondRequest sameSeed sameIndex firstUnsent secondUnsent
  have firstCoordinate : coordinate.1 = ⟨first.application.attempt, coordinate.1.event⟩ := by
    cases coordinate with
    | mk coordinate _bounded =>
      cases coordinate with
      | mk attempt event => exact congrArg (fun attempt : CommitAttemptId =>
          (⟨attempt, event⟩ : CommitAttemptEvent graph)) firstRequest.1
  have secondCoordinate : coordinate.1 = ⟨second.application.attempt, coordinate.1.event⟩ := by
    cases coordinate with
    | mk coordinate _bounded =>
      cases coordinate with
      | mk attempt event => exact congrArg (fun attempt : CommitAttemptId =>
          (⟨attempt, event⟩ : CommitAttemptEvent graph)) secondRequest.1
  have firstLaw := PhaseCount.bindingServiceReference_transmission_of_history runtime leaks bounds
    owner coordinate.1.event payload firstValues choose failure timing firstNonnegative
      firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
        rawNonnegative rawBounded menu plan inputs horizon (family firstSeeds) capacity
          ⟨firstRemaining, some owner, first⟩ firstTrace rfl output
            (firstCoordinate ▸ firstRequest) (firstCoordinate ▸ firstUnsent) catalogue
  have secondLaw := PhaseCount.bindingServiceReference_transmission_of_history runtime leaks bounds
    owner coordinate.1.event payload secondValues choose failure timing firstNonnegative
      firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
        rawNonnegative rawBounded menu plan inputs horizon (family secondSeeds) capacity
          ⟨secondRemaining, some owner, second⟩ secondTrace rfl output
            (secondCoordinate ▸ secondRequest) (secondCoordinate ▸ secondUnsent) catalogue
  rw [← firstCoordinate] at firstLaw
  rw [← secondCoordinate] at secondLaw
  exact firstLaw.trans ((congrArg (fun clocks => PhaseCount.bindingServiceEmissionLaw clocks
    choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded rawWeight
      rawNonnegative rawBounded) clocks).trans secondLaw.symm)

end Vegas.EventGraphRuntime.PhaseService
