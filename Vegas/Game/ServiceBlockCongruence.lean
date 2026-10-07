/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceDeviationTraffic
import Vegas.Game.ServiceAssignedPolicy
import Vegas.Game.ServiceBlockRun

/-! # A block of decided bindings against one deviating player

In a block of binding events, every player but one deviator follows its
first-turn client with its decisions at the block's events fixed in advance
(`Vegas.assignedTurnPolicy`), while the deviator follows an arbitrary native
policy. The deviator's traffic at the end of the block has a law that depends on
the execution only through its traffic at the start, and not at all on the
fixed decisions: every commitment carries the same public envelope whatever
private value it binds, and the owners' responses, turn counts and records at
the block's events are the same on both sides (`Vegas.decidedBlock_readout_congr`).

* `Vegas.runUntil_map_congr_of_rounds` turns a congruence of single rounds,
  under per-side invariants, into a congruence of whole stopped runs;
* `Vegas.blockRound_readout_congr` is the congruence of one round of the
  block, for the deviator's traffic together with every other owner's turn
  counts and records at the block's events (`Vegas.blockReadout`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

section Simulation

variable {Principal : Type} [DecidableEq Principal] {β : Type*}
  (app : ReactiveApplication Principal)

/-- **Stopped runs from a round congruence.** Two profiles whose single rounds
have equal laws of a readout `ψ` from executions with equal readouts, under
per-side invariants that rounds keep and that determine when to stop, have
equal laws of `ψ` after any number of stopped rounds. The invariants are indexed
by the rounds still to run. -/
theorem runUntil_map_congr_of_rounds (scheduler : app.Scheduler)
    (first second : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (ψ : app.Execution → β) (leftHolds rightHolds : Nat → app.Execution → Prop)
    (stops : ∀ n left right, leftHolds n left → rightHolds n right → ψ left = ψ right →
      (stop left ↔ stop right))
    (rounds : ∀ n left right, leftHolds (n + 1) left → rightHolds (n + 1) right →
      ψ left = ψ right → ¬ stop left →
      (app.round scheduler first left).map ψ = (app.round scheduler second right).map ψ)
    (leftStep : ∀ n left, leftHolds (n + 1) left → ¬ stop left →
      ∀ next ∈ (app.round scheduler first left).support, leftHolds n next)
    (rightStep : ∀ n right, rightHolds (n + 1) right → ¬ stop right →
      ∀ next ∈ (app.round scheduler second right).support, rightHolds n next) :
    ∀ count left right, leftHolds count left → rightHolds count right → ψ left = ψ right →
      (app.runUntil scheduler first stop count left).map ψ =
        (app.runUntil scheduler second stop count right).map ψ := by
  intro count
  induction count with
  | zero =>
      intro left right _ _ same
      simp only [ReactiveApplication.runUntil, PMF.pure_map]
      exact congrArg PMF.pure same
  | succ count ih =>
      intro left right leftValid rightValid same
      by_cases halted : stop left
      · have rightHalted := (stops _ left right leftValid rightValid same).mp halted
        rw [app.runUntil_of_stop scheduler first stop _ left halted,
          app.runUntil_of_stop scheduler second stop _ right rightHalted, PMF.pure_map,
          PMF.pure_map]
        exact congrArg PMF.pure same
      · have rightRunning : ¬ stop right := fun rightHalted =>
          halted ((stops _ left right leftValid rightValid same).mpr rightHalted)
        simp only [ReactiveApplication.runUntil, halted, rightRunning, ↓reduceIte, PMF.map_bind]
        apply bind_eq_of_map_eq _ _ _ _ (rounds count left right leftValid rightValid same halted)
        intro next nextReached other otherReached equal
        exact ih next other (leftStep count left leftValid halted next nextReached)
          (rightStep count right rightValid rightRunning other otherReached) equal

end Simulation

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section Decided

/-- The owner's recorded turns at `event`. -/
def ownerTurns (owner : Player) (event : (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Nat :=
  (execution.recall owner).countP fun entry =>
    decide (entry.beforeView.application.publicView.ownTurn? owner = some event)

/-- While `event` is ready, an input of its owner is its turn there, counted
by the owner's recorded turns. -/
theorem serviceTurn_of_ready {owner : Player} {event : (serviceGraph setup mode).EventId}
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    serviceTurn setup mode deadline leaks owner event (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      some (ownerTurns owner event execution) := by
  unfold serviceTurn ownerTurns
  split
  · rfl
  · rename_i idle
    exact (idle (serviceOwnTurn?_of_ready setup execution.application ready owned)).elim

/-- Away from an unrecorded first turn that still fits the deadline, the
decided policy is silent. -/
theorem decidedTurnPolicy_closed {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (closed : ¬ (ownerTurns owner event execution = 0 ∧
      (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall owner) event =
        false ∧
      execution.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
        bound event)) :
    decidedTurnPolicy setup leaks bound owner event action (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ⟨none⟩ := by
  have turn := serviceTurn_of_ready execution ready owned
  unfold decidedTurnPolicy
  by_cases first : ownerTurns owner event execution = 0
  · rw [(serviceApplication setup mode deadline leaks).turnScheduledPolicy_selected _ (0 : Fin 1)
      _ _ _ _ (by rw [turn, first]; rfl)]
    unfold decidedOpportunity
    by_cases recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (execution.recall owner) event = true
    · simp only [recorded, ↓reduceIte, ReactiveApplication.silentPolicy_apply]
    · have unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
          (execution.recall owner) event = false := by simpa using recorded
      have late : ¬ execution.application.publicView.InclusionFitsDeadline
          (serviceRuntime setup mode deadline) bound event := fun fits =>
        closed ⟨first, unrecorded, fits⟩
      have lateView : ¬ (execution.observe (serviceApplication setup mode deadline leaks)
          owner).application.publicView.InclusionFitsDeadline
            (serviceRuntime setup mode deadline) bound event := late
      simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, lateView,
        ReactiveApplication.silentPolicy_apply]
  · rw [(serviceApplication setup mode deadline leaks).turnScheduledPolicy_unselected _ _ _ _ _ _
      (by
        intro slot chosen
        rw [turn]
        intro equal
        exact first ((Option.some.inj equal).trans
          ((Fin.val_eq_zero slot).trans (by rfl))))]
    rfl

/-- At an unrecorded first turn, the decided policy is its opportunity. -/
theorem decidedTurnPolicy_open {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (first : ownerTurns owner event execution = 0) :
    decidedTurnPolicy setup leaks bound owner event action (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      decidedOpportunity setup leaks bound owner event action (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) := by
  have turn := serviceTurn_of_ready execution ready owned
  unfold decidedTurnPolicy
  rw [(serviceApplication setup mode deadline leaks).turnScheduledPolicy_selected _ (0 : Fin 1)
    _ _ _ _ (by rw [turn, first]; rfl)]

/-- An opportunity that transmits a given decision. -/
theorem decidedOpportunity_transmits {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (execution.recall owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (decision : (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
      (execution.recall owner) (execution.observe (serviceApplication setup mode deadline leaks)
        owner) event action = ⟨some material⟩) :
    decidedOpportunity setup leaks bound owner event action (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ⟨some material⟩ := by
  have fitsView : (execution.observe (serviceApplication setup mode deadline leaks)
      owner).application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
        bound event := fits
  unfold decidedOpportunity
  simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fitsView, decision, reduceCtorEq]

/-- An opportunity whose decision is silent is silent. -/
theorem decidedOpportunity_silent {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (quiet : ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
      (execution.recall owner) (execution.observe (serviceApplication setup mode deadline leaks)
        owner) event action).transmission = none) :
    decidedOpportunity setup leaks bound owner event action (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ⟨none⟩ := by
  unfold decidedOpportunity
  simp only [quiet, ↓reduceIte, ReactiveApplication.silentPolicy_apply]
  split_ifs <;> rfl

/-- Another player's response that transmits the same packet as its
counterpart, or is silent with it, keeps equal deviator traffic. -/
theorem bindingTraffic_respond_other {who actor : Player} (different : who ≠ actor)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right)
    (leftResponse rightResponse : (serviceApplication setup mode deadline leaks).Action)
    (packets : (leftResponse.transmission = none ∧ rightResponse.transmission = none) ∨
      ∃ leftMaterial rightMaterial, leftResponse = ⟨some leftMaterial⟩ ∧
        rightResponse = ⟨some rightMaterial⟩ ∧
        (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit left.application actor
              leftMaterial) actor (left.network.known actor) leftMaterial =
          (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit right.application actor
              rightMaterial) actor (right.network.known actor) rightMaterial) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (left.respond (serviceApplication setup mode deadline leaks) actor leftResponse) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (right.respond (serviceApplication setup mode deadline leaks) actor rightResponse) := by
  let app := serviceApplication setup mode deadline leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall who = right.recall who := congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  have kept (execution : app.Execution) (response : app.Action) :
      (execution.respond app actor response).application.playerView who =
        execution.application.playerView who := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        exact (submitStep_playerView_other (material.call.register execution.application actor)
          actor who different material.call.packet).trans
            (material.call.register_other execution.application actor who different)
  have afterViews : (left.respond app actor leftResponse).application.playerView who =
      (right.respond app actor rightResponse).application.playerView who := by
    rw [kept, kept, views]
  have afterNetworks : (left.respond app actor leftResponse).network =
      (right.respond app actor rightResponse).network := by
    rcases packets with ⟨leftQuiet, rightQuiet⟩ | ⟨leftMaterial, rightMaterial, rfl, rfl, packet⟩
    · rcases leftResponse with ⟨leftTransmission⟩
      rcases rightResponse with ⟨rightTransmission⟩
      change leftTransmission = none at leftQuiet
      change rightTransmission = none at rightQuiet
      subst leftQuiet rightQuiet
      exact networks
    · simp only [ReactiveApplication.Execution.respond]
      rw [packet, networks]
  refine Prod.ext afterNetworks (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_
    (Prod.ext afterViews (congrArg PlayerView.publicView afterViews)))))
  · exact receipts
  · exact environments
  · change (left.respond app actor leftResponse).recall who =
      (right.respond app actor rightResponse).recall who
    rw [app.respond_recall_other left actor who different,
      app.respond_recall_other right actor who different, recalled]

/-- While every ready event is a binding, an opening addressed to any event is
rejected. -/
theorem handle_opening_none_of_bindings (state : EventGraphRuntime.State (serviceGraph setup mode))
    (bindings : ∀ event, state.config.cut.Ready event →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (other : (serviceGraph setup mode).EventId)
    (candidate : Handle (serviceGraph setup mode)) (raw : Raw L) :
    handle (serviceRuntime setup mode deadline) state ⟨id, .opening other candidate raw⟩ =
      none := by
  by_cases otherReady : state.config.cut.Ready other
  · obtain ⟨owner, payload, outputEq, codeEq, node⟩ := bindings other otherReady
    by_cases timely : state.WithinDeadline (serviceRuntime setup mode deadline) other
    · simp [handle, otherReady, timely, node]
    · simp [handle, otherReady, timely]
  · simp [handle, otherReady]

/-- At an unrecorded first turn that fits the deadline, at which the owner's
counted slot is used canonically, the decided binding transmits the canonical
commitment at the counted slot. -/
theorem decidedBinding_response {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (action : (serviceGraph setup mode).Action event)
    {current : (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩))
    (own : OwnSubmissionsAtTurn setup leaks current owner)
    (slots : CanonicalSlotsUsed setup leaks current owner)
    (ready : current.application.config.cut.Ready event)
    (selected : (.activate owner : (serviceApplication setup mode deadline leaks).Command) ∈
      (scheduler current.environmentRecall
        (current.observeEnvironment (serviceApplication setup mode deadline leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup mode deadline leaks).observePending owner
      current.network.pending).support)
    (first : ownerTurns owner event current = 0)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (current.recall owner) event = false)
    (fits : current.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event) :
    let active := current.sampledActivation (serviceApplication setup mode deadline leaks) owner
      sample
    decidedTurnPolicy setup leaks bound owner event action (active.recall owner)
        (active.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ((serviceRuntime setup mode deadline).reactiveBinding leaks owner event payload
        (cast (congrArg EventGraph.EventField.Action outputEq) action)
        (current.application.publicView.bindingCount owner)) := by
  intro active
  let app := serviceApplication setup mode deadline leaks
  have owned : (serviceGraph setup mode).actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  have moved : active ∈ (current.environmentStep app (.activate owner)).support := by
    rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
    exact ⟨sample, sampled, rfl⟩
  obtain ⟨activeTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
    scheduler remaining current active (.activate owner) trace selected moved
  have turn : active.application.publicView.ownTurn? owner = some event :=
    serviceOwnTurn?_of_ready setup current.application ready owned
  have fresh := canonicalSlot_fresh_of_used activeTrace owner own slots event turn unrecorded
  have canonical := canonicalFreshSlot_canonical owner (active.observe app owner).application
    fresh
  have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (cast (congrArg EventGraph.EventField.Action outputEq) action) := by
    simp only [cast_cast, cast_eq]
  have decision := (serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks
    owner (active.recall owner) (active.observe app owner) event payload outputEq codeEq node _
    canonical (cast (congrArg EventGraph.EventField.Action outputEq) action)
  rw [← actionEq] at decision
  rw [decidedTurnPolicy_open action active ready owned first,
    decidedOpportunity_transmits action active unrecorded fits _ decision]
  rfl

end Decided

section Block

/-- Every other player's turn counts and records at the events of a block. -/
def blockMarks (who : Player) (low high : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Player → (serviceGraph setup mode).EventId → Nat × Bool := fun owner event =>
  if owner ≠ who ∧ low ≤ event.val ∧ event.val < high then
    (ownerTurns owner event execution,
      (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall owner) event)
  else (0, false)

/-- The readout compared across a block: the deviator's traffic and every
other player's turn counts and records at the block's events. -/
def blockReadout (who : Player) (low high : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :=
  ((serviceRuntime setup mode deadline).bindingTraffic leaks who execution,
    blockMarks who low high execution)

/-- The players of a block: `who` follows `deviation`, every other player its
first-turn client with the assigned decisions. -/
abbrev blockPlayers (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (assignment : Assignment setup mode) :
    Player → (serviceApplication setup mode deadline leaks).Policy :=
  Function.update (fun player => assignedTurnPolicy bound turns profile player assignment) who
    deviation

/-- Marks read only the players' recalls. -/
theorem blockMarks_of_recall (who : Player) (low high : Nat)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (kept : next.recall = execution.recall) :
    blockMarks who low high next = blockMarks who low high execution := by
  funext owner event
  simp only [blockMarks, ownerTurns, kept]

/-- Two responses at equal public views that submit for the same event keep
equal marks. -/
theorem blockMarks_respond (who : Player) (low high : Nat)
    {left right : (serviceApplication setup mode deadline leaks).Execution} (actor : Player)
    (same : blockMarks who low high left = blockMarks who low high right)
    (publics : left.application.publicView = right.application.publicView)
    (leftResponse rightResponse : (serviceApplication setup mode deadline leaks).Action)
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
      (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse) :
    blockMarks who low high
        (left.respond (serviceApplication setup mode deadline leaks) actor leftResponse) =
      blockMarks who low high
        (right.respond (serviceApplication setup mode deadline leaks) actor rightResponse) := by
  funext owner event
  have before := congrFun (congrFun same owner) event
  by_cases inside : owner ≠ who ∧ low ≤ event.val ∧ event.val < high
  · obtain ⟨different, lower, upper⟩ := inside
    simp only [blockMarks, different, ne_eq, not_false_eq_true, lower, upper, and_self,
      ↓reduceIte, Prod.mk.injEq] at before ⊢
    obtain ⟨turnsEq, recordedEq⟩ := before
    by_cases isActor : owner = actor
    · subst owner
      obtain ⟨leftEmitted, leftRecalled, _⟩ := respond_recall_self setup leaks left actor
        leftResponse
      obtain ⟨rightEmitted, rightRecalled, _⟩ := respond_recall_self setup leaks right actor
        rightResponse
      have views : (left.observe (serviceApplication setup mode deadline leaks)
            actor).application.publicView =
          (right.observe (serviceApplication setup mode deadline leaks)
            actor).application.publicView := publics
      unfold ownerTurns at turnsEq ⊢
      unfold EventGraphRuntime.eventRecorded at recordedEq ⊢
      refine ⟨?_, ?_⟩
      · rw [leftRecalled, rightRecalled, List.countP_append, List.countP_append, turnsEq]
        simp only [List.countP_singleton, views]
      · rw [leftRecalled, rightRecalled, List.any_append, List.any_append, recordedEq]
        simp only [List.any_cons, List.any_nil, Bool.or_false, submitted]
    · rw [(serviceApplication setup mode deadline leaks).respond_recall_other left actor owner
          isActor,
        (serviceApplication setup mode deadline leaks).respond_recall_other right actor owner
          isActor]
      unfold ownerTurns at turnsEq ⊢
      rw [(serviceApplication setup mode deadline leaks).respond_recall_other left actor owner
          isActor,
        (serviceApplication setup mode deadline leaks).respond_recall_other right actor owner
          isActor]
      exact ⟨turnsEq, recordedEq⟩
  · simp only [blockMarks, inside, ↓reduceIte]

/-- The silent first-turn client away from its turns. -/
theorem assignedTurnPolicy_idle {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {owner : Player}
    {assignment : Assignment setup mode}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    (idle : view.application.publicView.ownTurn? owner = none) :
    assignedTurnPolicy bound turns profile owner assignment past view =
      PMF.pure ⟨none⟩ := by
  simp only [assignedTurnPolicy, idle, serviceTurnPolicy,
    ReactiveApplication.silentPolicy_apply]

/-- **Another owner's response in a block.** At an activation of a player
other than the deviator, on two executions with equal readouts whose ready
events lie in a block of assigned bindings, the player's two responses are
deterministic, submit for the same event and leave equal deviator traffic. -/
theorem blockResponse_matched {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who actor : Player} (honest : actor ≠ who)
    {low high : Nat} (leftAssignment rightAssignment : Assignment setup mode)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : blockReadout who low high left = blockReadout who low high right)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (inBlock : ∀ event, left.application.config.cut.Ready event →
      low ≤ event.val ∧ event.val < high)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (leftAssigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∃ action, leftAssignment event = some action)
    (rightAssigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∃ action, rightAssignment event = some action)
    (leftOwn : OwnSubmissionsAtTurn setup leaks left actor)
    (leftSlots : CanonicalSlotsUsed setup leaks left actor)
    (rightOwn : OwnSubmissionsAtTurn setup leaks right actor)
    (rightSlots : CanonicalSlotsUsed setup leaks right actor)
    (selected : (.activate actor : (serviceApplication setup mode deadline leaks).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (serviceApplication setup mode deadline leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup mode deadline leaks).observePending actor
      left.network.pending).support) :
    let leftActive := left.sampledActivation (serviceApplication setup mode deadline leaks)
      actor sample
    let rightActive := right.sampledActivation (serviceApplication setup mode deadline leaks)
      actor sample
    ∃ leftResponse rightResponse,
      assignedTurnPolicy bound turns profile actor leftAssignment (leftActive.recall actor)
          (leftActive.observe (serviceApplication setup mode deadline leaks) actor) =
        PMF.pure leftResponse ∧
      assignedTurnPolicy bound turns profile actor rightAssignment (rightActive.recall actor)
          (rightActive.observe (serviceApplication setup mode deadline leaks) actor) =
        PMF.pure rightResponse ∧
      (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
        (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse ∧
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (leftActive.respond (serviceApplication setup mode deadline leaks) actor
            leftResponse) =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (rightActive.respond (serviceApplication setup mode deadline leaks) actor
            rightResponse) := by
  intro leftActive rightActive
  let app := serviceApplication setup mode deadline leaks
  have sameTraffic := congrArg Prod.fst same
  have sameMarks : blockMarks who low high left = blockMarks who low high right :=
    congrArg Prod.snd same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have cuts := cut_eq_of_publicView_eq publics
  have activated : (serviceRuntime setup mode deadline).bindingTraffic leaks who leftActive =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who rightActive :=
    bindingTraffic_activation (serviceRuntime setup mode deadline) leaks left right who actor
      sameTraffic sample
  have whoActor : who ≠ actor := fun equal => honest equal.symm
  cases turn : left.application.publicView.ownTurn? actor with
  | none =>
      have leftIdle : (leftActive.observe app actor).application.publicView.ownTurn? actor =
          none := turn
      have rightIdle : (rightActive.observe app actor).application.publicView.ownTurn? actor =
          none := by
        change right.application.publicView.ownTurn? actor = none
        rw [← publics]
        exact turn
      exact ⟨⟨none⟩, ⟨none⟩, assignedTurnPolicy_idle leftIdle, assignedTurnPolicy_idle rightIdle,
        rfl, bindingTraffic_respond_other whoActor activated ⟨none⟩ ⟨none⟩
          (Or.inl ⟨rfl, rfl⟩)⟩
  | some event =>
      obtain ⟨seen, owned⟩ := PublicView.ownTurn?_spec _ actor event turn
      have leftReady : left.application.config.cut.Ready event :=
        (left.application.publicView_eventReady event).mp seen
      have rightReady : right.application.config.cut.Ready event := by
        rw [← cuts]
        exact leftReady
      obtain ⟨lower, upper⟩ := inBlock event leftReady
      obtain ⟨leftAction, leftAssignedEq⟩ := leftAssigned event actor lower upper owned honest
      obtain ⟨rightAction, rightAssignedEq⟩ := rightAssigned event actor lower upper owned honest
      have leftTurn : (leftActive.observe app actor).application.publicView.ownTurn? actor =
          some event := turn
      have rightTurn : (rightActive.observe app actor).application.publicView.ownTurn? actor =
          some event := by
        change right.application.publicView.ownTurn? actor = some event
        rw [← publics]
        exact turn
      rw [assignedTurnPolicy_assigned leftTurn leftAssignedEq,
        assignedTurnPolicy_assigned rightTurn rightAssignedEq]
      have marksAt := congrFun (congrFun sameMarks actor) event
      simp only [blockMarks, honest, ne_eq, not_false_eq_true, lower, upper, and_self,
        ↓reduceIte, Prod.mk.injEq] at marksAt
      obtain ⟨sameTurns, sameRecorded⟩ := marksAt
      have leftActiveReady : leftActive.application.config.cut.Ready event := leftReady
      have rightActiveReady : rightActive.application.config.cut.Ready event := rightReady
      by_cases opened : ownerTurns actor event left = 0 ∧
          (serviceRuntime setup mode deadline).eventRecorded leaks (left.recall actor) event =
            false ∧
          left.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
            bound event
      · obtain ⟨first, unrecorded, fits⟩ := opened
        obtain ⟨owner, payload, outputEq, codeEq, node⟩ := bindings event lower upper
        have ownerIs : owner = actor := Option.some.inj
          ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
        subst ownerIs
        have rightFirst : ownerTurns owner event right = 0 := sameTurns ▸ first
        have rightUnrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
            (right.recall owner) event = false := sameRecorded ▸ unrecorded
        have rightFits : right.application.publicView.InclusionFitsDeadline
            (serviceRuntime setup mode deadline) bound event := publics ▸ fits
        have counts : left.application.publicView.bindingCount owner =
            right.application.publicView.bindingCount owner := by rw [publics]
        refine ⟨(serviceRuntime setup mode deadline).reactiveBinding leaks owner event payload
            (cast (congrArg EventGraph.EventField.Action outputEq) leftAction)
            (left.application.publicView.bindingCount owner),
          (serviceRuntime setup mode deadline).reactiveBinding leaks owner event payload
            (cast (congrArg EventGraph.EventField.Action outputEq) rightAction)
            (right.application.publicView.bindingCount owner), ?_, ?_, rfl, ?_⟩
        · exact decidedBinding_response outputEq codeEq node leftAction leftTrace leftOwn
            leftSlots leftReady selected sample sampled first unrecorded fits
        · exact decidedBinding_response outputEq codeEq node rightAction rightTrace rightOwn
            rightSlots rightReady (by
              rw [← environments, ← observeEnvironment_eq_of_bindingTraffic who sameTraffic]
              exact selected)
            sample (by
              rw [← networks]
              exact sampled) rightFirst rightUnrecorded rightFits
        · apply bindingTraffic_respond_other whoActor activated
          refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
          have activePublics : leftActive.application.publicView =
              rightActive.application.publicView := publics
          rw [reactiveApplication_packet_none, reactiveApplication_packet_none, counts,
            activePublics]
      · have rightClosed : ¬ (ownerTurns actor event right = 0 ∧
            (serviceRuntime setup mode deadline).eventRecorded leaks (right.recall actor) event =
              false ∧
            right.application.publicView.InclusionFitsDeadline
              (serviceRuntime setup mode deadline) bound event) := by
          rw [← sameTurns, ← sameRecorded, ← publics]
          exact opened
        exact ⟨⟨none⟩, ⟨none⟩,
          decidedTurnPolicy_closed leftAction leftActive leftActiveReady owned opened,
          decidedTurnPolicy_closed rightAction rightActive rightActiveReady owned rightClosed,
          rfl, bindingTraffic_respond_other whoActor activated ⟨none⟩ ⟨none⟩
            (Or.inl ⟨rfl, rfl⟩)⟩

/-- **One round of a block.** On two executions with equal readouts whose ready
events lie in a block of bindings, every one of them assigned on both sides
for owners other than the deviator, one round of the block's players gives
equal laws of the readout, whatever the assigned values. -/
theorem blockRound_readout_congr {horizon leftRemaining rightRemaining : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {low high : Nat} (leftAssignment rightAssignment : Assignment setup mode)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : blockReadout who low high left = blockReadout who low high right)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (inBlock : ∀ event, left.application.config.cut.Ready event →
      low ≤ event.val ∧ event.val < high)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (leftAssigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∃ action, leftAssignment event = some action)
    (rightAssigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∃ action, rightAssignment event = some action)
    (leftOwn : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks left owner)
    (leftSlots : ∀ owner, owner ≠ who → CanonicalSlotsUsed setup leaks left owner)
    (rightOwn : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks right owner)
    (rightSlots : ∀ owner, owner ≠ who → CanonicalSlotsUsed setup leaks right owner) :
    ((serviceApplication setup mode deadline leaks).round scheduler
        (blockPlayers bound turns profile who deviation leftAssignment) left).map
        (blockReadout who low high) =
      ((serviceApplication setup mode deadline leaks).round scheduler
        (blockPlayers bound turns profile who deviation rightAssignment) right).map
        (blockReadout who low high) := by
  let app := serviceApplication setup mode deadline leaks
  have sameTraffic : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right :=
    congrArg Prod.fst same
  have sameMarks : blockMarks who low high left = blockMarks who low high right :=
    congrArg Prod.snd same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have observed := observeEnvironment_eq_of_bindingTraffic who sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) sameTraffic
  have cuts := cut_eq_of_publicView_eq publics
  have leftBindings : ∀ event, left.application.config.cut.Ready event →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq :=
    fun event ready => bindings event (inBlock event ready).1 (inBlock event ready).2
  have rightBindings : ∀ event, right.application.config.cut.Ready event →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq := by
    intro event ready
    rw [← cuts] at ready
    exact leftBindings event ready
  have includeTraffic (id : MessageId Player) :
      (serviceRuntime setup mode deadline).bindingTraffic leaks who (left.includePending app id) =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (right.includePending app id) := by
    apply include_bindingTraffic_of_handled sameTraffic id
    intro message _
    rcases message with ⟨messageId, packet, evidence, token⟩
    cases packet with
    | commitment other candidate =>
        exact handle_commitment_playerView_congr (serviceRuntime setup mode deadline)
          left.application right.application who messageId other candidate views
    | opening other candidate raw =>
        change Option.map _ (handle (serviceRuntime setup mode deadline) left.application
            ⟨messageId, .opening other candidate raw⟩) =
          Option.map _ (handle (serviceRuntime setup mode deadline) right.application
            ⟨messageId, .opening other candidate raw⟩)
        rw [handle_opening_none_of_bindings left.application leftBindings,
          handle_opening_none_of_bindings right.application rightBindings]
    | malformed raw => simp [handle]
  unfold ReactiveApplication.round
  rw [environments, observed, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro command selected
  unfold ReactiveApplication.dispatch
  cases command with
  | activate actor =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, ReactiveApplication.Execution.activation_samples,
        PMF.bind_map, PMF.map_bind, Function.comp_def]
      rw [networks]
      apply bind_congr_on_support _
      intro sample sampled
      let leftActive := left.sampledActivation app actor sample
      let rightActive := right.sampledActivation app actor sample
      have activated : (serviceRuntime setup mode deadline).bindingTraffic leaks who leftActive =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who rightActive :=
        bindingTraffic_activation (serviceRuntime setup mode deadline) leaks left right who actor
          sameTraffic sample
      have activeMarks : blockMarks who low high leftActive = blockMarks who low high rightActive :=
        sameMarks
      have activePublics : leftActive.application.publicView =
          rightActive.application.publicView := publics
      change ((blockPlayers bound turns profile who deviation leftAssignment actor
          (leftActive.recall actor) (leftActive.observe app actor)).map
            (leftActive.respond app actor)).map _ =
        ((blockPlayers bound turns profile who deviation rightAssignment actor
          (rightActive.recall actor) (rightActive.observe app actor)).map
            (rightActive.respond app actor)).map _
      by_cases isWho : actor = who
      · subst actor
        have recalled : leftActive.recall who = rightActive.recall who :=
          congrArg (fun value => value.2.2.2.1) activated
        simp only [blockPlayers, Function.update_self]
        rw [recalled, observe_eq_of_bindingTraffic who activated, PMF.map_comp, PMF.map_comp]
        apply map_congr_on_support _
        intro response _
        exact Prod.ext (bindingTraffic_owner_response (serviceRuntime setup mode deadline) leaks
          leftActive rightActive who activated response)
          (blockMarks_respond who low high who activeMarks activePublics response response rfl)
      · simp only [blockPlayers, Function.update_of_ne isWho]
        obtain ⟨leftResponse, rightResponse, leftPure, rightPure, submitted, traffic⟩ :=
          blockResponse_matched isWho leftAssignment rightAssignment same leftTrace rightTrace
            inBlock bindings leftAssigned rightAssigned (leftOwn actor isWho)
            (leftSlots actor isWho) (rightOwn actor isWho) (rightSlots actor isWho)
            (by rw [environments, observed]; exact selected) sample
            (by rw [networks]; exact sampled)
        rw [leftPure, rightPure, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]
        exact congrArg PMF.pure (Prod.ext traffic (blockMarks_respond who low high actor
          activeMarks activePublics leftResponse rightResponse submitted))
  | «include» id =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      apply congrArg PMF.pure
      have leftKeeps : (left.includePending app id).recall = left.recall := by
        unfold ReactiveApplication.Execution.includePending
        generalize left.network.includePending id = pair
        rcases pair with ⟨_ | _, _⟩ <;> rfl
      have rightKeeps : (right.includePending app id).recall = right.recall := by
        unfold ReactiveApplication.Execution.includePending
        generalize right.network.includePending id = pair
        rcases pair with ⟨_ | _, _⟩ <;> rfl
      refine Prod.ext ?_ ?_
      · change (serviceRuntime setup mode deadline).bindingTraffic leaks who
            { left.includePending app id with environmentRecall := _ } =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who
            { right.includePending app id with environmentRecall := _ }
        rw [environments, observed]
        exact bindingTraffic_with_environmentRecall who (includeTraffic id) _
      · change blockMarks who low high { left.includePending app id with environmentRecall := _ } =
          blockMarks who low high { right.includePending app id with environmentRecall := _ }
        exact (blockMarks_of_recall who low high leftKeeps).trans
          (sameMarks.trans (blockMarks_of_recall who low high rightKeeps).symm)
  | application command =>
      change ((left.environmentStep app (.application command)).bind
          (app.resume (blockPlayers bound turns profile who deviation leftAssignment) none)).map
          _ =
        ((right.environmentStep app (.application command)).bind
          (app.resume (blockPlayers bound turns profile who deviation rightAssignment) none)).map
          _
      rw [show app.resume (blockPlayers bound turns profile who deviation leftAssignment) none =
          PMF.pure from rfl,
        show app.resume (blockPlayers bound turns profile who deviation rightAssignment) none =
          PMF.pure from rfl, PMF.bind_pure, PMF.bind_pure]
      have split (execution : app.Execution) :
          (execution.environmentStep app (.application command)).map
              (blockReadout who low high) =
            ((execution.environmentStep app (.application command)).map
              ((serviceRuntime setup mode deadline).bindingTraffic leaks who)).map
                fun traffic => (traffic, blockMarks who low high execution) := by
        rw [PMF.map_comp]
        apply map_congr_on_support _
        intro next reached
        exact Prod.ext rfl (blockMarks_of_recall who low high
          (app.environmentStep_recall execution next _ reached))
      rw [split left, split right, application_environmentStep_traffic_congr sameTraffic command,
        sameMarks]
  | wait =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      apply congrArg PMF.pure
      refine Prod.ext (bindingTraffic_record (leaks := leaks) who sameTraffic .wait) ?_
      change blockMarks who low high { left with environmentRecall := _ } =
        blockMarks who low high { right with environmentRecall := _ }
      exact sameMarks

/-- Inside an unfinished block, every ready event is a block event. -/
theorem WithinBlock.ready_mem (ordered : (serviceGraph setup mode).BarrierOrdered)
    {low high : Nat} (wall : BlockEnd setup mode high)
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (inside : WithinBlock low high execution) (running : ¬ BlockDone high execution)
    {event : (serviceGraph setup mode).EventId}
    (ready : execution.application.config.cut.Ready event) :
    low ≤ event.val ∧ event.val < high := by
  refine ⟨Nat.le_of_not_gt fun below => ready.1 (inside.within.1 event below), ?_⟩
  rcases ordered.ready_lt_of_within inside.within wall.2 ready with below | done
  · exact below
  · exact (running done).elim

/-- **A decided block run.** Facts along a block run of the block's players,
with `count` rounds still to run: a raw trace, the run inside the block, and
every player but the deviator submitting only at its turns and canonically. -/
structure DecidedBlock (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (who : Player)
    (low high count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  trace : ∃ remaining, Nonempty (((serviceApplication setup mode deadline leaks).protocol
    (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
  inside : WithinBlock low high execution
  own : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks execution owner
  slots : ∀ owner, owner ≠ who → CanonicalSlotsUsed setup leaks execution owner

/-- A round of the block's players keeps the decided block run. -/
theorem DecidedBlock.round (ordered : (serviceGraph setup mode).BarrierOrdered)
    {low high : Nat} (wall : BlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) {who : Player}
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (assignment : Assignment setup mode) {count : Nat}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (run : DecidedBlock horizon scheduler who low high (count + 1) execution)
    (running : ¬ BlockDone high execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).round scheduler
      (blockPlayers bound turns profile who deviation assignment) execution).support) :
    DecidedBlock horizon scheduler who low high count next := by
  obtain ⟨remaining, ⟨trace⟩⟩ := run.trace
  rw [show remaining + (count + 1) = (remaining + count) + 1 by omega] at trace
  obtain ⟨nextTrace⟩ := (serviceApplication setup mode deadline leaks).raw_trace_round
    (serviceInitialLaw setup mode) horizon scheduler _ (remaining + count) execution next trace
    reached
  have canonical (owner : Player) (honest : owner ≠ who) :=
    canonicalSlots_round (players := blockPlayers bound turns profile who deviation assignment)
      (by
        simp only [blockPlayers, Function.update_of_ne honest]
        exact assignedTurnPolicy_submitsCanonically bound turns profile owner assignment)
      (by
        simp only [blockPlayers, Function.update_of_ne honest]
        exact assignedTurnPolicy_submitsAtTurn bound turns profile owner assignment)
      trace (run.own owner honest) (run.slots owner honest) reached
  exact ⟨⟨remaining, ⟨nextTrace⟩⟩,
    round_within (wall.sealed ordered) scheduler _ execution next run.inside running reached,
    fun owner honest => (canonical owner honest).1, fun owner honest => (canonical owner honest).2⟩

/-- **A block of decided bindings.** On a barrier-ordered graph, in a block of
bindings every one of whose events owned by another player than the deviator
is assigned on both sides, the block's players stopped once the block is done
give, from two decided block runs with equal readouts, equal laws of the
readout, whatever the assigned values. -/
theorem decidedBlock_readout_congr (ordered : (serviceGraph setup mode).BarrierOrdered)
    {low high : Nat} (wall : BlockEnd setup mode high) {horizon : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (leftAssignment rightAssignment : Assignment setup mode)
    (leftAssigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∃ action, leftAssignment event = some action)
    (rightAssigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∃ action, rightAssignment event = some action) :
    ∀ count (left right : (serviceApplication setup mode deadline leaks).Execution),
      DecidedBlock horizon scheduler who low high count left →
      DecidedBlock horizon scheduler who low high count right →
      blockReadout who low high left = blockReadout who low high right →
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (blockPlayers bound turns profile who deviation leftAssignment) (BlockDone high) count
          left).map (blockReadout who low high) =
        ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (blockPlayers bound turns profile who deviation rightAssignment) (BlockDone high) count
          right).map (blockReadout who low high) := by
  apply runUntil_map_congr_of_rounds _ scheduler _ _ _ _
    (fun count execution => DecidedBlock horizon scheduler who low high count execution)
    (fun count execution => DecidedBlock horizon scheduler who low high count execution)
  · intro n left right _ _ same
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) (congrArg Prod.fst same)
    have cuts := cut_eq_of_publicView_eq publics
    unfold BlockDone
    rw [cuts]
  · intro n left right leftRun rightRun same running
    obtain ⟨leftRemaining, ⟨leftTrace⟩⟩ := leftRun.trace
    rw [show leftRemaining + (n + 1) = (leftRemaining + n) + 1 by omega] at leftTrace
    obtain ⟨rightRemaining, ⟨rightTrace⟩⟩ := rightRun.trace
    rw [show rightRemaining + (n + 1) = (rightRemaining + n) + 1 by omega] at rightTrace
    exact blockRound_readout_congr scheduler bound turns profile who deviation leftAssignment
      rightAssignment same leftTrace rightTrace
      (fun event ready => leftRun.inside.ready_mem ordered wall running ready) bindings
      leftAssigned rightAssigned leftRun.own leftRun.slots rightRun.own rightRun.slots
  · intro n left leftRun running next reached
    exact leftRun.round ordered wall bound turns profile deviation leftAssignment running reached
  · intro n right rightRun running next reached
    exact rightRun.round ordered wall bound turns profile deviation rightAssignment running
      reached

end Block

end Vegas
