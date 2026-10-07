/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealVirtual
import Vegas.Game.ServiceRevealLaw
import Vegas.Game.AsyncDeviationForeign

/-! # A block of opened disclosures against one deviating player

In a block of disclosures, every player but one deviator follows its first-turn
client with the opening assigned at its disclosures, while the deviator follows
an arbitrary native policy. The deviator may withhold one of its own effective
disclosures (`Vegas.DeviatorWithheld`), which it reads from its own observation
and which no later step undoes. Until it does, every completed disclosure of the
block publishes what the opened block publishes, so the other owners' openings
carry the same values on two executions whose opened blocks publish alike, and
the deviator's traffic keeps the same law. Once it has withheld, nothing more is
compared (`Vegas.runUntil_map_congr_of_rounds_withheld`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

section Simulation

variable {Principal : Type} [DecidableEq Principal] {β : Type*}
  (app : ReactiveApplication Principal)

/-- A stopped run from a state whose readout is `none`, along which `none` is
kept, has readout `none` throughout. -/
theorem runUntil_readout_none (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (ψ : app.Execution → Option β) (holds : Nat → app.Execution → Prop)
    (kept : ∀ n execution, holds (n + 1) execution → ψ execution = none →
      ∀ next ∈ (app.round scheduler players execution).support, ψ next = none)
    (step : ∀ n execution, holds (n + 1) execution → ¬ stop execution →
      ∀ next ∈ (app.round scheduler players execution).support, holds n next) :
    ∀ count execution, holds count execution → ψ execution = none →
      ∀ final ∈ (app.runUntil scheduler players stop count execution).support, ψ final = none := by
  intro count
  induction count with
  | zero =>
      intro execution _ dead final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact dead
  | succ count ih =>
      intro execution valid dead final reached
      by_cases halted : stop execution
      · rw [app.runUntil_of_stop scheduler players stop _ execution halted] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact dead
      · simp only [ReactiveApplication.runUntil, halted, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        exact ih middle (step count execution valid halted middle moved)
          (kept count execution valid dead middle moved) final rest

/-- **Stopped runs from a round congruence, up to an absorbing withdrawal.**
Two profiles whose single rounds have equal laws of an optional readout `ψ`
from executions with equal readouts other than `none`, under per-side
invariants that rounds keep and that determine when to stop while the readout
is not `none`, and along which `none` is kept, have equal laws of `ψ` after any
number of stopped rounds. -/
theorem runUntil_map_congr_of_rounds_withheld (scheduler : app.Scheduler)
    (first second : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (ψ : app.Execution → Option β) (leftHolds rightHolds : Nat → app.Execution → Prop)
    (stops : ∀ n left right, leftHolds n left → rightHolds n right → ψ left = ψ right →
      ψ left ≠ none → (stop left ↔ stop right))
    (rounds : ∀ n left right, leftHolds (n + 1) left → rightHolds (n + 1) right →
      ψ left = ψ right → ψ left ≠ none → ¬ stop left →
      (app.round scheduler first left).map ψ = (app.round scheduler second right).map ψ)
    (leftKept : ∀ n execution, leftHolds (n + 1) execution → ψ execution = none →
      ∀ next ∈ (app.round scheduler first execution).support, ψ next = none)
    (rightKept : ∀ n execution, rightHolds (n + 1) execution → ψ execution = none →
      ∀ next ∈ (app.round scheduler second execution).support, ψ next = none)
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
      by_cases dead : ψ left = none
      · have rightDead : ψ right = none := same ▸ dead
        have leftNone := runUntil_readout_none app scheduler first stop ψ leftHolds leftKept
          leftStep (count + 1) left leftValid dead
        have rightNone := runUntil_readout_none app scheduler second stop ψ rightHolds rightKept
          rightStep (count + 1) right rightValid rightDead
        rw [map_congr_on_support _ (g := fun _ => none) leftNone, pmf_map_fun_const,
          map_congr_on_support _ (g := fun _ => none) rightNone, pmf_map_fun_const]
      by_cases halted : stop left
      · have rightHalted := (stops _ left right leftValid rightValid same dead).mp halted
        rw [app.runUntil_of_stop scheduler first stop _ left halted,
          app.runUntil_of_stop scheduler second stop _ right rightHalted, PMF.pure_map,
          PMF.pure_map]
        exact congrArg PMF.pure same
      · have rightRunning : ¬ stop right := fun rightHalted =>
          halted ((stops _ left right leftValid rightValid same dead).mpr rightHalted)
        simp only [ReactiveApplication.runUntil, halted, rightRunning, ↓reduceIte, PMF.map_bind]
        apply bind_eq_of_map_eq _ _ _ _
          (rounds count left right leftValid rightValid same dead halted)
        intro next nextReached other otherReached equal
        exact ih next other (leftStep count left leftValid halted next nextReached)
          (rightStep count right rightValid rightRunning other otherReached) equal

end Simulation

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The deviator withheld an effective disclosure: one of its disclosures
completed with a decision other than disclosing exactly when its opening is
effective. -/
def DeviatorWithheld (who : Player) (config : (serviceGraph setup mode).Config) : Prop :=
  ∃ event, (serviceGraph setup mode).actor? event = some who ∧ ¬ OpenedAt config event

/-- Whether an owner's disclosure was opened depends only on that owner's
observation: its own completions and its view of the store. -/
theorem openedAt_congr_of_observe {who : Player} {left right : (serviceGraph setup mode).Config}
    (same : (serviceGraph setup mode).playerObserve who left =
      (serviceGraph setup mode).playerObserve who right)
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some who) :
    OpenedAt left event ↔ OpenedAt right event := by
  have stores : (serviceGraph setup mode).playerStore who left.store =
      (serviceGraph setup mode).playerStore who right.store :=
    congrArg EventGraph.PlayerObservation.store same
  have own : (serviceGraph setup mode).ownCompletions who left.history =
      (serviceGraph setup mode).ownCompletions who right.history :=
    congrArg EventGraph.PlayerObservation.ownActions same
  unfold OpenedAt
  cases node : nodeView (serviceGraph setup mode) event with
  | bind => exact Iff.rfl
  | sample => exact Iff.rfl
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerIs : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst ownerIs
      dsimp only
      have resolved (config : (serviceGraph setup mode).Config) :
          EventGraph.EventCode.resolveOutput? binding checks true config.store =
            EventGraph.EventCode.resolveOutput? binding checks true
              ((serviceGraph setup mode).playerStore owner config.store) :=
        (EventGraph.EventCode.resolveOutput?_playerStore (owner := owner) _ _ _ _).symm
      have membership (action : (serviceGraph setup mode).Action event) :
          (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ left.history ↔
            (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ right.history := by
        have leftIff : (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ left.history ↔
            (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
              (serviceGraph setup mode).ownCompletions owner left.history := by
          simp [EventGraph.ownCompletions, owned]
        have rightIff : (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
            right.history ↔ (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
              (serviceGraph setup mode).ownCompletions owner right.history := by
          simp [EventGraph.ownCompletions, owned]
        rw [leftIff, rightIff, own]
      rw [resolved left, resolved right, stores]
      exact forall_congr' fun action => imp_congr (membership action) Iff.rfl

/-- Whether the deviator withheld depends only on its own observation. -/
theorem deviatorWithheld_congr {who : Player} {left right : (serviceGraph setup mode).Config}
    (same : (serviceGraph setup mode).playerObserve who left =
      (serviceGraph setup mode).playerObserve who right) :
    DeviatorWithheld who left ↔ DeviatorWithheld who right := by
  unfold DeviatorWithheld
  exact exists_congr fun event => and_congr_right fun owned =>
    not_congr (openedAt_congr_of_observe same owned)

/-- A withheld disclosure stays withheld along every run. -/
theorem DeviatorWithheld.reaches {who : Player} {before after : (serviceGraph setup mode).Config}
    (reach : ConfigReaches setup before after) (withheld : DeviatorWithheld who before) :
    DeviatorWithheld who after := by
  obtain ⟨event, owned, notOpened⟩ := withheld
  refine ⟨event, owned, fun opened => notOpened ?_⟩
  by_cases done : event ∈ before.cut.completed
  · unfold OpenedAt at opened ⊢
    cases node : nodeView (serviceGraph setup mode) event with
    | bind => trivial
    | sample => trivial
    | resolve owner payload binding checks outputEq codeEq =>
        rw [node] at opened
        dsimp only at opened ⊢
        intro action member
        refine (opened action (reach.history_prefix.subset member)).trans ?_
        have reads : ((serviceGraph setup mode).nodes event).readFields =
            insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
          (EventGraph.EventCode.readFields_cast outputEq
            ((serviceGraph setup mode).nodes event)).symm.trans
            (congrArg EventGraph.EventCode.readFields codeEq)
        have agree := reach.readFields_agree (fun prior pred =>
          before.cut.predecessor_closed done pred)
        rw [reads] at agree
        rw [EventGraph.EventCode.resolveOutput?_congr binding checks true _ _ agree]
  · unfold OpenedAt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind => trivial
    | sample => trivial
    | resolve owner payload binding checks outputEq codeEq =>
        dsimp only
        intro action member
        exact (done ((before.history_exact event).mp (List.mem_map_of_mem member))).elim

/-- **Another owner's response in a block of openings.** At an activation of a
player other than the deviator, on two executions with equal readouts whose ready
events lie in a block of disclosures, each assigned the opening for owners other
than the deviator, and at which every ready disclosure of the block resolves
alike, the player's two responses are deterministic, submit for the same event
and leave equal deviator traffic. -/
theorem revealResponse_matched {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who actor : Player} (honest : actor ≠ who)
    {low high : Nat} (assignment : Assignment setup mode)
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
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (assigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∀ {payload : L.Ty}
          (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload),
          assignment event = some (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            true))
    (resolvesAlike : ∀ event owner payload binding checks outputEq codeEq,
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      left.application.config.cut.Ready event →
      EventGraph.EventCode.resolveOutput? binding checks true left.application.config.store =
        EventGraph.EventCode.resolveOutput? binding checks true right.application.config.store)
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
      assignedTurnPolicy bound turns profile actor assignment (leftActive.recall actor)
          (leftActive.observe (serviceApplication setup mode deadline leaks) actor) =
        PMF.pure leftResponse ∧
      assignedTurnPolicy bound turns profile actor assignment (rightActive.recall actor)
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
      obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
        nodeView_resolve_of_publication (publications event lower upper)
      have ownerIs : owner = actor := Option.some.inj
        ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst ownerIs
      have assignedEq := assigned event owner lower upper owned honest outputEq
      have leftTurn : (leftActive.observe app owner).application.publicView.ownTurn? owner =
          some event := turn
      have rightTurn : (rightActive.observe app owner).application.publicView.ownTurn? owner =
          some event := by
        change right.application.publicView.ownTurn? owner = some event
        rw [← publics]
        exact turn
      rw [assignedTurnPolicy_assigned leftTurn assignedEq,
        assignedTurnPolicy_assigned rightTurn assignedEq]
      have marksAt := congrFun (congrFun sameMarks owner) event
      simp only [blockMarks, honest, ne_eq, not_false_eq_true, lower, upper, and_self,
        ↓reduceIte, Prod.mk.injEq] at marksAt
      obtain ⟨sameTurns, sameRecorded⟩ := marksAt
      have leftActiveReady : leftActive.application.config.cut.Ready event := leftReady
      have rightActiveReady : rightActive.application.config.cut.Ready event := rightReady
      have resolveEq := resolvesAlike event owner payload binding checks outputEq codeEq node
        leftReady
      -- A disclosure whose opening does not succeed is decided silently.
      have silentOf (execution : app.Execution)
          (ready : execution.application.config.cut.Ready event)
          (notSuccess : ∀ value, EventGraph.EventCode.resolveOutput? binding checks true
            execution.application.config.store ≠ some (.success value)) :
          decidedTurnPolicy setup leaks bound owner event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
              (execution.recall owner) (execution.observe app owner) = PMF.pure ⟨none⟩ := by
        by_cases opened : ownerTurns owner event execution = 0 ∧
            (serviceRuntime setup mode deadline).eventRecorded leaks
              (execution.recall owner) event = false ∧
            execution.application.publicView.InclusionFitsDeadline
              (serviceRuntime setup mode deadline) bound event
        · rw [decidedTurnPolicy_open _ execution ready owned opened.1]
          apply decidedOpportunity_silent
          rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_resolution_unvalidated
            leaks owner _ _ event owner payload binding checks outputEq codeEq node
            (fun value candidate resolved _ => (notSuccess value (by
              change EventGraph.EventCode.resolveOutput? binding checks true
                ((serviceGraph setup mode).playerStore owner
                  execution.application.config.store) = _ at resolved
              rwa [EventGraph.EventCode.resolveOutput?_playerStore] at resolved)).elim)]
        · exact decidedTurnPolicy_closed _ execution ready owned opened
      by_cases success : ∃ value, EventGraph.EventCode.resolveOutput? binding checks true
          left.application.config.store = some (.success value)
      swap
      · have notLeft : ∀ value, EventGraph.EventCode.resolveOutput? binding checks true
            leftActive.application.config.store ≠ some (.success value) :=
          fun value equal => success ⟨value, equal⟩
        have notRight : ∀ value, EventGraph.EventCode.resolveOutput? binding checks true
            rightActive.application.config.store ≠ some (.success value) := by
          intro value equal
          change EventGraph.EventCode.resolveOutput? binding checks true
            right.application.config.store = _ at equal
          rw [← resolveEq] at equal
          exact success ⟨value, equal⟩
        exact ⟨⟨none⟩, ⟨none⟩, silentOf leftActive leftActiveReady notLeft,
          silentOf rightActive rightActiveReady notRight, rfl,
          bindingTraffic_respond_other whoActor activated ⟨none⟩ ⟨none⟩ (Or.inl ⟨rfl, rfl⟩)⟩
      obtain ⟨value, resolved⟩ := success
      by_cases opened : ownerTurns owner event left = 0 ∧
          (serviceRuntime setup mode deadline).eventRecorded leaks (left.recall owner) event =
            false ∧
          left.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
            bound event
      · obtain ⟨first, unrecorded, fits⟩ := opened
        have rightFirst : ownerTurns owner event right = 0 := sameTurns ▸ first
        have rightUnrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
            (right.recall owner) event = false := sameRecorded ▸ unrecorded
        have rightFits : right.application.publicView.InclusionFitsDeadline
            (serviceRuntime setup mode deadline) bound event := publics ▸ fits
        have rightSelected : (.activate owner : app.Command) ∈ (scheduler
            right.environmentRecall (right.observeEnvironment app)).support := by
          rw [← environments, ← observeEnvironment_eq_of_bindingTraffic who sameTraffic]
          exact selected
        have rightSampled : sample ∈ (app.observePending owner right.network.pending).support := by
          rw [← networks]
          exact sampled
        obtain ⟨leftHandle, leftMaterial, leftAssociated, leftPolicy, leftPacket⟩ :=
          decidedReveal_response node value leftTrace leftReady resolved selected sample
            sampled first unrecorded fits
        obtain ⟨rightHandle, rightMaterial, rightAssociated, rightPolicy, rightPacket⟩ :=
          decidedReveal_response node value rightTrace rightReady
            (resolveEq ▸ resolved) rightSelected sample rightSampled rightFirst
            rightUnrecorded rightFits
        have handles : leftHandle = rightHandle := by
          have accepted : left.application.accepted = right.application.accepted :=
            congrArg PublicView.accepted publics
          rw [accepted] at leftAssociated
          exact Option.some.inj (leftAssociated.symm.trans rightAssociated)
        subst handles
        refine ⟨⟨some leftMaterial⟩, ⟨some rightMaterial⟩, leftPolicy, rightPolicy, ?_, ?_⟩
        · rw [submittedEvent_some_eq_packet leftMaterial
              (app.submit leftActive.application owner leftMaterial) owner
              (leftActive.network.known owner),
            submittedEvent_some_eq_packet rightMaterial
              (app.submit rightActive.application owner rightMaterial) owner
              (rightActive.network.known owner), leftPacket, rightPacket]
        · exact bindingTraffic_respond_other whoActor activated _ _
            (Or.inr ⟨_, _, rfl, rfl, by rw [leftPacket, rightPacket, publics]⟩)
      · have rightClosed : ¬ (ownerTurns owner event right = 0 ∧
            (serviceRuntime setup mode deadline).eventRecorded leaks (right.recall owner) event =
              false ∧
            right.application.publicView.InclusionFitsDeadline
              (serviceRuntime setup mode deadline) bound event) := by
          rw [← sameTurns, ← sameRecorded, ← publics]
          exact opened
        exact ⟨⟨none⟩, ⟨none⟩,
          decidedTurnPolicy_closed _ leftActive leftActiveReady owned opened,
          decidedTurnPolicy_closed _ rightActive rightActiveReady owned rightClosed,
          rfl, bindingTraffic_respond_other whoActor activated ⟨none⟩ ⟨none⟩
            (Or.inl ⟨rfl, rfl⟩)⟩

/-- A pending opening of a player other than the deviator, for a ready
disclosure owned by its sender, opens the sender's verified handle with the
value it binds. -/
def PendingOpeningsValid (who : Player) (low high : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  ∀ id message, execution.network.lookup id = some message → message.sender ≠ who →
    ∀ (event : (serviceGraph setup mode).EventId), low ≤ event.val → event.val < high →
    ∀ owner payload binding checks outputEq codeEq,
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      execution.application.config.cut.Ready event → message.sender = owner →
      ∀ (candidate : Handle (serviceGraph setup mode)) (raw : Raw L),
        message.payload.call = .opening event candidate raw →
        ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧ candidate.1 = owner ∧
          execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
          binding.get? execution.application.config.store = some (.success value)

/-- **One round of a block of openings.** On two executions with equal readouts
whose ready events lie in a block of disclosures, each assigned the opening for
owners other than the deviator, at which every ready disclosure of the block
resolves alike and every pending opening of another player is valid, one round
of the block's players gives equal laws of the readout. -/
theorem revealRound_readout_congr {horizon leftRemaining rightRemaining : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {low high : Nat} (assignment : Assignment setup mode)
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
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (assigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∀ {payload : L.Ty}
          (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload),
          assignment event = some (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            true))
    (resolvesAlike : ∀ event owner payload binding checks outputEq codeEq,
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      left.application.config.cut.Ready event →
      EventGraph.EventCode.resolveOutput? binding checks true left.application.config.store =
        EventGraph.EventCode.resolveOutput? binding checks true right.application.config.store)
    (leftValid : PendingOpeningsValid who low high left)
    (rightValid : PendingOpeningsValid who low high right) :
    ((serviceApplication setup mode deadline leaks).round scheduler
        (blockPlayers bound turns profile who deviation assignment) left).map
        (blockReadout who low high) =
      ((serviceApplication setup mode deadline leaks).round scheduler
        (blockPlayers bound turns profile who deviation assignment) right).map
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
  have includeTraffic (id : MessageId Player) :
      (serviceRuntime setup mode deadline).bindingTraffic leaks who (left.includePending app id) =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (right.includePending app id) := by
    apply include_bindingTraffic_of_handled sameTraffic id
    intro message found
    by_cases fromWho : message.sender = who
    · exact handle_playerView_congr_of_sender (serviceRuntime setup mode deadline)
        left.application right.application who ⟨message.id, message.payload.call⟩ views fromWho
    rcases message with ⟨messageId, packet, evidence, token⟩
    cases packet with
    | commitment other candidate =>
        exact handle_commitment_playerView_congr (serviceRuntime setup mode deadline)
          left.application right.application who messageId other candidate views
    | malformed raw => simp [handle]
    | opening other candidate raw =>
        change Option.map _ (handle (serviceRuntime setup mode deadline) left.application
            ⟨messageId, .opening other candidate raw⟩) =
          Option.map _ (handle (serviceRuntime setup mode deadline) right.application
            ⟨messageId, .opening other candidate raw⟩)
        by_cases otherReady : left.application.config.cut.Ready other
        · have rightOtherReady : right.application.config.cut.Ready other := by
            rw [← cuts]
            exact otherReady
          obtain ⟨lower, upper⟩ := inBlock other otherReady
          obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
            nodeView_resolve_of_publication (publications other lower upper)
          by_cases fromOwner : messageId.1 = owner
          · have rightFound : right.network.lookup id =
                some ⟨messageId, ⟨.opening other candidate raw, evidence, token⟩⟩ := by
              rw [← networks]
              exact found
            obtain ⟨value, rawEq, handleOwner, leftOpenable, leftStored⟩ :=
              leftValid id _ found fromWho other lower upper owner payload binding checks outputEq
                codeEq node otherReady fromOwner candidate raw rfl
            obtain ⟨rightValue, rightRawEq, _, rightOpenable, rightStored⟩ :=
              rightValid id _ rightFound fromWho other lower upper owner payload binding checks
                outputEq codeEq node rightOtherReady fromOwner candidate raw rfl
            subst rawEq
            have values : rightValue = value := by
              have injected := Raw.mk.inj rightRawEq
              exact (eq_of_heq injected.2).symm
            subst values
            exact handle_opening_playerView_congr node left.application right.application who
              views otherReady rightOtherReady messageId fromOwner candidate handleOwner rightValue
              leftOpenable rightOpenable leftStored rightStored
          · have rejected (state : EventGraphRuntime.State (serviceGraph setup mode)) :
                handle (serviceRuntime setup mode deadline) state
                  ⟨messageId, .opening other candidate raw⟩ = none := by
              cases accepted : handle (serviceRuntime setup mode deadline) state
                  ⟨messageId, .opening other candidate raw⟩ with
              | none => rfl
              | some next =>
                  have actor := handle_sender_actor (serviceRuntime setup mode deadline) state next
                    _ accepted other rfl
                  rw [nodeView_resolve_actor outputEq codeEq] at actor
                  exact (fromOwner (Option.some.inj actor).symm).elim
            rw [rejected, rejected]
        · have rightNot : ¬ right.application.config.cut.Ready other := by
            rw [← cuts]
            exact otherReady
          simp [handle, otherReady, rightNot]
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
      change ((blockPlayers bound turns profile who deviation assignment actor
          (leftActive.recall actor) (leftActive.observe app actor)).map
            (leftActive.respond app actor)).map _ =
        ((blockPlayers bound turns profile who deviation assignment actor
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
          revealResponse_matched isWho assignment same leftTrace rightTrace inBlock publications
            assigned resolvesAlike (by rw [environments, observed]; exact selected) sample
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
          (app.resume (blockPlayers bound turns profile who deviation assignment) none)).map
          _ =
        ((right.environmentStep app (.application command)).bind
          (app.resume (blockPlayers bound turns profile who deviation assignment) none)).map
          _
      rw [show app.resume (blockPlayers bound turns profile who deviation assignment) none =
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

/-- **A run of a block of openings.** Facts along a run of the block's players
from `start`, with `count` rounds still to run: a raw trace, the configuration
reached from the start, the run inside the block, every player but the deviator
submitting only at its turns, activations answered, and every other owner of a
disclosure of the block in its decided phase there, deciding the opening. -/
structure OpenedBlockRun (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (who : Player) (low high count : Nat)
    (start execution : (serviceApplication setup mode deadline leaks).Execution) : Prop where
  trace : ∃ remaining, Nonempty (((serviceApplication setup mode deadline leaks).protocol
    (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
  reach : ConfigReaches setup start.application.config execution.application.config
  inside : WithinBlock low high execution
  untouched : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
    Untouched setup leaks event start
  own : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks execution owner
  answered : ActivationsAnswered setup leaks execution
  phase : ∀ (event : (serviceGraph setup mode).EventId) owner, low ≤ event.val →
    event.val < high → (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
    ∀ {payload : L.Ty}
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload),
      DecidedEventPhase bound start owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) execution

/-- At the start of a block the run of openings holds trivially. -/
theorem OpenedBlockRun.initial {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (bound : (serviceGraph setup mode).EventId → Nat) (who : Player) {low high count : Nat}
    (lowHigh : low ≤ high) (start : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ∃ remaining, Nonempty (((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + count, none, start⟩)))
    (startPrefix : start.application.config.cut.IsPrefix low)
    (startUntouched : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      Untouched setup leaks event start)
    (startOwn : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks start owner)
    (startAnswered : ActivationsAnswered setup leaks start) :
    OpenedBlockRun horizon scheduler bound who low high count start start where
  trace := trace
  reach := Relation.ReflTransGen.refl
  inside := ⟨startPrefix.within lowHigh, fun event above =>
    startUntouched event (Nat.le_trans lowHigh above)⟩
  untouched := startUntouched
  own := startOwn
  answered := startAnswered
  phase event owner lower _ _ honest _ _ :=
    DecidedEventPhase.initial bound _ (startUntouched event lower) (startOwn owner honest)
      (fun completed => by
        have := (startPrefix.2 event).mp completed
        omega)

/-- A round of the block's players keeps the run of openings. -/
theorem OpenedBlockRun.round {low high : Nat} (sealed : BlockSealed setup mode low high)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program) {who : Player}
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (assignment : Assignment setup mode)
    (assigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∀ {payload : L.Ty}
          (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload),
          assignment event = some (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            true))
    {count : Nat} {start execution next : (serviceApplication setup mode deadline leaks).Execution}
    (run : OpenedBlockRun horizon scheduler bound who low high (count + 1) start execution)
    (running : ¬ BlockDone high execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).round scheduler
      (blockPlayers bound turns profile who deviation assignment) execution).support) :
    OpenedBlockRun horizon scheduler bound who low high count start next := by
  obtain ⟨remaining, ⟨trace⟩⟩ := run.trace
  rw [show remaining + (count + 1) = (remaining + count) + 1 by omega] at trace
  obtain ⟨nextTrace⟩ := (serviceApplication setup mode deadline leaks).raw_trace_round
    (serviceInitialLaw setup mode) horizon scheduler _ (remaining + count) execution next trace
    reached
  have policyOf (owner : Player) (honest : owner ≠ who) :
      blockPlayers bound turns profile who deviation assignment owner =
        assignedTurnPolicy bound turns profile owner assignment := by
    simp only [blockPlayers, Function.update_of_ne honest]
  have atTurn (owner : Player) (honest : owner ≠ who) :
      SubmitsAtTurn setup leaks (blockPlayers bound turns profile who deviation assignment owner)
        owner := by
    rw [policyOf owner honest]
    exact assignedTurnPolicy_submitsAtTurn bound turns profile owner assignment
  refine ⟨⟨remaining, ⟨nextTrace⟩⟩,
    run.reach.trans_single (round_configStep setup leaks scheduler _ execution next reached),
    round_within sealed scheduler _ execution next run.inside running reached, run.untouched,
    fun owner honest => round_ownSubmissionsAtTurn setup leaks (atTurn owner honest)
      (run.own owner honest) reached,
    round_activationsAnswered setup leaks run.answered reached, ?_⟩
  intro event owner lower upper owned honest payload outputEq
  have loud : ¬ SilentAction event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) := by
    obtain ⟨_, _, _, _, nodeEq, _, node⟩ :=
      nodeView_resolve_of_publication (by rw [outputEq]; trivial : ((serviceGraph setup
        mode).outputLayout event).IsPublication)
    unfold SilentAction
    rw [node]
    simp
  exact (run.phase event owner lower upper owned honest outputEq).round contract timely owned
    (fun other same => by rw [outputEq] at same; cases same) loud trace (run.own owner honest)
    run.answered (run.untouched event lower)
    (by
      rw [policyOf owner honest]
      exact assignedTurnPolicy_decidesAt bound turns profile owner assignment event _
        (assigned event owner lower upper owned honest outputEq))
    reached

/-- Along a run of openings every completed disclosure of the block whose owner
is not the deviator was opened. -/
theorem OpenedBlockRun.opened {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {who : Player} {low high count : Nat}
    {start execution : (serviceApplication setup mode deadline leaks).Execution}
    (run : OpenedBlockRun horizon scheduler bound who low high count start execution)
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (alive : ¬ DeviatorWithheld who execution.application.config) :
    ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event ∈ execution.application.config.cut.completed →
        OpenedAt execution.application.config event := by
  intro event lower done
  have upper := run.inside.within.2 event done
  obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
    nodeView_resolve_of_publication (publications event lower upper)
  have owned := nodeView_resolve_actor outputEq codeEq
  by_cases honest : owner = who
  · subst honest
    by_contra notOpened
    exact alive ⟨event, owned, notOpened⟩
  · exact (run.phase event owner lower upper owned honest outputEq).opened node done

/-- Along a run of openings every pending opening of another player is valid. -/
theorem OpenedBlockRun.pendingValid {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {who : Player} {low high count : Nat}
    {start execution : (serviceApplication setup mode deadline leaks).Execution}
    (run : OpenedBlockRun horizon scheduler bound who low high count start execution) :
    PendingOpeningsValid who low high execution := by
  intro id message found fromOther event lower upper owner payload binding checks outputEq codeEq
    node ready sender candidate raw call
  obtain ⟨remaining, ⟨trace⟩⟩ := run.trace
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨entry, member, material, transmission, emittedEq, _, _, packet⟩ :=
    facts.provenance.pending message (List.mem_of_find?_eq_some found)
  rw [sender] at member fromOther
  have owned := nodeView_resolve_actor outputEq codeEq
  have submitted :
      (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event := by
    rw [issued_submittedEvent transmission packet, call]
    rfl
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  obtain ⟨packetMessage, emittedP, _, _, realized⟩ :=
    (run.phase event owner lower upper owned fromOther outputEq).submitted before entry after
      split submitted
  rw [emittedEq] at emittedP
  cases Option.some.inj emittedP
  have realizedNow := realized ready.1
  unfold RealizesAt at realizedNow
  rw [node] at realizedNow
  obtain ⟨_, handle, value, callEq, handleOwner, _, fixed, stored, _⟩ := realizedNow
  rw [call] at callEq
  injection callEq with _ handleEq rawEq
  subst handleEq rawEq
  exact ⟨value, rfl, handleOwner, fixed, stored⟩

/-- Two laws with equal images under `f` have equal images under every `h`
that `f` determines. -/
theorem PMF.map_eq_map_of_factor {α β γ : Type*} (first second : PMF α) (f : α → β)
    (h : α → γ) (factor : ∀ x y, f x = f y → h x = h y)
    (same : first.map f = second.map f) : first.map h = second.map h := by
  classical
  let g : β → γ := fun value => if present : ∃ x, f x = value then h present.choose
    else h first.support_nonempty.choose
  have factored : h = g ∘ f := by
    funext x
    have present : ∃ y, f y = f x := ⟨x, rfl⟩
    simp only [Function.comp_apply, g, dite_eq_left present]
    exact factor x present.choose present.choose_spec.symm
  rw [factored, ← PMF.map_comp, ← PMF.map_comp, same]

/-- **Opened disclosures resolve alike.** Two configurations that completed a
disclosure, each with the decision to disclose exactly when its opening is
effective, and with the same output, resolve its opening alike. -/
theorem resolve_true_eq_of_outputs {start left right : (serviceGraph setup mode).Config}
    {startRight : (serviceGraph setup mode).Config}
    (leftReach : ConfigReaches setup start left) (rightReach : ConfigReaches setup startRight right)
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (leftFresh : event ∉ start.cut.completed) (rightFresh : event ∉ startRight.cut.completed)
    (leftDone : event ∈ left.cut.completed) (rightDone : event ∈ right.cut.completed)
    (leftOpened : OpenedAt left event) (rightOpened : OpenedAt right event)
    (outputs : left.outputs event = right.outputs event) :
    EventGraph.EventCode.resolveOutput? binding checks true left.store =
      EventGraph.EventCode.resolveOutput? binding checks true right.store := by
  have reads : ((serviceGraph setup mode).nodes event).readFields =
      insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
    (EventGraph.EventCode.readFields_cast outputEq
      ((serviceGraph setup mode).nodes event)).symm.trans
      (congrArg EventGraph.EventCode.readFields codeEq)
  have available (config : (serviceGraph setup mode).Config)
      (done : event ∈ config.cut.completed) :
      ∀ field ∈ insert binding.field (EventGraph.GuardCheck.listReadFields checks),
        (config.store field).isSome = true := by
    intro field member
    rw [← reads] at member
    have read := (serviceGraph setup mode).reads_available event field member
    cases field with
    | inl input => simp [EventGraph.Config.store]
    | inr producer =>
        rw [EventGraph.Config.store_output, config.output_available]
        exact config.cut.predecessor_closed done read
  unfold OpenedAt at leftOpened rightOpened
  rw [node] at leftOpened rightOpened
  dsimp only at leftOpened rightOpened
  obtain ⟨⟨leftEvent, leftAction⟩, leftMember, leftEventEq⟩ :=
    List.mem_map.mp ((left.history_exact event).mpr leftDone)
  have leftSame : event = leftEvent := leftEventEq.symm
  subst leftSame
  obtain ⟨⟨rightEvent, rightAction⟩, rightMember, rightEventEq⟩ :=
    List.mem_map.mp ((right.history_exact event).mpr rightDone)
  have rightSame : event = rightEvent := rightEventEq.symm
  subst rightSame
  have leftOutput := leftReach.resolve_output leftMember leftFresh (outputEq := outputEq)
    (codeEq := codeEq)
  have rightOutput := rightReach.resolve_output rightMember rightFresh (outputEq := outputEq)
    (codeEq := codeEq)
  have leftIff := leftOpened leftAction leftMember
  have rightIff := rightOpened rightAction rightMember
  obtain ⟨leftResult, leftResolved⟩ := Option.isSome_iff_exists.mp
    (EventGraph.EventCode.resolveOutput?_isSome binding checks true left.store
      (available left leftDone))
  obtain ⟨rightResult, rightResolved⟩ := Option.isSome_iff_exists.mp
    (EventGraph.EventCode.resolveOutput?_isSome binding checks true right.store
      (available right rightDone))
  have leftFalse := EventGraph.EventCode.resolveOutput?_false_eq_failure binding checks left.store
    (available left leftDone)
  have rightFalse := EventGraph.EventCode.resolveOutput?_false_eq_failure binding checks
    right.store (available right rightDone)
  -- Each output is the opening's result when disclosing and failure otherwise.
  have outputOf (config : (serviceGraph setup mode).Config)
      (action : (serviceGraph setup mode).Action event)
      (result : PublicationResult (L.Val payload))
      (resolved : EventGraph.EventCode.resolveOutput? binding checks true config.store =
        some result)
      (failed : EventGraph.EventCode.resolveOutput? binding checks false config.store =
        some .failure)
      (output : config.outputs event = (EventGraph.EventCode.resolveOutput? binding checks
        (cast (congrArg EventGraph.EventField.Action outputEq) action) config.store).map
          (cast (congrArg EventGraph.EventField.Value outputEq.symm))) :
      config.outputs event = some (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (if (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) then result
          else .failure)) := by
    rw [output]
    cases (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) with
    | true => rw [resolved]; rfl
    | false => rw [failed]; rfl
  have leftOut := outputOf left leftAction leftResult leftResolved leftFalse leftOutput
  have rightOut := outputOf right rightAction rightResult rightResolved rightFalse rightOutput
  rw [leftOut, rightOut] at outputs
  have castInjective := (cast_inj (congrArg EventGraph.EventField.Value outputEq.symm)).mp
    (Option.some.inj outputs)
  rw [leftResolved, rightResolved]
  congr 1
  cases leftResult with
  | success leftValue =>
      have leftTrue := leftIff.mpr ⟨leftValue, leftResolved⟩
      rw [leftTrue] at castInjective
      simp only [↓reduceIte] at castInjective
      cases rightDisclose : (cast (congrArg EventGraph.EventField.Action outputEq) rightAction :
          Bool) with
      | true =>
          rw [rightDisclose] at castInjective
          simpa using castInjective
      | false =>
          rw [rightDisclose] at castInjective
          cases castInjective
  | failure =>
      have leftNot : (cast (congrArg EventGraph.EventField.Action outputEq) leftAction : Bool) =
          false := by
        cases decide : (cast (congrArg EventGraph.EventField.Action outputEq) leftAction : Bool)
        · rfl
        · obtain ⟨value, success⟩ := leftIff.mp decide
          rw [leftResolved] at success
          cases success
      cases rightResult with
      | failure => rfl
      | success rightValue =>
          have rightTrue := rightIff.mpr ⟨rightValue, rightResolved⟩
          rw [leftNot, rightTrue] at castInjective
          cases castInjective

open Classical in
/-- The readout of a block of openings while the deviator has not withheld an
effective disclosure: the deviator's traffic and every other owner's turn counts
and records at the block's events. -/
def openedReadout (who : Player) (low high : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :=
  if DeviatorWithheld who execution.application.config then none
  else some (blockReadout who low high execution)

/-- The readout while the deviator has not withheld is read from the readout. -/
theorem openedReadout_congr {who : Player} {low high : Nat}
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : blockReadout who low high left = blockReadout who low high right) :
    openedReadout who low high left = openedReadout who low high right := by
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) (congrArg Prod.fst same)
  have withheld := deviatorWithheld_congr (who := who)
    (left.application.playerView_observation_eq right.application who views)
  unfold openedReadout
  by_cases leftWithheld : DeviatorWithheld who left.application.config
  · rw [ite_eq_left leftWithheld, ite_eq_left (withheld.mp leftWithheld)]
  · rw [ite_eq_right leftWithheld,
      ite_eq_right (fun right => leftWithheld (withheld.mpr right)), same]

/-- **Two opened runs resolve alike.** Along two runs of openings that have not
withheld, from starts whose opened blocks publish alike, every ready disclosure
of the block resolves alike. -/
theorem OpenedBlockRun.resolvesAlike {low high : Nat} {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {who : Player} {leftCount rightCount : Nat}
    {leftStart rightStart left right : (serviceApplication setup mode deadline leaks).Execution}
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (leftStartPrefix : leftStart.application.config.cut.IsPrefix low)
    (rightStartPrefix : rightStart.application.config.cut.IsPrefix low)
    {leftVirtual rightVirtual : (serviceGraph setup mode).Config}
    (leftVirtualReach : ConfigReaches setup leftStart.application.config leftVirtual)
    (rightVirtualReach : ConfigReaches setup rightStart.application.config rightVirtual)
    (leftVirtualPrefix : leftVirtual.cut.IsPrefix high)
    (rightVirtualPrefix : rightVirtual.cut.IsPrefix high)
    (leftVirtualOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → OpenedAt leftVirtual event)
    (rightVirtualOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → OpenedAt rightVirtual event)
    (virtualAgree : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → leftVirtual.outputs event = rightVirtual.outputs event)
    (leftRun : OpenedBlockRun horizon scheduler bound who low high leftCount leftStart left)
    (rightRun : OpenedBlockRun horizon scheduler bound who low high rightCount rightStart right)
    (leftAlive : ¬ DeviatorWithheld who left.application.config)
    (rightAlive : ¬ DeviatorWithheld who right.application.config)
    (cuts : left.application.config.cut = right.application.config.cut)
    (inBlock : ∀ event, left.application.config.cut.Ready event →
      low ≤ event.val ∧ event.val < high) :
    ∀ event owner payload binding checks outputEq codeEq,
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      left.application.config.cut.Ready event →
      EventGraph.EventCode.resolveOutput? binding checks true left.application.config.store =
        EventGraph.EventCode.resolveOutput? binding checks true
          right.application.config.store := by
  intro event owner payload binding checks outputEq codeEq node ready
  obtain ⟨lower, upper⟩ := inBlock event ready
  have rightReady : right.application.config.cut.Ready event := by
    rw [← cuts]
    exact ready
  have reads : ((serviceGraph setup mode).nodes event).readFields =
      insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
    (EventGraph.EventCode.readFields_cast outputEq
      ((serviceGraph setup mode).nodes event)).symm.trans
      (congrArg EventGraph.EventCode.readFields codeEq)
  -- Each side resolves as its opened block.
  have toVirtual {start current : (serviceApplication setup mode deadline leaks).Execution}
      {count : Nat} {virtual : (serviceGraph setup mode).Config}
      (run : OpenedBlockRun horizon scheduler bound who low high count start current)
      (startPrefix : start.application.config.cut.IsPrefix low)
      (virtualReach : ConfigReaches setup start.application.config virtual)
      (virtualPrefix : virtual.cut.IsPrefix high)
      (virtualOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
        event.val < high → OpenedAt virtual event)
      (alive : ¬ DeviatorWithheld who current.application.config)
      (currentReady : current.application.config.cut.Ready event) :
      EventGraph.EventCode.resolveOutput? binding checks true current.application.config.store =
        EventGraph.EventCode.resolveOutput? binding checks true virtual.store := by
    apply EventGraph.EventCode.resolveOutput?_congr
    intro field member
    rw [← reads] at member
    have read := (serviceGraph setup mode).reads_available event field member
    cases field with
    | inl input =>
        rw [EventGraph.Config.store_input, EventGraph.Config.store_input, run.reach.inputs,
          virtualReach.inputs]
    | inr producer =>
        rw [EventGraph.Config.store_output, EventGraph.Config.store_output]
        exact outputs_eq_of_opened run.reach virtualReach startPrefix
          (fun other done => run.inside.within.2 other done) virtualPrefix publications
          (run.opened publications alive) virtualOpened producer (currentReady.2 read)
  rw [toVirtual leftRun leftStartPrefix leftVirtualReach leftVirtualPrefix leftVirtualOpened
      leftAlive ready,
    toVirtual rightRun rightStartPrefix rightVirtualReach rightVirtualPrefix rightVirtualOpened
      rightAlive rightReady]
  have fresh (start : (serviceApplication setup mode deadline leaks).Execution)
      (startPrefix : start.application.config.cut.IsPrefix low) :
      event ∉ start.application.config.cut.completed := fun done => by
    have := (startPrefix.2 event).mp done
    omega
  exact resolve_true_eq_of_outputs leftVirtualReach rightVirtualReach node
    (fresh leftStart leftStartPrefix) (fresh rightStart rightStartPrefix)
    ((leftVirtualPrefix.2 event).mpr upper) ((rightVirtualPrefix.2 event).mpr upper)
    (leftVirtualOpened event lower upper) (rightVirtualOpened event lower upper)
    (virtualAgree event lower upper)

/-- **A block of openings against one deviator.** In a sealed block of
disclosures, every one of them owned by another player than the deviator
assigned the opening, the block's players stopped once the block is done give,
from two runs of openings whose starts' opened blocks publish alike and whose
readouts are equal, equal laws of the readout while the deviator has not
withheld. -/
theorem openedBlock_readout_congr {low high : Nat} (sealed : BlockSealed setup mode low high)
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (assignment : Assignment setup mode)
    (assigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∀ {payload : L.Ty}
          (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload),
          assignment event = some (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            true))
    (leftStart rightStart : (serviceApplication setup mode deadline leaks).Execution)
    (leftStartPrefix : leftStart.application.config.cut.IsPrefix low)
    (rightStartPrefix : rightStart.application.config.cut.IsPrefix low)
    {leftVirtual rightVirtual : (serviceGraph setup mode).Config}
    (leftVirtualReach : ConfigReaches setup leftStart.application.config leftVirtual)
    (rightVirtualReach : ConfigReaches setup rightStart.application.config rightVirtual)
    (leftVirtualPrefix : leftVirtual.cut.IsPrefix high)
    (rightVirtualPrefix : rightVirtual.cut.IsPrefix high)
    (leftVirtualOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → OpenedAt leftVirtual event)
    (rightVirtualOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → OpenedAt rightVirtual event)
    (virtualAgree : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → leftVirtual.outputs event = rightVirtual.outputs event) :
    ∀ count (left right : (serviceApplication setup mode deadline leaks).Execution),
      OpenedBlockRun horizon scheduler bound who low high count leftStart left →
      OpenedBlockRun horizon scheduler bound who low high count rightStart right →
      openedReadout who low high left = openedReadout who low high right →
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (blockPlayers bound turns profile who deviation assignment) (BlockDone high) count
          left).map (openedReadout who low high) =
        ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (blockPlayers bound turns profile who deviation assignment) (BlockDone high) count
          right).map (openedReadout who low high) := by
  have aliveOf {execution : (serviceApplication setup mode deadline leaks).Execution}
      (live : openedReadout who low high execution ≠ none) :
      ¬ DeviatorWithheld who execution.application.config := by
    intro withheld
    apply live
    unfold openedReadout
    rw [ite_eq_left withheld]
  have readoutOf {left right : (serviceApplication setup mode deadline leaks).Execution}
      (same : openedReadout who low high left = openedReadout who low high right)
      (live : openedReadout who low high left ≠ none) :
      blockReadout who low high left = blockReadout who low high right := by
    have leftAlive := aliveOf live
    have rightAlive := aliveOf (same ▸ live)
    unfold openedReadout at same
    rw [ite_eq_right leftAlive, ite_eq_right rightAlive] at same
    exact Option.some.inj same
  apply runUntil_map_congr_of_rounds_withheld _ scheduler _ _ _ _
    (fun count execution => OpenedBlockRun horizon scheduler bound who low high count leftStart
      execution)
    (fun count execution => OpenedBlockRun horizon scheduler bound who low high count rightStart
      execution)
  · intro n left right _ _ same live
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) (congrArg Prod.fst (readoutOf same live))
    unfold BlockDone
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftRun rightRun same live running
    have readouts := readoutOf same live
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) (congrArg Prod.fst readouts)
    have inBlock : ∀ event, left.application.config.cut.Ready event →
        low ≤ event.val ∧ event.val < high := fun event ready =>
      leftRun.inside.ready_mem sealed running ready
    obtain ⟨leftRemaining, ⟨leftTrace⟩⟩ := leftRun.trace
    rw [show leftRemaining + (n + 1) = (leftRemaining + n) + 1 by omega] at leftTrace
    obtain ⟨rightRemaining, ⟨rightTrace⟩⟩ := rightRun.trace
    rw [show rightRemaining + (n + 1) = (rightRemaining + n) + 1 by omega] at rightTrace
    have round := revealRound_readout_congr scheduler bound turns profile who deviation
      assignment readouts leftTrace rightTrace inBlock publications assigned
      (leftRun.resolvesAlike publications leftStartPrefix rightStartPrefix leftVirtualReach
        rightVirtualReach leftVirtualPrefix rightVirtualPrefix leftVirtualOpened
        rightVirtualOpened virtualAgree rightRun (aliveOf live) (aliveOf (same ▸ live))
        (cut_eq_of_publicView_eq publics) inBlock)
      leftRun.pendingValid rightRun.pendingValid
    exact PMF.map_eq_map_of_factor _ _ _ _ (fun _ _ equal => openedReadout_congr equal) round
  · intro n execution run dead next reached
    unfold openedReadout at dead ⊢
    have withheld : DeviatorWithheld who execution.application.config := by
      by_contra alive
      rw [ite_eq_right alive] at dead
      cases dead
    rw [ite_eq_left (withheld.reaches (Relation.ReflTransGen.single
      (round_configStep setup leaks scheduler _ execution next reached)))]
  · intro n execution run dead next reached
    unfold openedReadout at dead ⊢
    have withheld : DeviatorWithheld who execution.application.config := by
      by_contra alive
      rw [ite_eq_right alive] at dead
      cases dead
    rw [ite_eq_left (withheld.reaches (Relation.ReflTransGen.single
      (round_configStep setup leaks scheduler _ execution next reached)))]
  · intro n left leftRun running next reached
    exact leftRun.round sealed contract timely turns profile deviation assignment assigned running
      reached
  · intro n right rightRun running next reached
    exact rightRun.round sealed contract timely turns profile deviation assignment assigned
      running reached

end Vegas
