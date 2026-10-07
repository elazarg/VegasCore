/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceBlockView
import Vegas.Game.SourceCommitBlock

/-! # Drawing a block's commitments in advance

In a block of binding events, the players satisfying a predicate `drawn`
follow their first-turn clients. Each such owner's commitment in the block
follows its source kernel at its view, and its view there is its view at the
block's start together with its own earlier commitments in the block: the other
players' commitments are hidden from it, and on a reveal-relaxed graph its own
earlier bindings have completed exactly when one of its later bindings is
ready.

So the block's commitments of these players can be drawn before the block
runs, one after another in source order from their source kernels
(`Vegas.assignChain`), and the clients then run as the mixture, over those
draws, of clients deciding the drawn actions
(`Vegas.drawnPlayers_runUntil_predraw`), whatever the other players do. With
one deviator outside the predicate this is
`Vegas.blockPlayers_runUntil_predraw`; with every player drawn it is the honest
block.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The output field of an embedded commitment is its binding. -/
theorem commit_headLayout {Γ : SourceCtx Player L} {names : Finset VarId} {name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names)}
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next)) :
    outputLayout setup.program (embedding.event ⟨0, by simp [eventCount]⟩) =
      .binding owner payload := by
  simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩

variable (setup mode) in
/-- **The block's draws.** The commitments of every owner satisfying `drawn`
among the leading commitments, drawn one after another in source order from
their source kernels, each at the source configuration reached by the earlier
draws; the other owners' commitments are read as failed bindings, which no drawn
owner sees. -/
def assignChain (drawn : Player → Prop) [DecidablePred drawn] : (count : Nat) →
    {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    BehavioralProfile program → (prefixed : CommitPrefix program count) →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
    Config Player L Γ → Assignment setup mode → PMF (Assignment setup mode)
  | 0, _, _, _, _, _, _, _, assignment => PMF.pure assignment
  | count + 1, _, _, .commit name owner _ guard next, profile, prefixed, embedding, config,
      assignment =>
      if drawn owner then
        (commitKernel profile (config.view owner)).bind fun choice =>
          assignChain drawn count next (afterCommit profile) prefixed
            (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
            (commitSuccessor name guard config choice)
            (Function.update assignment (embedding.event ⟨0, by simp [eventCount]⟩)
              (some (cast (congrArg EventGraph.EventField.Action
                (commit_headLayout embedding).symm) choice)))
      else
        assignChain drawn count next (afterCommit profile) prefixed
          (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
          (commitSuccessor name guard config .failure) assignment
  | _ + 1, _, _, .ret _, _, prefixed, _, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, _, prefixed, _, _, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, _, prefixed, _, _, _ => prefixed.elim

/-- The players of a block: every player satisfying `drawn` runs its client
deciding the assigned actions, every other player its policy in `others`. -/
def drawnPlayers (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (drawn : Player → Prop) [DecidablePred drawn]
    (others : Player → (serviceApplication setup mode deadline leaks).Policy)
    (assignment : Assignment setup mode) :
    Player → (serviceApplication setup mode deadline leaks).Policy :=
  fun player => if drawn player then assignedTurnPolicy bound turns profile player assignment
    else others player

/-- With one deviator, the block's players are the players drawn but the
deviator. -/
theorem blockPlayers_eq_drawnPlayers (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (assignment : Assignment setup mode) :
    blockPlayers bound turns profile who deviation assignment =
      drawnPlayers bound turns profile (· ≠ who) (fun _ => deviation) assignment := by
  funext player
  by_cases isWho : player = who
  · subst player
    simp only [blockPlayers, drawnPlayers, Function.update_self, ne_eq, not_true_eq_false,
      ↓reduceIte]
  · simp only [blockPlayers, drawnPlayers, Function.update_of_ne isWho, ne_eq, isWho,
      not_false_eq_true, ↓reduceIte]

/-- Assigning an event of one drawn owner changes only that owner's client. -/
theorem drawnPlayers_update (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (drawn : Player → Prop) [DecidablePred drawn]
    (others : Player → (serviceApplication setup mode deadline leaks).Policy)
    (assignment : Assignment setup mode) {event : (serviceGraph setup mode).EventId}
    {owner : Player} (owned : (serviceGraph setup mode).actor? event = some owner)
    (isDrawn : drawn owner) (value : Option ((serviceGraph setup mode).Action event)) :
    drawnPlayers bound turns profile drawn others (Function.update assignment event value) =
      Function.update (drawnPlayers bound turns profile drawn others assignment) owner
        (assignedTurnPolicy bound turns profile owner
          (Function.update assignment event value)) := by
  funext player
  by_cases isOwner : player = owner
  · subst player
    simp only [drawnPlayers, Function.update_self, isDrawn, ↓reduceIte]
  · rw [Function.update_of_ne isOwner]
    by_cases playerDrawn : drawn player
    · simp only [drawnPlayers, playerDrawn, ↓reduceIte]
      funext past view
      apply assignedTurnPolicy_update_of_not_turn
      intro turn
      have actor := (PublicView.ownTurn?_spec _ player event turn).2
      exact isOwner (Option.some.inj (actor.symm.trans owned))
    · simp only [drawnPlayers, playerDrawn, ↓reduceIte]

/-- A checkpoint is kept by completing a commitment on a bare configuration. -/
theorem SourceCheckpoint.commit_config
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup mode).layout Γ} {rank : Nat}
    {native : (serviceGraph setup mode).Config}
    (checkpoint : SourceCheckpoint setup source refs rank native)
    {owner : Player} {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ owner name payload)
    (event : (serviceGraph setup mode).EventId) (eventRank : event.val = rank)
    (ready : native.cut.Ready event)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (choice : PublicationResult (L.Val payload))
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice)) :
    SourceCheckpoint setup (commitSuccessor name guard source choice)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)) :=
  SourceCheckpoint.commit (native := { EventGraphRuntime.State.initial
    (graph := serviceGraph setup mode) native.inputs with config := native }) checkpoint name
    guard event eventRank ready outputEq before choice decoded

/-- The facts kept along a block run while some of its commitments are drawn:
the run reaches its configuration from the block's start, stays inside the
block, every drawn commitment's owner is in its decided binding phase, every
drawn player submits only at its turns, and every activation was answered. -/
structure PredrawRun (bound : (serviceGraph setup mode).EventId → Nat)
    (drawn : Player → Prop) (low high : Nat)
    (start : (serviceApplication setup mode deadline leaks).Execution)
    (assignment : Assignment setup mode)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop where
  reach : ConfigReaches setup start.application.config execution.application.config
  inside : WithinBlock low high execution
  phase : ∀ event owner action, assignment event = some action →
    (serviceGraph setup mode).actor? event = some owner → drawn owner →
      DecidedEventPhase bound start owner event action execution
  own : ∀ owner, drawn owner → OwnSubmissionsAtTurn setup leaks execution owner
  answered : ActivationsAnswered setup leaks execution

/-- **Drawing a block's commitments in advance.** From the start of a block of
bindings, on a reveal-relaxed graph under the asynchronous contract with
`delay + bound < deadline`, the block's players with some commitments already
drawn run, until the block is done, as the mixture over the remaining draws of
`Vegas.assignChain` of the block's players with all of them drawn. The policies
of the players not drawn are arbitrary. The induction follows the leading
commitments of a residual program at the block's current rank `offset`, together
with a configuration `virtual` that completes the block's events below `offset`
in source order with the drawn actions. -/
theorem drawnPlayers_runUntil_predraw (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wall : BlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (drawn : Player → Prop)
    [DecidablePred drawn] (others : Player → (serviceApplication setup mode deadline leaks).Policy)
    (start : (serviceApplication setup mode deadline leaks).Execution)
    (startPrefix : start.application.config.cut.IsPrefix low)
    (startUntouched : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      Untouched setup leaks event start)
    (startOwn : ∀ owner, drawn owner → OwnSubmissionsAtTurn setup leaks start owner)
    (startAnswered : ActivationsAnswered setup leaks start)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
      (source : Config Player L Γ),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations
        source.registry embedding refsBefore offset →
      ∀ virtual : (serviceGraph setup mode).Config,
      SourceCheckpoint setup source refs offset virtual →
      ConfigReaches setup start.application.config virtual →
      low ≤ offset → offset + count = high →
      ∀ assignment : Assignment setup mode,
      (∀ event action, assignment event = some action → low ≤ event.val ∧ event.val < offset) →
      (∀ event owner, low ≤ event.val → event.val < offset →
        (serviceGraph setup mode).actor? event = some owner → drawn owner →
          ∃ action, assignment event = some action ∧
            (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ virtual.history) →
      ∀ (rounds remaining : Nat),
      ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + rounds, none, start⟩) →
      (serviceApplication setup mode deadline leaks).runUntil scheduler
          (drawnPlayers bound turns wholeProfile drawn others assignment) (BlockDone high)
          rounds start =
        (assignChain setup mode drawn count program profile prefixed embedding source
          assignment).bind fun picked =>
          (serviceApplication setup mode deadline leaks).runUntil scheduler
            (drawnPlayers bound turns wholeProfile drawn others picked) (BlockDone high)
            rounds start := by
  let app := serviceApplication setup mode deadline leaks
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed refs embedding refsBefore offset source _ virtual
        _ _ _ _ assignment _ _ rounds remaining _
      simp only [assignChain, PMF.pure_bind]
  | succ count ih =>
      intro Γ names program profile prefixed refs embedding refsBefore offset source aligned
        virtual checkpoint reachVirtual lowOffset offsetEnd assignment assignedRange assignedOld
        rounds remaining trace
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          let index : Fin (eventCount (.commit name owner fresh guard next)) :=
            ⟨0, by simp [eventCount]⟩
          let event : (serviceGraph setup mode).EventId := embedding.event index
          have eventRank : event.val = offset := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload :=
            commit_headLayout embedding
          have codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout)
              outputEq) ((serviceGraph setup mode).nodes event) = .bind owner payload := by
            change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) = _
            simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
          have owned : (serviceGraph setup mode).actor? event = some owner :=
            (serviceGraph setup mode).actor?_of_outputLayout_binding outputEq
          have decodedAction (choice : PublicationResult (L.Val payload)) :
              decodeEventAction setup.program event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
                  some (.commit owner name payload choice) := by
            have lookup := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
            simpa [event, index, outputEq, decodeEventAction] using lookup
          have inBlock : offset < high := by omega
          have ready : virtual.cut.Ready event := by
            have active : offset < (serviceGraph setup mode).order.eventCount := by
              rw [← eventRank]
              exact event.isLt
            have prefixReady := checkpoint.ordered.ready active
            rwa [show (⟨offset, active⟩ : (serviceGraph setup mode).EventId) = event from
              Fin.ext eventRank.symm] at prefixReady
          -- The successor configuration, checkpoint and alignment after one commitment.
          have successor (choice : PublicationResult (L.Val payload)) :
              let nextVirtual := virtual.complete event ready
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
                (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)
              SourceCheckpoint setup (commitSuccessor name guard source choice)
                (refs.cons (name := name) ⟨.inr event, outputEq⟩) (offset + 1) nextVirtual ∧
              ConfigReaches setup start.application.config nextVirtual := by
            intro nextVirtual
            refine ⟨checkpoint.commit_config name guard event eventRank ready outputEq
              (fun ref => refsBefore ref index) choice (decodedAction choice),
              reachVirtual.trans_single (Or.inr ⟨event, ready,
                cast (congrArg EventGraph.EventField.Action outputEq.symm) choice, ?_⟩)⟩
            rw [commit_step virtual event ready outputEq codeEq choice]
            exact PMF.mem_support_pure_iff _ _ |>.mpr rfl
          have tailAligned (choice : PublicationResult (L.Val payload)) :=
            aligned.commitTail setup.program wholeProfile fresh guard next profile refs
              source.revelations source.registry embedding refsBefore offset
          by_cases own : drawn owner
          · let law := (commitKernel profile (source.view owner)).map fun choice =>
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :
                (serviceGraph setup mode).Action event)
            have unassigned : assignment event = none := by
              cases assigned : assignment event with
              | none => rfl
              | some action =>
                  have range := assignedRange event action assigned
                  omega
            have selfPolicy : drawnPlayers bound turns wholeProfile drawn others assignment owner =
                assignedTurnPolicy bound turns wholeProfile owner assignment := by
              simp only [drawnPlayers, own, ↓reduceIte]
            have shape : drawnPlayers bound turns wholeProfile drawn others assignment =
                Function.update (drawnPlayers bound turns wholeProfile drawn others assignment)
                  owner (assignedTurnPolicy bound turns wholeProfile owner assignment) := by
              rw [← selfPolicy, Function.update_eq_self]
            have lowHigh : low ≤ high := by omega
            have eventLow : low ≤ event.val := by omega
            -- the run facts
            have holds : PredrawRun bound drawn low high start assignment start :=
              { reach := Relation.ReflTransGen.refl
                inside := ⟨startPrefix.within lowHigh,
                  fun other above => startUntouched other (Nat.le_trans lowHigh above)⟩
                phase := fun other otherOwner action assigned _ honest =>
                  DecidedEventPhase.initial bound action
                    (startUntouched other (assignedRange other action assigned).1)
                    (startOwn otherOwner honest)
                    (fun done => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
                      ((startPrefix.2 other).mp done) (assignedRange other action assigned).1))
                own := startOwn
                answered := startAnswered }
            have preserved : ∀ (rest : Nat) (execution : app.Execution),
                (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
                  (some ⟨rest + 1, none, execution⟩) →
                PredrawRun bound drawn low high start assignment execution →
                ¬ BlockDone high execution →
                ∀ next ∈ (app.round scheduler (Function.update
                  (drawnPlayers bound turns wholeProfile drawn others assignment) owner
                  (assignedTurnPolicy bound turns wholeProfile owner assignment))
                  execution).support,
                  PredrawRun bound drawn low high start assignment next := by
              intro rest execution executionTrace run running next reached
              rw [← shape] at reached
              refine
                { reach := run.reach.trans_single
                    (round_configStep setup leaks scheduler _ execution next reached)
                  inside := round_within (BlockEnd.sealed_relaxed relaxed wall
                    (plain_of_bindings bindings)) scheduler _ execution next run.inside
                    running
                    reached
                  phase := ?_
                  own := fun other honest => round_ownSubmissionsAtTurn setup leaks
                    (by
                      simp only [drawnPlayers, honest, ↓reduceIte]
                      exact assignedTurnPolicy_submitsAtTurn bound turns wholeProfile other
                        assignment)
                    (run.own other honest) reached
                  answered := round_activationsAnswered setup leaks run.answered reached }
              intro other otherOwner action assigned otherOwned honest
              obtain ⟨lower, upper⟩ := assignedRange other action assigned
              obtain ⟨nodeOwner, nodePayload, nodeEq, nodeCode, _⟩ :=
                bindings other lower (by omega)
              have ownerIs : nodeOwner = otherOwner := Option.some.inj
                ((nodeView_bind_actor nodeEq nodeCode).symm.trans otherOwned)
              subst ownerIs
              have facts := binding_decision_facts nodeEq action
              exact (run.phase other nodeOwner action assigned otherOwned honest).round contract
                timely facts.1 facts.2.1 facts.2.2.1 executionTrace
                (run.own nodeOwner honest) run.answered (startUntouched other lower)
                (players := drawnPlayers bound turns wholeProfile drawn others assignment)
                (by
                  simp only [drawnPlayers, honest, ↓reduceIte]
                  exact assignedTurnPolicy_decidesAt bound turns wholeProfile nodeOwner assignment
                    other action assigned) reached
            have policy : ∀ (rest : Nat) (execution : app.Execution),
                (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
                  (some ⟨rest + 1, none, execution⟩) →
                PredrawRun bound drawn low high start assignment execution →
                ¬ BlockDone high execution →
                ∀ command ∈ (scheduler execution.environmentRecall
                  (execution.observeEnvironment app)).support,
                ∀ middle ∈ (execution.environmentStep app command).support,
                  command.actor? app = some owner →
                  serviceTurn setup mode deadline leaks owner event (middle.recall owner)
                    (middle.observe app owner) = some 0 →
                  serviceCanonicalPolicy setup mode deadline leaks wholeProfile owner
                      (middle.recall owner) (middle.observe app owner) =
                    law.map fun action =>
                        (serviceRuntime setup mode deadline).canonicalServiceDecision
                      leaks owner (middle.recall owner) (middle.observe app owner) event
                          action := by
              intro rest execution _ run running command _ middle moved active first
              have activateIs : command = .activate owner := by
                cases command with
                | activate actor => cases active; rfl
                | «include» => cases active
                | application => cases active
                | wait => cases active
              subst activateIs
              have sameApp := activation_application setup leaks execution middle owner moved
              have turn : middle.application.publicView.ownTurn? owner = some event :=
                (sourceServiceTurn_first first).1
              have readyNow : execution.application.config.cut.Ready event := by
                rw [← sameApp]
                exact (middle.application.publicView_eventReady event).mp
                  (PublicView.ownTurn?_spec _ owner event turn).1
              obtain ⟨storeEq, ownEq⟩ := playerView_eq_of_reaches relaxed run.reach reachVirtual
                owner
                (fun other notStart done => by
                  have lower : low ≤ other.val :=
                    Nat.le_of_not_gt fun below => notStart ((startPrefix.2 other).mpr below)
                  have upper : other.val < high := by
                    rcases done with inRun | inVirtual
                    · exact run.inside.within.2 other inRun
                    · have := (checkpoint.ordered.2 other).mp inVirtual
                      omega
                  exact bindings other lower upper)
                (fun other otherPayload otherEq => by
                  rw [binding_completed_iff relaxed readyNow outputEq otherEq,
                    checkpoint.ordered.2 other, eventRank])
                (fun completion member otherPayload otherEq notStart => by
                  have done : completion.event ∈ execution.application.config.cut.completed :=
                    (execution.application.config.history_exact _).mp (List.mem_map_of_mem member)
                  have below : completion.event.val < offset := by
                    rw [← eventRank]
                    exact (binding_completed_iff relaxed readyNow outputEq otherEq).mp done
                  have lower : low ≤ completion.event.val :=
                    Nat.le_of_not_gt fun under => notStart ((startPrefix.2 _).mpr under)
                  have otherOwned :=
                      (serviceGraph setup mode).actor?_of_outputLayout_binding otherEq
                  obtain ⟨action, assigned, inVirtual⟩ := assignedOld completion.event owner lower
                    below otherOwned own
                  have inRun := (run.phase completion.event owner action assigned otherOwned
                    own).binding_completed otherEq done
                  have same := completion_eq_of_event inRun member rfl
                  rw [← same]
                  exact inVirtual)
              have result := serviceCanonicalPolicy_commit_of_observation setup leaks fresh guard
                next wholeProfile profile refs source embedding refsBefore offset aligned middle
                (by
                  rw [sameApp, storeEq]
                  exact decodeObservation?_playerStore_eq_some (graph := serviceGraph setup mode)
                    refs owner source.state
                    virtual.store checkpoint.agrees)
                (by
                  rw [sameApp, ownEq, ownCompletions_fromModeCompletion]
                  exact congrFun checkpoint.history owner)
                turn
              rw [result, PMF.map_comp]
              rfl
            have clean : ∀ entry ∈ start.recall owner,
                entry.beforeView.application.publicView.ownTurn? owner ≠ some event :=
              fun entry member turn => startUntouched event eventLow owner entry member
                (PublicView.ownTurn?_spec _ owner event turn).1
            conv_lhs => rw [shape]
            rw [assignedTurnPolicy_runUntil_mixture (serviceInitialLaw setup mode) horizon scheduler
              (drawnPlayers bound turns wholeProfile drawn others assignment) bound turns
              wholeProfile owner assignment event unassigned owned law (BlockDone high)
              (PredrawRun bound drawn low high start assignment) policy preserved rounds remaining
              start trace holds clean]
            simp only [assignChain, own, ↓reduceIte, law, PMF.bind_map]
            rw [PMF.bind_bind]
            apply bind_congr_on_support _
            intro choice _
            obtain ⟨nextCheckpoint, nextReach⟩ := successor choice
            rw [Function.comp_apply, ← drawnPlayers_update bound turns wholeProfile drawn others
              assignment owned own]
            exact ih next (afterCommit profile) prefixed _
              (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _ (offset + 1)
              (commitSuccessor name guard source choice) (tailAligned choice) _
              nextCheckpoint nextReach (by omega) (by omega) _
              (fun other action assigned => by
                by_cases same : other = event
                · subst same
                  omega
                · rw [Function.update_of_ne same] at assigned
                  have range := assignedRange other action assigned
                  omega)
              (fun other otherOwner lower upper otherOwned honest => by
                by_cases same : other = event
                · subst same
                  refine ⟨_, Function.update_self .., ?_⟩
                  rw [EventGraph.Config.complete_history]
                  exact List.mem_append_right _ (List.mem_singleton_self _)
                · have below : other.val < offset := by
                    have : other.val ≠ offset := fun equal => same (Fin.ext (equal.trans
                      eventRank.symm))
                    omega
                  obtain ⟨action, assigned, member⟩ := assignedOld other otherOwner lower below
                    otherOwned honest
                  refine ⟨action, by rw [Function.update_of_ne same]; exact assigned, ?_⟩
                  rw [EventGraph.Config.complete_history]
                  exact List.mem_append_left _ member)
              rounds remaining trace
          · obtain ⟨nextCheckpoint, nextReach⟩ := successor .failure
            have step := ih next (afterCommit profile) prefixed _
              (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _ (offset + 1)
              (commitSuccessor name guard source .failure) (tailAligned .failure) _
              nextCheckpoint nextReach (by omega) (by omega) assignment
              (fun other action assigned => by
                have range := assignedRange other action assigned
                omega)
              (fun other otherOwner lower upper otherOwned honest => by
                have different : other ≠ event := by
                  intro same
                  rw [same, owned] at otherOwned
                  exact own (by rw [Option.some.inj otherOwned]; exact honest)
                have below : other.val < offset := by
                  have : other.val ≠ offset := fun equal => different (Fin.ext (equal.trans
                    eventRank.symm))
                  omega
                obtain ⟨action, assigned, member⟩ := assignedOld other otherOwner lower below
                  otherOwned honest
                refine ⟨action, assigned, ?_⟩
                rw [EventGraph.Config.complete_history]
                exact List.mem_append_left _ member)
              rounds remaining trace
            rw [step]
            simp only [assignChain, own, ↓reduceIte]

/-- **Drawing a block's commitments in advance, against one deviator.** The
case of `Vegas.drawnPlayers_runUntil_predraw` in which every player but one
deviator is drawn. -/
theorem blockPlayers_runUntil_predraw (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wall : BlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (start : (serviceApplication setup mode deadline leaks).Execution)
    (startPrefix : start.application.config.cut.IsPrefix low)
    (startUntouched : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      Untouched setup leaks event start)
    (startOwn : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks start owner)
    (startAnswered : ActivationsAnswered setup leaks start)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (prefixed : CommitPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program)
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (source : Config Player L Γ)
    (aligned : CompiledPolicySuffix setup.program wholeProfile program profile refs
      source.revelations source.registry embedding refsBefore offset)
    (virtual : (serviceGraph setup mode).Config)
    (checkpoint : SourceCheckpoint setup source refs offset virtual)
    (reachVirtual : ConfigReaches setup start.application.config virtual)
    (lowOffset : low ≤ offset) (offsetEnd : offset + count = high)
    (assignment : Assignment setup mode)
    (assignedRange : ∀ event action, assignment event = some action →
      low ≤ event.val ∧ event.val < offset)
    (assignedOld : ∀ event owner, low ≤ event.val → event.val < offset →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∃ action, assignment event = some action ∧
          (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ virtual.history)
    (rounds remaining : Nat)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + rounds, none, start⟩)) :
    (serviceApplication setup mode deadline leaks).runUntil scheduler
        (blockPlayers bound turns wholeProfile who deviation assignment) (BlockDone high)
        rounds start =
      (assignChain setup mode (· ≠ who) count program profile prefixed embedding source
        assignment).bind fun picked =>
        (serviceApplication setup mode deadline leaks).runUntil scheduler
          (blockPlayers bound turns wholeProfile who deviation picked) (BlockDone high)
          rounds start := by
  simp only [blockPlayers_eq_drawnPlayers]
  exact drawnPlayers_runUntil_predraw relaxed wall contract timely turns wholeProfile (· ≠ who)
    (fun _ => deviation) start startPrefix startUntouched startOwn startAnswered bindings count
    program profile prefixed refs embedding refsBefore offset source aligned virtual checkpoint
    reachVirtual lowOffset offsetEnd assignment assignedRange assignedOld rounds remaining trace

end Vegas
