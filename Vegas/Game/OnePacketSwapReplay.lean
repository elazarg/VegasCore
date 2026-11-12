module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketSwapRecord
public import Vegas.Game.SourceSwapPairs
public import Vegas.Game.OnePacketActingJoint
public import Vegas.Game.OnePacketDecodedActor
public import Vegas.Game.OnePacketReplaySteps
public import Vegas.Game.IntendedPreservation
public import Vegas.Source.ConditionedInitialHistory

@[expose] public section

/-! # Swapped histories replay the swapped intended history

Fix two intended histories `first` and `second` of equal length, with states
`p` and `q`. The native swap of the pairs between `p` and `q`
(`Vegas.betweenPairs`) moves the decoded point of every configuration by the
source swap between `p` and `q` (`Vegas.decodedPoint_betweenPairs`), and a
decoded action of a completion by the same swap.

So along a native history whose intended replay is a prefix of `first`, the
image history under the swap symmetry replays the corresponding prefix of
`second` (`Vegas.intendedHistory?_mapTrace`). Each completion lands on the next
step of `second`: by the prefix correspondence of intended histories the target
is the next state of `second`, and the acting joint of the swapped decoded
action is the joint action of that step, since a realized intended step is the
acting joint of every choice reaching its target.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A decoded action is available at its decoded point** under the forfeiture
interface, to every player. -/
theorem decodeSourcePrefix?_available (who : Player) {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
      some state →
    (inside : count < eventCount program) →
    ∀ (graphAction : EventGraph.EventField.Action (outputLayout program ⟨count, inside⟩))
      (action : OwnAction Player L),
      decodeEventAction program ⟨count, inside⟩ graphAction = some action →
      action ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program)
        (ProtocolState.observe who program state)
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults,
      state, decoded, inside => by
      cases program with
      | ret _ => simp [eventCount] at inside
      | sample _ _ _ next =>
          intro _ _ decodedAction
          cases decodedAction
      | commit _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro graphAction action decodedAction
          cases decodedAction
          refine ⟨graphAction, ?_, rfl⟩
          cases graphAction with
          | none => trivial
          | some result => cases result <;> trivial
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro graphAction action decodedAction
          cases decodedAction
          exact ⟨graphAction, rfl⟩
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, state,
      decoded, inside => by
      cases program with
      | ret _ => cases decoded
      | sample _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | commit _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)

variable {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

private theorem sourceStep_congr :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (point : ProtocolState program) →
    (first second : Player → Option (OwnAction Player L)) →
    (∀ who, ProtocolView.actor who program (ProtocolState.observe who program point) =
      some who → first who = second who) →
    ProtocolState.step program point first = ProtocolState.step program point second
  | _, _, .ret _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, first, second, agree => by
      cases point with
      | inl _ => rfl
      | inr point =>
          exact congrArg (fun law => law.map Sum.inr)
            (sourceStep_congr next point first second agree)
  | _, _, .commit name owner fresh guard next, point, first, second, agree => by
      cases point with
      | inl config =>
          by_cases inactive : owner ∈ config.defaulted
          · simp [ProtocolState.step, commitSuccessor, inactive]
          · have choice := agree owner (by
              simp [ProtocolView.actor, ProtocolState.observe, inactive])
            simp only [ProtocolState.step, Sum.elim_inl, choice]
      | inr point =>
          exact congrArg (fun law => law.map Sum.inr)
            (sourceStep_congr next point first second agree)
  | _, _, .reveal published owner name fresh source unresolved next,
      point, first, second, agree => by
      cases point with
      | inl config =>
          by_cases inactive : owner ∈ config.defaulted
          · simp [ProtocolState.step, revealSuccessor, inactive]
          · have choice := agree owner (by
              simp [ProtocolView.actor, ProtocolState.observe, inactive])
            simp only [ProtocolState.step, Sum.elim_inl, choice]
      | inr point =>
          exact congrArg (fun law => law.map Sum.inr)
            (sourceStep_congr next point first second agree)

private theorem decodedPoint_step_actualDecision {config : (graph setup).Config}
    {event : (graph setup).EventId} (ready : config.cut.Ready event)
    {point : ProtocolState setup.program} (decoded : decodedPoint setup config = some point)
    (action : (graph setup).Action event) :
    ProtocolState.step setup.program point
        (fun _ => (config.actualDecision event action).bind
          (decodeEventAction setup.program event)) =
      ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action) := by
  apply sourceStep_congr
  intro who acts
  have filtered := (decodedPoint_actor who ready decoded).symm.trans acts
  obtain ⟨owned, active⟩ := Option.filter_eq_some_iff.mp filtered
  simp only [decide_eq_true_eq] at active
  rw [config.actualDecision_of_active event who owned active action]
  rfl

/-- **A completion's decoded action is addressed to its decoded point**: it is
available there to every active player under the forfeiture interface. -/
theorem decoded_addressed {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (graphAction : (graph setup).Action event) :
    ∀ who action, decodeEventAction setup.program event graphAction = some action →
      (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).active
        (some point) who →
      action ∈ (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).available
        (some point) who := by
  intro who action decodedAction _
  have ordered : config.cut.IsPrefix event.val :=
    ⟨event.isLt.le, fun query =>
      setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
  rw [decodedPoint_eq_of_isPrefix ordered] at decoded
  exact decodeSourcePrefix?_available who event.val setup.program _ _ _ _ _ _ _ point
    decoded event.isLt graphAction action decodedAction

section Between

variable [DecidableEq (CellTy Player L)] {first second : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup first second}
  {succeed : CommitmentCellsSucceed setup first second}

/-- **The decoded point of a swapped configuration** is the swapped decoded point. -/
theorem decodedPoint_betweenPairs (config : (graph setup).Config) :
    decodedPoint setup (config.swap (EventGraph.ValueSwap.ofPairs
        (betweenPairs publicAgree succeed))) =
      (decodedPoint setup config).map
        ((CellSwap.between setup.program first second).protocolState setup.program) := by
  unfold decodedPoint
  by_cases ordered : ∃ rank, config.cut.IsPrefix rank
  · have swappedOrdered : ∃ rank, (config.swap (EventGraph.ValueSwap.ofPairs
        (betweenPairs publicAgree succeed))).cut.IsPrefix rank := ordered
    rw [dite_eq_left_of_eq_true (eq_true swappedOrdered),
      dite_eq_left_of_eq_true (eq_true ordered)]
    exact sourceServicePrefix?_betweenPairs _ config
  · have swappedOrdered : ¬ ∃ rank, (config.swap (EventGraph.ValueSwap.ofPairs
        (betweenPairs publicAgree succeed))).cut.IsPrefix rank := ordered
    rw [dite_eq_right_of_eq_false (eq_false swappedOrdered),
      dite_eq_right_of_eq_false (eq_false ordered)]
    rfl

end Between

end Vegas

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A nonempty history extends a shorter one by one step. -/
theorem exists_extend_of_length_pos {ι : Type*} {E : ExecutionProtocol ι} {state : E.State}
    (trace : E.Trace state) (positive : 0 < trace.length) :
    ∃ (source : E.State) (shorter : E.Trace source) (joint : ∀ i, Option (E.Action i))
      (isLegal : E.Legal source joint)
      (realized : state ∈ (E.step source ⟨joint, isLegal⟩).support),
      trace = shorter.extend joint isLegal realized ∧ shorter.length + 1 = trace.length := by
  cases trace with
  | start => simp [Trace.length] at positive
  | extend shorter joint isLegal realized => exact ⟨_, shorter, joint, isLegal, realized, rfl, rfl⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The history a prefix extends by one step is a prefix as well. -/
theorem TracePrefix.of_extend {ι : Type*} {E : ExecutionProtocol ι} {source target final : E.State}
    {prior : E.Trace source} {joint : ∀ i, Option (E.Action i)} {isLegal : E.Legal source joint}
    {realized : target ∈ (E.step source ⟨joint, isLegal⟩).support} {trace : E.Trace final}
    (isPrefix : TracePrefix (prior.extend joint isLegal realized) trace) :
    TracePrefix prior trace :=
  (TracePrefix.extend .refl joint isLegal realized).trans isPrefix

/-- An advanced replay extends the replay it advances. -/
theorem tracePrefix_of_advanceIntended? {leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (graph setup))}
    {history result : setup.intendedProtocol.History}
    {before after : (application setup timeouts leaks).ProtocolState}
    (advanced : advanceIntended? setup timeouts leaks history before after = some result) :
    TracePrefix history.trace result.trace := by
  have extended : ∀ {choice target}, extendIntended? setup history choice target = some result →
      TracePrefix history.trace result.trace := by
    intro choice target extendedEq
    unfold extendIntended? at extendedEq
    split at extendedEq
    · split at extendedEq
      · cases extendedEq
        exact .extend .refl _ _ _
      · cases extendedEq
    · cases extendedEq
  match before, after, advanced with
  | none, some _, advanced => exact extended advanced
  | some before, some after, advanced =>
      simp only [advanceIntended?] at advanced
      rcases dropped : List.drop before.execution.application.config.history.length
          after.execution.application.config.history with
        _ | ⟨record, _ | ⟨_, _⟩⟩
      · rw [dropped] at advanced
        cases advanced
        exact .refl
      · rw [dropped] at advanced
        exact extended advanced
      · rw [dropped] at advanced
        cases advanced

variable [DecidableEq (CellTy Player L)]

omit [DecidableEq (CellTy Player L)] in
private theorem defaults_record_step :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (before after : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → ¬ ProtocolState.terminal program before →
    after ∈ (ProtocolState.step program before joint).support →
    ∃ event, ProtocolState.defaults program after =
      (ProtocolState.defaults program before).record event
  | _, _, .ret _, _, _, _, running, _ => (running trivial).elim
  | _, _, .sample _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          obtain ⟨value, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact ⟨none, by rw [ProtocolState.defaults, Sum.elim_inr,
            ProtocolState.defaults_entry]; rfl⟩
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact defaults_record_step next rest target joint running supported
  | _, _, .commit _ _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          simp only [ProtocolState.defaults, Sum.elim_inl, Sum.elim_inr,
            ProtocolState.defaults_entry, commitSuccessor]
          exact ⟨_, rfl⟩
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact defaults_record_step next rest target joint running supported
  | _, _, .reveal _ _ _ _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          simp only [ProtocolState.defaults, Sum.elim_inl, Sum.elim_inr,
            ProtocolState.defaults_entry, revealSuccessor]
          exact ⟨_, rfl⟩
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact defaults_record_step next rest target joint running supported

omit [DecidableEq (CellTy Player L)] in
private theorem intended_defaults_trace (wellFormed : setup.WellFormed) :
    ∀ {state} (trace : setup.intendedProtocol.Trace state),
      setup.protocolDefaults state = ⟨List.replicate (trace.length - 1) none⟩
  | _, .start => rfl
  | _, .extend (source := before) prior joint legal realized => by
      have earlier := intended_defaults_trace wellFormed prior
      cases before with
      | none =>
          have empty : prior.length = 0 :=
            congrArg Trace.length (setup.intended_trace_none prior)
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ realized
          simp only [Setup.protocolDefaults, ProtocolState.defaults_entry, Config.initial,
            Trace.length, empty, Nat.zero_add, Nat.sub_self, List.replicate_zero]
      | some before =>
          have positive : 0 < prior.length :=
            setup.intended_trace_positive prior (by simp)
          obtain ⟨after, supported, rfl⟩ := PMF.support_map .. ▸ realized
          have intended : ProtocolState.Intended setup.program after :=
            setup.intendedState_trace wellFormed (.extend prior joint legal
              ((PMF.mem_support_map_iff _ _ _).mpr ⟨after, supported, rfl⟩))
          obtain ⟨event, record⟩ := defaults_record_step setup.program before after joint
            legal.1 supported
          have silent : event = none := by
            cases event with
            | none => rfl
            | some who =>
                apply False.elim
                apply ProtocolState.not_excluded_of_intended who setup.program after intended
                unfold ProtocolState.Excluded
                rw [ProtocolState.defaulted_eq_defaults, record,
                  DefaultHistory.defaulted_record_some]
                exact Finset.mem_insert_self who _
          change ProtocolState.defaults setup.program after = _
          change ProtocolState.defaults setup.program before = _ at earlier
          rw [silent, earlier] at record
          rw [record]
          change (⟨none :: List.replicate (prior.length - 1) none⟩ : DefaultHistory Player) =
            ⟨List.replicate (prior.length + 1 - 1) none⟩
          apply congrArg DefaultHistory.mk
          rw [show prior.length + 1 - 1 = (prior.length - 1) + 1 by omega,
            List.replicate_succ]

/-- **One step of a prefix lands on the next step of the corresponding prefix.**
Let `extended` be a prefix of `first` extending `prior` by one step, and let
`prior'` be the prefix of `second` of the same length as `prior`. If the
acting joint of a choice addressed to the state of `prior'` reaches the swapped
state of `extended`, then extending `prior'` by that choice to that state is
the prefix of `second` of the same length as `extended`. -/
theorem extendIntended?_between {first second : setup.intendedProtocol.History}
    {p q : ProtocolState setup.program} (firstState : first.state = some p)
    (secondState : second.state = some q)
    (sameLength : first.trace.length = second.trace.length)
    (sameDefaults : ProtocolState.defaults setup.program p =
      ProtocolState.defaults setup.program q)
    {prior extended prior' : setup.intendedProtocol.History}
    (oneStep : extended.trace.length = prior.trace.length + 1)
    (extendedPrefix : TracePrefix extended.trace first.trace)
    (priorPrefix' : TracePrefix prior'.trace second.trace)
    (priorLength : prior'.trace.length = prior.trace.length)
    {admission : CommitmentInterface setup.program} {choice : Option (OwnAction Player L)}
    (addressed : ∀ who action, choice = some action →
      (setup.executionProtocol admission).active prior'.state who →
        action ∈ (setup.executionProtocol admission).available prior'.state who)
    (reaches : extended.state.map
        ((CellSwap.between setup.program p q).protocolState setup.program) ∈
      (setup.protocolStep prior'.state (actingJoint setup prior'.state choice)).support) :
    ∃ extended', extendIntended? setup prior' choice (extended.state.map
        ((CellSwap.between setup.program p q).protocolState setup.program)) = some extended' ∧
      TracePrefix extended'.trace second.trace ∧
      extended'.trace.length = extended.trace.length := by
  obtain ⟨state', trace', prefix', length', stateEq⟩ :=
    Setup.intended_prefix_between setup firstState secondState sameLength sameDefaults
      extended.trace
      extendedPrefix
  obtain ⟨source, shorter, joint, legal, realized, rfl, shorterLength⟩ :=
    exists_extend_of_length_pos trace' (by omega)
  have shorterPrefix := TracePrefix.of_extend prefix'
  have samePrior := TracePrefix.eq_of_same_length shorterPrefix priorPrefix' (by omega)
  rcases prior' with ⟨priorState, priorTrace⟩
  cases samePrior
  have jointEq := intended_joint_eq_actingJoint setup legal realized choice addressed
    (stateEq ▸ reaches)
  subst jointEq
  refine ⟨⟨state', priorTrace.extend _ legal realized⟩, ?_, prefix', by omega⟩
  rw [← stateEq]
  unfold extendIntended?
  rw [dite_eq_left_of_eq_true (eq_true legal), dite_eq_left_of_eq_true (eq_true realized)]

end Vegas

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  [DecidableEq (CellTy Player L)]

omit [Fintype Player] [DecidableEq (CellTy Player L)] in
/-- The history of a swapped configuration from a later step. -/
theorem drop_history_swap (swap : (graph setup).ValueSwap) (before after : (graph setup).Config) :
    (after.swap swap).history.drop (before.swap swap).history.length =
      (after.history.drop before.history.length).map swap.completion := by
  rw [EventGraph.Config.swap_history, EventGraph.Config.swap_history, List.length_map,
    List.map_drop]

omit [Fintype Player] [DecidableEq (CellTy Player L)] in
theorem advanceIntended?_of_drop_nil (history : setup.intendedProtocol.History)
    (before after : (application setup timeouts leaks).Control)
    (dropped : after.execution.application.config.history.drop
      before.execution.application.config.history.length = []) :
    advanceIntended? setup timeouts leaks history (some before) (some after) = some history := by
  simp only [advanceIntended?, dropped]

omit [Fintype Player] [DecidableEq (CellTy Player L)] in
theorem advanceIntended?_of_drop_single (history : setup.intendedProtocol.History)
    (before after : (application setup timeouts leaks).Control) (event : (graph setup).EventId)
    (decision : Option ((graph setup).Action event)) (defaultEvent : Option Player)
    (dropped : after.execution.application.config.history.drop
      before.execution.application.config.history.length = [⟨event, decision, defaultEvent⟩]) :
    advanceIntended? setup timeouts leaks history (some before) (some after) =
      extendIntended? setup history (decision.bind (decodeEventAction setup.program event))
        (decodedPoint setup after.execution.application.config) := by
  simp only [advanceIntended?, dropped]

/-- **Swapped histories replay the corresponding prefix of the second intended
history.** -/
theorem intendedHistory?_mapTrace (wellFormed : setup.WellFormed)
    {first second : setup.intendedProtocol.History}
    {p q : ProtocolState setup.program} (firstState : first.state = some p)
    (secondState : second.state = some q)
    (sameLength : first.trace.length = second.trace.length)
    {publicAgree : PublicCellsAgree setup p q} {succeed : CommitmentCellsSucceed setup p q}
    (handlePairs : Handle (graph setup) → Option (Raw L × Raw L))
    {allowed : Set (graph setup).Inputs}
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) ∈
        (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values →
      (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).raw handle raw ∈
        bounds.values) :
    ∀ {state} (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      state)
      (guarded : SwapGuardState setup timeouts
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) allowed state)
      {replay : setup.intendedProtocol.History},
      intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some replay →
      TracePrefix replay.trace first.trace →
      ∃ image, intendedHistory? setup timeouts leaks bounds horizon scheduler
          ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
            (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
            bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded) =
          some image ∧
        TracePrefix image.trace second.trace ∧ image.trace.length = replay.trace.length ∧
        image.state = replay.state.map
          ((CellSwap.between setup.program p q).protocolState setup.program)
  | _, .start, _, replay, replayed, _ => by
      cases replayed
      exact ⟨setup.intendedProtocol.initHistory, rfl, TracePrefix.start second.trace, rfl, rfl⟩
  | _, .extend (source := before) (target := after) prior joint legal realized, guarded, replay,
      replayed, firstPrefix => by
      have sameDefaults : ProtocolState.defaults setup.program p =
          ProtocolState.defaults setup.program q := by
        have firstDefaults := (congrArg setup.protocolDefaults firstState).symm.trans
          (intended_defaults_trace wellFormed first.trace)
        have secondDefaults := (congrArg setup.protocolDefaults secondState).symm.trans
          (intended_defaults_trace wellFormed second.trace)
        exact firstDefaults.trans (by rw [sameLength]; exact secondDefaults.symm)
      have priorGuard := (onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup)
        horizon scheduler
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
        bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).guard_source prior legal realized
          guarded
      change (intendedHistory? setup timeouts leaks bounds horizon scheduler prior).bind
        (fun history => advanceIntended? setup timeouts leaks history before after) = some replay
        at replayed
      obtain ⟨previous, previousReplay, advanced⟩ := Option.bind_eq_some_iff.mp replayed
      have previousPrefix := (tracePrefix_of_advanceIntended? (timeouts := timeouts) advanced).trans
        firstPrefix
      obtain ⟨previous', previousImage, previousPrefix', previousLength, previousState⟩ :=
        intendedHistory?_mapTrace wellFormed firstState secondState sameLength
          handlePairs initialClosed
          bounded prior priorGuard previousReplay previousPrefix
      have mappedEq : intendedHistory? setup timeouts leaks bounds horizon scheduler
          ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
            (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
            bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace
              (.extend prior joint legal realized) guarded) =
          advanceIntended? setup timeouts leaks previous'
            ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState
              (timeouts := timeouts)
              before)
            ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState
              (timeouts := timeouts)
              after) := by
        rw [StateSymmetry.mapTrace_extend]
        change (intendedHistory? setup timeouts leaks bounds horizon scheduler _).bind _ = _
        rw [previousImage]
        rfl
      have realizedImage := (onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup)
        horizon scheduler
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
        bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).realized prior legal realized guarded
      rw [mappedEq]
      have oneStep : ∀ {choice target}, extendIntended? setup previous choice target =
          some replay → replay.trace.length = previous.trace.length + 1 := by
        intro choice target extended
        unfold extendIntended? at extended
        split at extended
        · split at extended
          · cases extended
            rfl
          · cases extended
        · cases extended
      rcases before with _ | current <;> rcases after with _ | next
      · cases advanced
      · -- The initial draw.
        change extendIntended? setup previous none
          (decodedPoint setup next.execution.application.config) = some replay at advanced
        have replayStateEq := extendIntended?_state advanced
        have previousNone : previous'.state = none := by
          rw [previousState]
          obtain rfl := trace_eq_start_of_none (timeouts := timeouts) prior
          cases previousReplay
          rfl
        change some (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs
          publicAgree succeed)
          handlePairs) next) ∈ ((application setup timeouts leaks).transition
          (initialLaw setup) horizon scheduler none
          ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).joint (timeouts :=
            timeouts)
            joint)).support at realizedImage
        rw [ReactiveApplication.transition, PMF.support_map] at realizedImage
        obtain ⟨initialState, initialMember, initialEq⟩ := realizedImage
        have drawn : initialState ∈ (initialLaw setup).support := initialMember
        rw [initialLaw, serviceInitialLaw, PMF.support_map] at drawn
        obtain ⟨initialValues, valuesMember, initialStateEq⟩ := drawn
        have swappedConfig : next.execution.application.config.swap
            (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)) =
            initialState.config := by
          have := congrArg (fun control : Option (application setup timeouts leaks).Control =>
            control.map fun current => current.execution.application.config) initialEq
          exact (Option.some.inj this).symm
        have swappedDecoded : (decodedPoint setup next.execution.application.config).map
            ((CellSwap.between setup.program p q).protocolState setup.program) =
            some (ProtocolState.entry setup.program (Config.initial initialValues)) := by
          rw [← decodedPoint_betweenPairs (publicAgree := publicAgree) (succeed := succeed),
            swappedConfig, ← initialStateEq, decodedPoint_initial]
        have reaches : replay.state.map
            ((CellSwap.between setup.program p q).protocolState setup.program) ∈
            (setup.protocolStep previous'.state
              (actingJoint setup previous'.state none)).support := by
          rw [previousNone, replayStateEq, swappedDecoded]
          change _ ∈ (setup.initialLaw.map fun initial =>
            some (ProtocolState.entry setup.program (Config.initial initial))).support
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨initialValues, valuesMember, rfl⟩
        obtain ⟨image, extended, imagePrefix, imageLength⟩ := extendIntended?_between
          (admission := CommitmentInterface.forfeiture setup.program) firstState secondState
          sameLength sameDefaults (oneStep advanced) firstPrefix previousPrefix' previousLength
          (fun _ _ impossible => by cases impossible) reaches
        refine ⟨image, ?_, imagePrefix, imageLength, ?_⟩
        · change extendIntended? setup previous' none (decodedPoint setup
            (next.execution.application.config.swap (EventGraph.ValueSwap.ofPairs
              (betweenPairs publicAgree succeed)))) = some image
          rw [decodedPoint_betweenPairs, ← replayStateEq]
          exact extended
        · exact extendIntended?_state extended
      · cases advanced
      · -- A scheduler round or a response between initialized states.
        have previousStateEq := intendedHistory?_state (timeouts := timeouts) prior previousReplay
        change previous.state = decodedPoint setup current.execution.application.config
          at previousStateEq
        simp only [advanceIntended?] at advanced
        have droppedImage := drop_history_swap
          (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))
          current.execution.application.config next.execution.application.config
        change some (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs
          publicAgree succeed)
            handlePairs) next) ∈ ((application setup timeouts leaks).transition
            (initialLaw setup) horizon scheduler
            (some (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs
              publicAgree succeed)
              handlePairs) current))
            ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).joint (timeouts :=
              timeouts)
              joint)).support at realizedImage
        rcases dropped : List.drop current.execution.application.config.history.length
            next.execution.application.config.history with
          _ | ⟨record, _ | ⟨_, _⟩⟩
        · rw [dropped] at advanced droppedImage
          cases advanced
          exact ⟨previous', advanceIntended?_of_drop_nil (timeouts := timeouts) (leaks := leaks)
            previous'
            (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs publicAgree
              succeed)
              handlePairs) current)
            (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs publicAgree
              succeed)
              handlePairs) next) droppedImage, previousPrefix', previousLength, previousState⟩
        · rw [dropped] at advanced droppedImage
          have replayStateEq := extendIntended?_state advanced
          obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts)
            (failureProfile setup.program)
            (bounds.onePacketMenu timeouts leaks) horizon scheduler
            ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon
              scheduler
              (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
              bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace prior priorGuard) _ rfl
          have path := reactive_protocol_graph_steps timeouts leaks (initialLaw setup) horizon
            scheduler _ _ _ realizedImage
          change Relation.ReflTransGen EventGraph.Config.Step
            (current.execution.application.config.swap
              (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)))
            (next.execution.application.config.swap
              (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))) at path
          obtain ⟨stepReady, stepAction, member⟩ := EventGraph.Config.Step.path_singleton path
            ((EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).completion record)
            (by simpa only [dropped, List.map_singleton] using droppedImage)
          obtain ⟨point, target, decodedCurrent, decodedNext, reachedStep⟩ :=
            decodedPoint_step residual record.event stepReady stepAction _ member
          obtain ⟨value, _output, historyEq⟩ :=
            (current.execution.application.config.swap
              (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))).step_completion
              record.event stepReady stepAction _ member
          change (next.execution.application.config.swap
            (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))).history =
              (current.execution.application.config.swap
                (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))).history ++
                [EventGraph.completion (graph setup) record.event
                  ((current.execution.application.config.swap
                    (EventGraph.ValueSwap.ofPairs
                      (betweenPairs publicAgree succeed))).actualDecision
                      record.event stepAction) value] at historyEq
          have recordEq : EventGraph.completion (graph setup) record.event
              ((current.execution.application.config.swap
                (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))).actualDecision
                  record.event stepAction) value =
                (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).completion
                  record := by
            apply List.singleton_injective
            simpa only [historyEq, List.drop_left, dropped, List.map_singleton] using droppedImage
          have chosen :
              ((EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).completion
                record).decision =
              (current.execution.application.config.swap
                (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))).actualDecision
                  record.event stepAction := by
            have packed := congrArg (fun completion : (graph setup).Completion =>
              (⟨completion.event, completion.decision⟩ :
                Σ event, Option ((graph setup).Action event))) recordEq
            exact (eq_of_heq (Sigma.mk.inj packed).2).symm
          have previousPoint : previous'.state = some point := by
            rw [previousState, previousStateEq, ← decodedPoint_betweenPairs
              (publicAgree := publicAgree) (succeed := succeed)]
            exact decodedCurrent
          have targetEq : replay.state.map
              ((CellSwap.between setup.program p q).protocolState setup.program) =
              some target := by
            rw [replayStateEq, ← decodedPoint_betweenPairs (publicAgree := publicAgree)
              (succeed := succeed)]
            exact decodedNext
          have choiceEq :
              (((EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).completion
                record).decision.bind (decodeEventAction setup.program record.event)) =
              (record.decision.bind (decodeEventAction setup.program record.event)).map
                (CellSwap.between setup.program p q).action := by
            cases decision : record.decision with
            | none => simp [EventGraph.ValueSwap.completion, decision]
            | some action =>
                simpa only [EventGraph.ValueSwap.completion, decision, Option.map_some,
                  Option.bind_some] using decodeEventAction_betweenPairs
                    (publicAgree := publicAgree) (succeed := succeed) record.event action
          have actualStep := decodedPoint_step_actualDecision stepReady decodedCurrent stepAction
          change ProtocolState.step setup.program point
              (fun _ => ((current.execution.application.config.swap
                (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))).actualDecision
                  record.event stepAction).bind (decodeEventAction setup.program record.event)) =
            ProtocolState.step setup.program point
              (fun _ => decodeEventAction setup.program record.event stepAction) at actualStep
          have reaches : replay.state.map
              ((CellSwap.between setup.program p q).protocolState setup.program) ∈
              (setup.protocolStep previous'.state (actingJoint setup previous'.state
                ((record.decision.bind (decodeEventAction setup.program record.event)).map
                  (CellSwap.between setup.program p q).action))).support := by
            rw [targetEq, previousPoint, protocolStep_actingJoint, ← choiceEq, chosen,
              actualStep, PMF.support_map]
            exact ⟨target, reachedStep, rfl⟩
          obtain ⟨image, extended, imagePrefix, imageLength⟩ := extendIntended?_between
            (admission := CommitmentInterface.forfeiture setup.program) firstState secondState
            sameLength sameDefaults (oneStep advanced) firstPrefix previousPrefix' previousLength
            (by
              rw [previousPoint, ← choiceEq]
              intro who action decodedAction active
              cases choice : ((EventGraph.ValueSwap.ofPairs
                  (betweenPairs publicAgree succeed)).completion record).decision with
              | none => simp [choice] at decodedAction
              | some graphAction =>
                  exact decoded_addressed (event := record.event) stepReady decodedCurrent
                    graphAction
                    who action
                    (by simpa only [choice, Option.bind_some] using decodedAction) active)
            reaches
          refine ⟨image, ?_, imagePrefix, imageLength, ?_⟩
          · refine (advanceIntended?_of_drop_single (timeouts := timeouts) (leaks := leaks)
              previous'
              (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs
                (betweenPairs publicAgree succeed) handlePairs) current)
              (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs
                (betweenPairs publicAgree succeed) handlePairs) next)
              record.event _ _ (by
                change (next.execution.application.config.swap
                    (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))).history.drop
                  (current.execution.application.config.swap
                    (EventGraph.ValueSwap.ofPairs
                      (betweenPairs publicAgree succeed))).history.length =
                    _
                simpa only [dropped, List.map_singleton, EventGraph.ValueSwap.completion]
                  using droppedImage)).trans ?_
            change extendIntended? setup previous' _ (decodedPoint setup
              (next.execution.application.config.swap (EventGraph.ValueSwap.ofPairs
                (betweenPairs publicAgree succeed)))) = _
            rw [decodedPoint_betweenPairs, ← replayStateEq]
            change extendIntended? setup previous'
              (((EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).completion
                record).decision.bind (decodeEventAction setup.program record.event)) _ = _
            rw [choiceEq]
            exact extended
          · exact extendIntended?_state extended
        · rw [dropped] at advanced
          cases advanced

end Vegas
