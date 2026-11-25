module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.BindingPrefixObservation
public import Vegas.Game.SourceServiceCanonicalPolicy
public import Vegas.Game.SourceServiceReachedDecoding

@[expose] public section

/-! # Source binding views at native callbacks

A native ready binding and its canonical source-prefix replay have the same
prescribed action kernel when their earlier own records agree. The existing
source residual and prefix decoder recover the genuine source observation.
Neither callback configuration must have a literal source-prefix cut.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

theorem serviceReference_callback_of_binding_paths
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    {inputs : (serviceGraph setup deps).Inputs}
    (origin ghost : (serviceGraph setup deps).Config) (start : Nat)
    (originReach : origin.Reachable inputs) (ordered : origin.cut.IsPrefix start)
    (current : (serviceApplication setup deps duration leaks).Execution)
    (currentPath : Relation.ReflTransGen Config.Step origin current.application.config)
    (ghostPath : Relation.ReflTransGen Config.Step origin ghost)
    (who : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some who)
    (notPublication : ¬ ((serviceGraph setup deps).outputLayout event).IsPublication)
    (currentReady : current.application.config.cut.Ready event)
    (ghostReady : ghost.cut.Ready event) (ghostActive : who ∉ ghost.defaulted)
    (bindings : ∀ prior : (serviceGraph setup deps).EventId,
      start ≤ prior.val → prior.val < event.val →
      ∃ owner payload, (serviceGraph setup deps).outputLayout prior = .binding owner payload)
    (own : ∀ prior : (serviceGraph setup deps).EventId, prior.val < event.val →
      (serviceGraph setup deps).actor? prior = some who →
      completionOf current.application.config prior = completionOf ghost prior)
    {horizon remaining : Nat} {acting : Option Player}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨remaining, acting, current⟩)) :
    referencePolicy (serviceTimeouts setup deps duration) leaks
        ((serviceGraph setup deps).prefixProfile profile) who (current.logs who)
        (current.observe (serviceApplication setup deps duration leaks) who) =
      (actionDistribution ((serviceGraph setup deps).prefixProfile profile) ghost event).map
        ((canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks who
          (current.logs who) (current.observe (serviceApplication setup deps duration leaks) who)
          event) := by
  have currentActive : who ∉ current.application.config.defaulted :=
    current.application.active_of_ready_owned
      (legalFacts setup leaks horizon scheduler _ trace).quiescent currentReady owned
  have turn := current.application.ownTurn?_of_ready (relaxed.actorSerial event) currentReady owned
  have law := prefixProfile_actionDistribution_of_binding_paths relaxed profile origin
    current.application.config ghost start originReach ordered currentPath ghostPath who event
    owned notPublication currentReady ghostReady currentActive ghostActive bindings own
  rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks
    ((serviceGraph setup deps).prefixProfile profile) who current event turn owned,
    dite_eq_right currentActive]
  rw [actionDistribution_of_actor _ _ owned, dite_eq_right currentActive] at law
  exact congrArg (PMF.map _) law

theorem SourceResidual.decode_prefixView
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {ghost : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank ghost)
    {inputs : setup.informationGraph.Inputs} (reachable : ghost.Reachable inputs)
    (clean : ghost.NoBindingDefaults) (who : Player) (event : setup.informationGraph.EventId)
    (eventRank : event.val = rank) :
    let observation := setup.informationGraph.prefixObservation who event
      (setup.informationGraph.playerObserve who ghost)
    decodeViewPrefix? who setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
        rank observation.store (decodeCompletions setup.program observation.ownActions)
        observation.defaults =
      some (ProtocolState.observe who setup.program
        (residual.lift (ProtocolState.entry residual.program residual.source))) := by
  intro observation
  have ordered : ghost.cut.IsPrefix event.val := by
    simpa only [eventRank] using residual.checkpoint.ordered
  have sameObservation : observation = setup.informationGraph.playerObserve who ghost :=
    (prefixObservation_playerObserve_of_prefix who event ghost ordered clean).trans
      (normalizeObservation_playerObserve_of_rankOrdered who ghost
        (rankSort_history_of_reachable setup.informationGraph_total reachable))
  rw [sameObservation]
  change decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
      rank (setup.informationGraph.playerStore who ghost.store)
      (decodeHistory setup.program ghost.history who) ghost.defaults = _
  rw [decodeViewPrefix?_playerStore (graph := setup.informationGraph) who rank setup.program]
  exact decodeViewPrefix?_eq_observe who rank setup.program _ [] _ _ _ _ _ _ residual.decode

/-- Visible source cells remain readable after the callback, even after later visible events. -/
private theorem checkpoint_observation_at_path_end
    {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (ghost : setup.informationGraph.Config) (rank : Nat)
    (checkpoint : SourceCheckpoint setup source refs rank ghost)
    (who : Player) (event : (serviceGraph setup deps).EventId)
    (before after : (serviceGraph setup deps).Config)
    (same : (serviceGraph setup deps).prefixObservation who event
      ((serviceGraph setup deps).playerObserve who before) =
      setup.informationGraph.playerObserve who ghost)
    (path : Relation.ReflTransGen Config.Step before after) :
    decodeObservation? who refs ((serviceGraph setup deps).playerStore who after.store) =
      some (sourceObserve who source.state) := by
  rw [decodeObservation?_playerStore (graph := serviceGraph setup deps) who refs after.store]
  apply decodeObservation?_eq_some_of_visible
  intro name cell ref visible
  have fieldVisible : (cellField cell).VisibleTo who := by cases cell <;> exact visible
  have stores := congrArg EventPlayerObservation.store same
  change (serviceGraph setup deps).playerStore who before.store =
    setup.informationGraph.playerStore who ghost.store at stores
  have beforeRead : (refs.get ref).get? before.store = some (cellValue (source.state.get ref)) := by
    rw [← (refs.get ref).get?_playerStore (graph := serviceGraph setup deps)
      who before.store fieldVisible, stores,
      (refs.get ref).get?_playerStore (graph := setup.informationGraph)
        who ghost.store fieldVisible]
    exact checkpoint.agrees ref
  exact (refs.get ref).get?_preserved before.store after.store
    (fun field value stored => Config.Step.path_store_of_some path field value stored)
    _ beforeRead

omit [IExpr.ResultTypes L] in
/-- Active own binding successors depend only on the prior source view and chosen action. -/
private theorem commit_view_eq_of_view_eq
    {Γ : SourceCtx Player L} {who : Player} {name : VarId} {payload : L.Ty}
    (guard : SourceGuard L Γ who name payload) (left right : Config Player L Γ)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted)
    (same : left.view who = right.view who)
    (choice : Option (PublicationResult (L.Val payload))) :
    (commitSuccessor name guard left choice).view who =
      (commitSuccessor name guard right choice).view who := by
  have observations := congrArg DecisionView.observation same
  have defaults := congrArg DecisionView.defaults same
  have histories := congrArg DecisionView.history same
  change sourceObserve who left.state = sourceObserve who right.state at observations
  change left.defaults = right.defaults at defaults
  change left.history who = right.history who at histories
  have extended : sourceObserve who (Env.cons (x := name) (τ := .commitment who payload)
    (choice.getD .failure) left.state) =
      sourceObserve who (Env.cons (x := name) (τ := .commitment who payload) (choice.getD .failure)
        right.state) := by
    apply congrArg SourceObservation.mk
    funext readName readCell ref
    cases ref with
    | here => rfl
    | there ref =>
        cases readCell <;> exact congrArg (fun observation => observation.cells.get ref)
          observations
  change DecisionView.mk _ _ _ = DecisionView.mk _ _ _
  simp only [commitSuccessor, leftActive, rightActive, ite_false,
    Function.update_self]
  rw [extended, defaults, histories]

/-- Equal final graph observations determine the complete reconstructed own binding view.
Historical pre-target witnesses suffice even after later own events or chance samples:
visible source cells persist, and own choices and default slots are cropped at source rank. -/
theorem source_commit_view_eq_of_playerObserve
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {Γ : SourceCtx Player L} {who : Player} {name : VarId} {payload : L.Ty}
    (guard : SourceGuard L Γ who name payload)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some who)
    (notPublication : ¬ ((serviceGraph setup deps).outputLayout event).IsPublication)
    (leftSource rightSource : Config Player L Γ)
    (leftActive : who ∉ leftSource.defaulted) (rightActive : who ∉ rightSource.defaulted)
    (leftGhost rightGhost : setup.informationGraph.Config)
    (leftCheckpoint : SourceCheckpoint setup leftSource refs event.val leftGhost)
    (rightCheckpoint : SourceCheckpoint setup rightSource refs event.val rightGhost)
    {leftInputs rightInputs : setup.informationGraph.Inputs}
    (leftReach : leftGhost.Reachable leftInputs) (rightReach : rightGhost.Reachable rightInputs)
    (leftClean : leftGhost.NoBindingDefaults) (rightClean : rightGhost.NoBindingDefaults)
    (leftBefore rightBefore : (serviceGraph setup deps).Config)
    (leftReady : leftBefore.cut.Ready event) (rightReady : rightBefore.cut.Ready event)
    (leftFinal rightFinal : (serviceGraph setup deps).Config)
    (leftPath : Relation.ReflTransGen Config.Step leftBefore leftFinal)
    (rightPath : Relation.ReflTransGen Config.Step rightBefore rightFinal)
    (leftMatch : (serviceGraph setup deps).prefixObservation who event
      ((serviceGraph setup deps).playerObserve who leftBefore) =
      setup.informationGraph.prefixObservation who event
        (setup.informationGraph.playerObserve who leftGhost))
    (rightMatch : (serviceGraph setup deps).prefixObservation who event
      ((serviceGraph setup deps).playerObserve who rightBefore) =
      setup.informationGraph.prefixObservation who event
        (setup.informationGraph.playerObserve who rightGhost))
    (sameObservation : (serviceGraph setup deps).playerObserve who leftFinal =
      (serviceGraph setup deps).playerObserve who rightFinal) :
    let readChoice := fun final : (serviceGraph setup deps).Config =>
      OwnAction.binding who name payload (decodeActionAt setup.program event final.history)
    (commitSuccessor name guard leftSource (readChoice leftFinal)).view who =
      (commitSuccessor name guard rightSource (readChoice rightFinal)).view who := by
  intro readChoice
  have ghostObservation (ghost : setup.informationGraph.Config)
      (checkpoint : ghost.cut.IsPrefix event.val) {inputs : setup.informationGraph.Inputs}
      (reachable : ghost.Reachable inputs) (clean : ghost.NoBindingDefaults) :
      setup.informationGraph.prefixObservation who event
        (setup.informationGraph.playerObserve who ghost) =
      setup.informationGraph.playerObserve who ghost :=
    (prefixObservation_playerObserve_of_prefix (graph := setup.informationGraph)
      who event ghost checkpoint clean).trans
      (normalizeObservation_playerObserve_of_rankOrdered (graph := setup.informationGraph) who ghost
        (rankSort_history_of_reachable setup.informationGraph_total reachable))
  have leftMatched := leftMatch.trans
    (ghostObservation leftGhost leftCheckpoint.ordered leftReach leftClean)
  have rightMatched := rightMatch.trans
    (ghostObservation rightGhost rightCheckpoint.ordered rightReach rightClean)
  have leftDecoded := checkpoint_observation_at_path_end leftSource refs leftGhost event.val
    leftCheckpoint who event leftBefore leftFinal leftMatched leftPath
  have rightDecoded := checkpoint_observation_at_path_end rightSource refs rightGhost event.val
    rightCheckpoint who event rightBefore rightFinal rightMatched rightPath
  have stores := congrArg EventPlayerObservation.store sameObservation
  have observations : sourceObserve who leftSource.state = sourceObserve who rightSource.state :=
    Option.some.inj (leftDecoded.symm.trans
      ((congrArg (decodeObservation? who refs) stores).trans rightDecoded))
  have finalOwn := congrArg
    (fun observation => ((serviceGraph setup deps).prefixObservation who event
      observation).ownActions)
    sameObservation
  have leftOwn := RevealRelaxedOrdered.prefixOwnActions_eq_of_ready_path relaxed who event
    leftBefore
    leftFinal leftReady owned notPublication leftPath
  have rightOwn := RevealRelaxedOrdered.prefixOwnActions_eq_of_ready_path relaxed who event
    rightBefore
    rightFinal rightReady owned notPublication rightPath
  have histories : leftSource.history who = rightSource.history who := by
    calc
      _ = decodeCompletions setup.program
          ((serviceGraph setup deps).prefixObservation who event
            ((serviceGraph setup deps).playerObserve who leftBefore)).ownActions := by
        rw [congrArg EventPlayerObservation.ownActions leftMatched]
        exact (congrFun leftCheckpoint.history who).symm
      _ = decodeCompletions setup.program
          ((serviceGraph setup deps).prefixObservation who event
            ((serviceGraph setup deps).playerObserve who leftFinal)).ownActions
              :=
        congrArg (decodeCompletions setup.program) leftOwn
      _ = decodeCompletions setup.program
          ((serviceGraph setup deps).prefixObservation who event
            ((serviceGraph setup deps).playerObserve who rightFinal)).ownActions
              :=
        congrArg (decodeCompletions setup.program) finalOwn
      _ = decodeCompletions setup.program
          ((serviceGraph setup deps).prefixObservation who event
            ((serviceGraph setup deps).playerObserve who rightBefore)).ownActions :=
        congrArg (decodeCompletions setup.program) rightOwn.symm
      _ = _ := by
        rw [congrArg EventPlayerObservation.ownActions rightMatched]
        exact congrFun rightCheckpoint.history who
  have finalDefaults := congrArg
    (fun observation => ((serviceGraph setup deps).prefixObservation who event
      observation).defaults)
    sameObservation
  have leftDefaults := RevealRelaxedOrdered.prefixDefaults_eq_of_ready_path relaxed who event
    leftBefore
    leftFinal leftReady owned notPublication leftPath
  have rightDefaults := RevealRelaxedOrdered.prefixDefaults_eq_of_ready_path relaxed who event
    rightBefore
    rightFinal rightReady owned notPublication rightPath
  have defaults : leftSource.defaults = rightSource.defaults := by
    calc
      _ = ((serviceGraph setup deps).prefixObservation who event
          ((serviceGraph setup deps).playerObserve who leftBefore)).defaults :=
        leftCheckpoint.defaults.symm.trans
          (congrArg EventPlayerObservation.defaults leftMatched).symm
      _ = ((serviceGraph setup deps).prefixObservation who event
          ((serviceGraph setup deps).playerObserve who leftFinal)).defaults :=
        leftDefaults
      _ = ((serviceGraph setup deps).prefixObservation who event
          ((serviceGraph setup deps).playerObserve who rightFinal)).defaults :=
        finalDefaults
      _ = ((serviceGraph setup deps).prefixObservation who event
          ((serviceGraph setup deps).playerObserve who rightBefore)).defaults := rightDefaults.symm
      _ = _ := (congrArg EventPlayerObservation.defaults rightMatched).trans
        rightCheckpoint.defaults
  have previous : leftSource.view who = rightSource.view who := by
    change DecisionView.mk _ _ _ = DecisionView.mk _ _ _
    rw [observations, defaults, histories]
  have chosen : readChoice leftFinal = readChoice rightFinal := by
    dsimp only [readChoice]
    rw [← decodeActionAt_ownCompletions setup.program who event owned
      leftFinal.history leftFinal.history_nodup,
      ← decodeActionAt_ownCompletions setup.program who event owned
        rightFinal.history rightFinal.history_nodup]
    exact congrArg (fun observation => OwnAction.binding who name payload
      (decodeActionAt setup.program event observation.ownActions)) sameObservation
  rw [chosen]
  exact commit_view_eq_of_view_eq guard leftSource rightSource leftActive rightActive previous _

end Vegas
