/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyCoherence
import Vegas.Pending.EventResolutionBlock
import Vegas.Pending.EventInvariant
import Interaction.MessageApplicationLocality

/-! # Local observations in event-service replay

Private staging by another player preserves the focal player's entire native
input. The public scheduler also sees no change. These are equalities of the
actual runtime projections, not restrictions on what a deviator may inspect.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Another player's arbitrary private command preserves every component of
the observer's application view, including its own candidate catalogue. -/
theorem privateStep_other_playerView (state : State graph) (owner observer : Player)
    (different : observer ≠ owner) (command : PrivateCommand graph) :
    (privateStep state owner command).playerView observer = state.playerView observer := by
  cases command with
  | prepare serial raw =>
      have candidates :
          (fun slot => (state.candidates.prepare owner (.prepared serial) raw).lookup
            (observer, slot)) = (fun slot => state.candidates.lookup (observer, slot)) := by
        funext slot
        apply CommitmentCandidates.lookup_prepare_other
        exact fun same => different (congrArg Prod.fst same)
      simp only [privateStep, State.playerView]
      rw [candidates]
      rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some owner
      · rw [privateStep, dif_pos owned]
        cases cached : state.remembered event with
        | some prior => rfl
        | none =>
            have memory :
                (fun query => if graph.actor? query = some observer then
                  Function.update state.remembered event (some action) query else none) =
                (fun query => if graph.actor? query = some observer then
                  state.remembered query else none) := by
              funext query
              by_cases same : query = event
              · subst query
                simp [owned, Ne.symm different]
              · simp [Function.update_of_ne same]
            simp only [State.playerView]
            rw [memory]
            rfl
      · rw [privateStep, dif_neg owned]

/-- Private commands do not advance the semantic event configuration. -/
theorem privateStep_config (state : State graph) (owner : Player)
    (command : PrivateCommand graph) :
    (privateStep state owner command).config = state.config := by
  cases command with
  | prepare => rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some owner
      · rw [privateStep, dif_pos owned]
        cases state.remembered event <;> rfl
      · rw [privateStep, dif_neg owned]

@[simp] theorem stagingCount_append (runtime : EventGraphRuntime graph)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (command : runtime.application.PlayerCommand) (event : graph.EventId) :
    stagingCount (history ++ [⟨view, command⟩]) event =
      stagingCount history event + if stagesEvent event command then 1 else 0 := by
  cases marked : stagesEvent event command <;> simp [stagingCount, marked]

/-- Private staging remains hidden even when the observer retains its entire
authenticated request history and all delivered and included packets. -/
theorem playerStep_other_input (runtime : EventGraphRuntime graph)
    (owner observer : Player) (different : observer ≠ owner)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (member : next ∈ (runtime.application.playerStep owner execution command).support) :
    (next.principalHistory observer,
        MessageApplication.State.observe runtime.application next.native observer) =
      (execution.principalHistory observer,
        MessageApplication.State.observe runtime.application execution.native observer) := by
  exact runtime.application.playerStep_other_input owner observer different
    (fun state command => privateStep_other_playerView state owner observer different command)
    execution next command member

/-- Equal authenticated focal views remain equal after applying the same
focal private command. Foreign candidate meanings and remembered actions are
not compared. -/
theorem privateStep_focal_playerView_congr
    (left right : State graph) (focal : Player) (command : PrivateCommand graph)
    (publicEq : left.publicView = right.publicView)
    (observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config)
    (rememberedEq : (fun event => if graph.actor? event = some focal then
      left.remembered event else none) = fun event =>
        if graph.actor? event = some focal then right.remembered event else none)
    (candidatesEq : (fun slot => left.candidates.lookup (focal, slot)) =
      fun slot => right.candidates.lookup (focal, slot)) :
    (privateStep left focal command).playerView focal =
      (privateStep right focal command).playerView focal := by
  cases command with
  | prepare serial raw =>
      unfold State.playerView
      congr 1
      funext slot
      by_cases same : (focal, slot) = (focal, Slot.prepared serial)
      · have slotEq : slot = Slot.prepared serial := congrArg Prod.snd same
        subst slot
        simp only [privateStep, CommitmentCandidates.lookup_prepare_self]
        rw [congrFun candidatesEq (Slot.prepared serial)]
      · simp only [privateStep]
        rw [left.candidates.lookup_prepare_other focal (.prepared serial) raw
            (focal, slot) same,
          right.candidates.lookup_prepare_other focal (.prepared serial) raw
            (focal, slot) same,
          congrFun candidatesEq slot]
  | remember event action =>
      by_cases owned : graph.actor? event = some focal
      · have cachedEq : left.remembered event = right.remembered event := by
          have atEvent := congrFun rememberedEq event
          simpa [State.playerView, owned] using atEvent
        rw [privateStep, dif_pos owned, privateStep, dif_pos owned]
        cases leftCached : left.remembered event with
        | none =>
            have rightCached : right.remembered event = none := cachedEq.symm.trans leftCached
            simp only [rightCached]
            unfold State.playerView
            congr 1
            funext query
            by_cases same : query = event
            · subst query
              simp [owned]
            · simp only
              rw [Function.update_of_ne same, Function.update_of_ne same]
              exact congrFun rememberedEq query
        | some prior =>
            have rightCached : right.remembered event = some prior := cachedEq.symm.trans leftCached
            simp only [rightCached]
            unfold State.playerView
            congr 1
      · rw [privateStep, dif_neg owned, privateStep, dif_neg owned]
        unfold State.playerView
        congr 1

/-- The native data that must agree when replaying one fixed pure policy at
`focal`.  Other players' private candidates, remembered actions, and complete
histories are intentionally absent.  Their two policy cursors are retained
only through the event-local counters read by the compiled policies. -/
structure NativeReplay (runtime : EventGraphRuntime graph) (focal : Player)
    (left right : runtime.application.PolicyExecution) : Prop where
  publicView : left.native.application.publicView =
    right.native.application.publicView
  observation : graph.playerObserve focal left.native.application.config =
    graph.playerObserve focal right.native.application.config
  remembered : (fun event => if graph.actor? event = some focal then
      left.native.application.remembered event else none) =
    fun event => if graph.actor? event = some focal then
      right.native.application.remembered event else none
  candidates : (fun slot =>
      left.native.application.candidates.lookup (focal, slot)) =
    fun slot => right.native.application.candidates.lookup (focal, slot)
  pool : left.native.pool = right.native.pool
  receipts : left.native.receipts = right.native.receipts
  focalHistory : left.principalHistory focal = right.principalHistory focal
  environmentHistory : left.environmentHistory = right.environmentHistory
  stagingCount_other : ∀ owner, owner ≠ focal → ∀ event,
    stagingCount (left.principalHistory owner) event =
      stagingCount (right.principalHistory owner) event
  submittedAt_other : ∀ owner, owner ≠ focal → ∀ event,
    submittedAt (left.principalHistory owner) event =
      submittedAt (right.principalHistory owner) event

namespace NativeReplay

/-- The component formulation above is exactly equality of the authenticated
application projection at the focal player. -/
theorem applicationPlayerView
    {runtime : EventGraphRuntime graph} {focal : Player}
    {left right : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right) :
    left.native.application.playerView focal =
      right.native.application.playerView focal := by
  unfold State.playerView
  congr 1
  · exact replay.publicView
  · exact replay.observation
  · exact replay.remembered
  · exact replay.candidates

/-- Native replay gives the actual policy input at the focal player, including
the observable pool and public receipt log. -/
theorem playerView
    {runtime : EventGraphRuntime graph} {focal : Player}
    {left right : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right) :
    MessageApplication.State.observe runtime.application left.native focal =
      MessageApplication.State.observe runtime.application right.native focal := by
  unfold MessageApplication.State.observe
  congr 1
  · exact congrArg (fun pool => pool.observe focal) replay.pool
  · change left.native.application.playerView focal =
      right.native.application.playerView focal
    exact replay.applicationPlayerView
  · exact replay.receipts

/-- The public environment observation follows from the focal public
application view together with equality of the complete transport state. -/
theorem environmentView
    {runtime : EventGraphRuntime graph} {focal : Player}
    {left right : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right) :
    MessageApplication.State.environmentView runtime.application left.native =
      MessageApplication.State.environmentView runtime.application right.native := by
  unfold MessageApplication.State.environmentView
  rw [replay.pool, replay.receipts]
  exact congrArg (fun view => MessageInterface.EnvironmentObservation.mk
    right.native.pool view right.native.receipts) replay.publicView

/-- Applying the same supported focal command on both sides preserves native
replay.  The recorded history entry contains the pre-command view, which is
equal by the incoming invariant even for replay and wait commands. -/
theorem playerStep
    (runtime : EventGraphRuntime graph) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (command : runtime.application.PlayerCommand)
    (leftSupported : leftNext ∈
      (runtime.application.playerStep focal left command).support)
    (rightSupported : rightNext ∈
      (runtime.application.playerStep focal right command).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have beforeView := replay.playerView
  have leftHistory := runtime.application.playerStep_history_self focal left command
    leftNext leftSupported
  have rightHistory := runtime.application.playerStep_history_self focal right command
    rightNext rightSupported
  have focalHistory : leftNext.principalHistory focal =
      rightNext.principalHistory focal := by
    rw [leftHistory, rightHistory, replay.focalHistory, beforeView]
  have environmentHistory : leftNext.environmentHistory =
      rightNext.environmentHistory := by
    rw [runtime.application.playerStep_environmentHistory focal left command leftNext
        leftSupported,
      runtime.application.playerStep_environmentHistory focal right command rightNext
        rightSupported]
    exact replay.environmentHistory
  have stagingCount_other : ∀ owner, owner ≠ focal → ∀ event,
      stagingCount (leftNext.principalHistory owner) event =
        stagingCount (rightNext.principalHistory owner) event := by
    intro owner different event
    rw [runtime.application.playerStep_other_history focal owner different left command
        leftNext leftSupported,
      runtime.application.playerStep_other_history focal owner different right command
        rightNext rightSupported]
    exact replay.stagingCount_other owner different event
  have submittedAt_other : ∀ owner, owner ≠ focal → ∀ event,
      submittedAt (leftNext.principalHistory owner) event =
        submittedAt (rightNext.principalHistory owner) event := by
    intro owner different event
    rw [runtime.application.playerStep_other_history focal owner different left command
        leftNext leftSupported,
      runtime.application.playerStep_other_history focal owner different right command
        rightNext rightSupported]
    exact replay.submittedAt_other owner different event
  cases command with
  | privateCommand privateCommand =>
      rw [runtime.application.playerStep_private_eq, FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftNext
      subst rightNext
      have applicationView := privateStep_focal_playerView_congr
        left.native.application right.native.application focal privateCommand
        replay.publicView replay.observation replay.remembered replay.candidates
      refine
        { publicView := congrArg PlayerView.publicView applicationView
          observation := ?_
          remembered := congrArg PlayerView.remembered applicationView
          candidates := congrArg PlayerView.candidates applicationView
          pool := replay.pool
          receipts := replay.receipts
          focalHistory
          environmentHistory
          stagingCount_other
          submittedAt_other }
      change graph.playerObserve focal
          (privateStep left.native.application focal privateCommand).config =
        graph.playerObserve focal
          (privateStep right.native.application focal privateCommand).config
      cases privateCommand with
      | prepare serial raw => exact replay.observation
      | remember event action =>
          by_cases owned : graph.actor? event = some focal
          · simp only [privateStep, dif_pos owned]
            split <;> split <;> exact replay.observation
          · simp only [privateStep, dif_neg owned]
            exact replay.observation
  | submit payload =>
      rw [runtime.application.playerStep_submit_eq, FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftNext
      subst rightNext
      refine
        { publicView := replay.publicView
          observation := replay.observation
          remembered := replay.remembered
          candidates := replay.candidates
          pool := ?_
          receipts := replay.receipts
          focalHistory
          environmentHistory
          stagingCount_other
          submittedAt_other }
      simp only [MessageApplication.afterSubmit]
      rw [replay.pool]
  | replay id =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at leftSupported rightSupported
      subst leftNext
      subst rightNext
      refine
        { publicView := replay.publicView
          observation := replay.observation
          remembered := replay.remembered
          candidates := replay.candidates
          pool := ?_
          receipts := replay.receipts
          focalHistory
          environmentHistory
          stagingCount_other
          submittedAt_other }
      simp only
      rw [replay.pool]
  | wait =>
      rw [runtime.application.playerStep_wait, FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftNext
      subst rightNext
      exact
        { publicView := replay.publicView
          observation := replay.observation
          remembered := replay.remembered
          candidates := replay.candidates
          pool := replay.pool
          receipts := replay.receipts
          focalHistory
          environmentHistory
          stagingCount_other
          submittedAt_other }

/-- The command shapes that a prescribed nonfocal policy may pair across two
replays.  Its private data may select different commands, but both commands
must consume the same event-local staging opportunities.  Public submission
must be byte-for-byte the same. -/
inductive PrescribedCommandPair (runtime : EventGraphRuntime graph) :
    runtime.application.PlayerCommand → runtime.application.PlayerCommand → Prop where
  | wait : PrescribedCommandPair runtime .wait .wait
  | privateCommand (left right : PrivateCommand graph)
      (stages : ∀ event,
        stagesEvent (runtime := runtime) event (.privateCommand left) =
          stagesEvent (runtime := runtime) event (.privateCommand right)) :
      PrescribedCommandPair runtime (.privateCommand left) (.privateCommand right)
  | submit (payload : Payload graph) :
      PrescribedCommandPair runtime (.submit payload) (.submit payload)

/-- Paired prescribed-command shapes preserve replay when invoked by a
nonfocal owner.  Different private commands are allowed because their entire
authenticated effect is hidden from `focal`; only their per-event history
cursor contribution must coincide. -/
theorem nonfocalPlayerStep
    (runtime : EventGraphRuntime graph) (focal owner : Player)
    (different : owner ≠ focal)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    {leftCommand rightCommand : runtime.application.PlayerCommand}
    (paired : PrescribedCommandPair runtime leftCommand rightCommand)
    (leftSupported : leftNext ∈
      (runtime.application.playerStep owner left leftCommand).support)
    (rightSupported : rightNext ∈
      (runtime.application.playerStep owner right rightCommand).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have environmentHistory : leftNext.environmentHistory =
      rightNext.environmentHistory := by
    rw [runtime.application.playerStep_environmentHistory owner left leftCommand leftNext
        leftSupported,
      runtime.application.playerStep_environmentHistory owner right rightCommand rightNext
        rightSupported]
    exact replay.environmentHistory
  have focalHistory : leftNext.principalHistory focal =
      rightNext.principalHistory focal := by
    rw [runtime.application.playerStep_other_history owner focal (Ne.symm different) left
        leftCommand leftNext leftSupported,
      runtime.application.playerStep_other_history owner focal (Ne.symm different) right
        rightCommand rightNext rightSupported]
    exact replay.focalHistory
  have leftHistorySelf := runtime.application.playerStep_history_self owner left
    leftCommand leftNext leftSupported
  have rightHistorySelf := runtime.application.playerStep_history_self owner right
    rightCommand rightNext rightSupported
  have leftHistoryOther : ∀ query, query ≠ owner →
      leftNext.principalHistory query = left.principalHistory query := by
    intro query queryOwner
    exact runtime.application.playerStep_other_history owner query queryOwner left
      leftCommand leftNext leftSupported
  have rightHistoryOther : ∀ query, query ≠ owner →
      rightNext.principalHistory query = right.principalHistory query := by
    intro query queryOwner
    exact runtime.application.playerStep_other_history owner query queryOwner right
      rightCommand rightNext rightSupported
  cases paired with
  | wait =>
      rw [runtime.application.playerStep_wait, FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftNext
      subst rightNext
      refine
        { publicView := replay.publicView
          observation := replay.observation
          remembered := replay.remembered
          candidates := replay.candidates
          pool := replay.pool
          receipts := replay.receipts
          focalHistory
          environmentHistory
          stagingCount_other := ?_
          submittedAt_other := ?_ }
      · intro query queryFocal event
        by_cases queryOwner : query = owner
        · subst query
          simp only [if_pos]
          simpa [stagingCount, stagesEvent] using
            replay.stagingCount_other owner different event
        · simp only [if_neg queryOwner]
          exact replay.stagingCount_other query queryFocal event
      · intro query queryFocal event
        by_cases queryOwner : query = owner
        · subst query
          simp only [if_pos]
          simpa [submittedAt] using replay.submittedAt_other owner different event
        · simp only [if_neg queryOwner]
          exact replay.submittedAt_other query queryFocal event
  | privateCommand leftPrivate rightPrivate stages =>
      rw [runtime.application.playerStep_private_eq, FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftNext
      subst rightNext
      have applicationView :
          (privateStep left.native.application owner leftPrivate).playerView focal =
            (privateStep right.native.application owner rightPrivate).playerView focal :=
        (privateStep_other_playerView left.native.application owner focal
          (Ne.symm different) leftPrivate).trans
          (replay.applicationPlayerView.trans
            (privateStep_other_playerView right.native.application owner focal
              (Ne.symm different) rightPrivate).symm)
      refine
        { publicView := congrArg PlayerView.publicView applicationView
          observation := ?_
          remembered := congrArg PlayerView.remembered applicationView
          candidates := congrArg PlayerView.candidates applicationView
          pool := replay.pool
          receipts := replay.receipts
          focalHistory
          environmentHistory
          stagingCount_other := ?_
          submittedAt_other := ?_ }
      · change graph.playerObserve focal
          (privateStep left.native.application owner leftPrivate).config =
        graph.playerObserve focal
          (privateStep right.native.application owner rightPrivate).config
        rw [privateStep_config, privateStep_config]
        exact replay.observation
      · intro query queryFocal event
        by_cases queryOwner : query = owner
        · subst query
          rw [leftHistorySelf, rightHistorySelf]
          rw [stagingCount_append, stagingCount_append,
            replay.stagingCount_other owner different event, stages event]
        · rw [leftHistoryOther query queryOwner, rightHistoryOther query queryOwner]
          exact replay.stagingCount_other query queryFocal event
      · intro query queryFocal event
        by_cases queryOwner : query = owner
        · subst query
          rw [leftHistorySelf, rightHistorySelf]
          simpa [submittedAt] using replay.submittedAt_other owner different event
        · rw [leftHistoryOther query queryOwner, rightHistoryOther query queryOwner]
          exact replay.submittedAt_other query queryFocal event
  | submit payload =>
      rw [runtime.application.playerStep_submit_eq, FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftNext
      subst rightNext
      refine
        { publicView := replay.publicView
          observation := replay.observation
          remembered := replay.remembered
          candidates := replay.candidates
          pool := ?_
          receipts := replay.receipts
          focalHistory
          environmentHistory
          stagingCount_other := ?_
          submittedAt_other := ?_ }
      · simp only [MessageApplication.afterSubmit]
        rw [replay.pool]
      · intro query queryFocal event
        by_cases queryOwner : query = owner
        · subst query
          simp only [MessageApplication.afterSubmit, if_pos]
          simpa [stagingCount, stagesEvent] using
            replay.stagingCount_other owner different event
        · simp only [MessageApplication.afterSubmit, if_neg queryOwner]
          exact replay.stagingCount_other query queryFocal event
      · intro query queryFocal event
        by_cases queryOwner : query = owner
        · subst query
          simp only [MessageApplication.afterSubmit, if_pos]
          rw [submittedAt_append_submit, submittedAt_append_submit,
            replay.submittedAt_other owner different event]
        · simp only [MessageApplication.afterSubmit, if_neg queryOwner]
          exact replay.submittedAt_other query queryFocal event

/-- One actual invocation of a prescribed nonfocal policy preserves native
replay.  At resolution submission the theorem asks only for equality of the
two locally computed packets; the reason for that equality belongs to the
endpoint/protection argument that calls this local replay law. -/
theorem prescribedPlayer_afterInvoke
    (runtime : EventGraphRuntime graph) (focal owner : Player)
    (different : owner ≠ focal) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftCoherent : PolicyCoherentAll runtime left owner)
    (rightCoherent : PolicyCoherentAll runtime right owner)
    (event : graph.EventId)
    (grant : left.native.application.serviceGrant = some event)
    (compiled : players owner = runtime.compilePlayerPolicy owner policy)
    (resolutionPayloadEq : ∀ (payload : L.Ty)
      (binding : FieldRef graph.layout (.binding owner payload))
      (checks : List (DeferredCheck graph.layout payload))
      (outputEq : graph.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
        (graph.nodes event) = .resolve owner payload binding checks)
      (_viewNode : nodeView graph event =
        .resolve owner payload binding checks outputEq codeEq)
      (_actor : graph.actor? event = some owner)
      (_leftReady : left.native.application.config.cut.Ready event)
      (_rightReady : right.native.application.config.cut.Ready event)
      (leftAction rightAction : graph.Action event),
      left.native.application.remembered event = some leftAction →
      right.native.application.remembered event = some rightAction →
      runtime.resolutionPayload owner event payload binding checks outputEq leftAction
          (MessageApplication.State.observe runtime.application left.native owner) =
        runtime.resolutionPayload owner event payload binding checks outputEq rightAction
          (MessageApplication.State.observe runtime.application right.native owner))
    (leftSupported : leftNext ∈ (runtime.application.invoke players environment left
      (.player owner)).support)
    (rightSupported : rightNext ∈ (runtime.application.invoke players environment right
      (.player owner)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  simp only [MessageApplication.invoke, compiled, FinDist.support_bind, Set.mem_iUnion]
    at leftSupported rightSupported
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftSupported
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightSupported
  let leftView := MessageApplication.State.observe runtime.application left.native owner
  let rightView := MessageApplication.State.observe runtime.application right.native owner
  have leftGrant : leftView.application.publicView.serviceGrant = some event := by
    change left.native.application.serviceGrant = some event
    exact grant
  have rightGrant : rightView.application.publicView.serviceGrant = some event := by
    change right.native.application.serviceGrant = some event
    exact (congrArg PublicView.serviceGrant replay.publicView).symm.trans grant
  have leftOwner : leftView.application.who = owner := by
    change owner = owner
    rfl
  have rightOwner : rightView.application.who = owner := by
    change owner = owner
    rfl
  have submittedEq : submittedAt (left.principalHistory owner) event =
      submittedAt (right.principalHistory owner) event :=
    replay.submittedAt_other owner different event
  have stageEq : stagingCount (left.principalHistory owner) event =
      stagingCount (right.principalHistory owner) event :=
    replay.stagingCount_other owner different event
  have readyEq : leftView.application.publicView.EventReady event ↔
      rightView.application.publicView.EventReady event := by
    change left.native.application.publicView.EventReady event ↔
      right.native.application.publicView.EventReady event
    rw [replay.publicView]
  have paired : PrescribedCommandPair runtime leftCommand rightCommand := by
    by_cases submitted : submittedAt (left.principalHistory owner) event = true
    · have rightSubmitted : submittedAt (right.principalHistory owner) event = true := by
        rw [← submittedEq]
        exact submitted
      have leftLaw : runtime.compilePlayerPolicy owner policy
          (left.principalHistory owner) leftView = FinDist.pure .wait := by
        unfold compilePlayerPolicy
        rw [leftGrant]
        simp [submitted]
      have rightLaw : runtime.compilePlayerPolicy owner policy
          (right.principalHistory owner) rightView = FinDist.pure .wait := by
        unfold compilePlayerPolicy
        rw [rightGrant]
        simp [rightSubmitted]
      rw [leftLaw, FinDist.mem_support_pure] at leftChosen
      rw [rightLaw, FinDist.mem_support_pure] at rightChosen
      subst leftCommand
      subst rightCommand
      exact .wait
    · have leftNotSubmitted : submittedAt (left.principalHistory owner) event = false :=
        Bool.eq_false_of_not_eq_true submitted
      have rightNotSubmitted : submittedAt (right.principalHistory owner) event = false := by
        rw [← submittedEq]
        exact leftNotSubmitted
      by_cases ready : leftView.application.publicView.EventReady event
      · have rightReady : rightView.application.publicView.EventReady event := readyEq.mp ready
        by_cases actor : graph.actor? event = some owner
        · cases viewNode : nodeView graph event with
          | sample payload law outputEq codeEq =>
              have leftLaw : runtime.compilePlayerPolicy owner policy
                  (left.principalHistory owner) leftView = FinDist.pure .wait := by
                unfold compilePlayerPolicy
                rw [leftGrant]
                simp [leftNotSubmitted, leftOwner, ready, actor, viewNode]
              have rightLaw : runtime.compilePlayerPolicy owner policy
                  (right.principalHistory owner) rightView = FinDist.pure .wait := by
                unfold compilePlayerPolicy
                rw [rightGrant]
                simp [rightNotSubmitted, rightOwner, rightReady, actor, viewNode]
              rw [leftLaw, FinDist.mem_support_pure] at leftChosen
              rw [rightLaw, FinDist.mem_support_pure] at rightChosen
              subst leftCommand
              subst rightCommand
              exact .wait
          | bind eventOwner payload outputEq codeEq =>
              cases countEq : stagingCount (left.principalHistory owner) event with
              | zero =>
                  have rightCount : stagingCount (right.principalHistory owner) event = 0 := by
                    rw [← stageEq]
                    exact countEq
                  have leftLaw := runtime.compilePlayerPolicy_bind_stage_zero owner policy
                    (left.principalHistory owner) leftView event eventOwner payload outputEq
                    codeEq viewNode leftGrant leftNotSubmitted leftOwner ready actor countEq
                  have rightLaw := runtime.compilePlayerPolicy_bind_stage_zero owner policy
                    (right.principalHistory owner) rightView event eventOwner payload outputEq
                    codeEq viewNode rightGrant rightNotSubmitted rightOwner rightReady actor
                    rightCount
                  rw [leftLaw, FinDist.support_map] at leftChosen
                  rw [rightLaw, FinDist.support_map] at rightChosen
                  obtain ⟨leftAction, _, rfl⟩ := leftChosen
                  obtain ⟨rightAction, _, rfl⟩ := rightChosen
                  exact .privateCommand _ _ (by intro query; simp [stagesEvent])
              | succ count =>
                  cases count with
                  | zero =>
                      have rightCount :
                          stagingCount (right.principalHistory owner) event = 1 := by
                        rw [← stageEq]
                        exact countEq
                      obtain ⟨leftAction, leftCached⟩ :=
                        (leftCoherent event actor).cached_of_stage (by omega)
                      obtain ⟨rightAction, rightCached⟩ :=
                        (rightCoherent event actor).cached_of_stage (by omega)
                      have leftRemembered : leftView.application.remembered event =
                          some leftAction := by
                        change (if graph.actor? event = some owner then
                          left.native.application.remembered event else none) = some leftAction
                        simp [actor, leftCached]
                      have rightRemembered : rightView.application.remembered event =
                          some rightAction := by
                        change (if graph.actor? event = some owner then
                          right.native.application.remembered event else none) = some rightAction
                        simp [actor, rightCached]
                      have leftLaw := runtime.compilePlayerPolicy_bind_stage_one owner policy
                        (left.principalHistory owner) leftView event eventOwner payload outputEq
                        codeEq viewNode leftAction leftGrant leftNotSubmitted leftOwner ready
                        actor countEq leftRemembered
                      have rightLaw := runtime.compilePlayerPolicy_bind_stage_one owner policy
                        (right.principalHistory owner) rightView event eventOwner payload outputEq
                        codeEq viewNode rightAction rightGrant rightNotSubmitted rightOwner
                        rightReady actor rightCount rightRemembered
                      rw [leftLaw, FinDist.mem_support_pure] at leftChosen
                      rw [rightLaw, FinDist.mem_support_pure] at rightChosen
                      subst leftCommand
                      subst rightCommand
                      obtain ⟨leftPrivate, leftPrivateEq⟩ :=
                        runtime.bindingStageCommand_is_private event payload outputEq leftAction
                      obtain ⟨rightPrivate, rightPrivateEq⟩ :=
                        runtime.bindingStageCommand_is_private event payload outputEq rightAction
                      rw [leftPrivateEq, rightPrivateEq]
                      have leftStages : stagesEvent event
                          (.privateCommand leftPrivate : Command runtime) = true := by
                        rw [← leftPrivateEq]
                        exact stagesEvent_bindingStageCommand runtime event eventOwner payload
                          outputEq leftAction
                      have rightStages : stagesEvent event
                          (.privateCommand rightPrivate : Command runtime) = true := by
                        rw [← rightPrivateEq]
                        exact stagesEvent_bindingStageCommand runtime event eventOwner payload
                          outputEq rightAction
                      exact .privateCommand leftPrivate rightPrivate (by
                        intro query
                        by_cases same : query = event
                        · subst query
                          rw [leftStages, rightStages]
                        · rw [runtime.stagesEvent_other_of_stagesEvent event query _ same
                              leftStages,
                            runtime.stagesEvent_other_of_stagesEvent event query _ same
                              rightStages])
                  | succ extra =>
                      have leftStage : 2 ≤ stagingCount (left.principalHistory owner) event := by
                        omega
                      have rightStage : 2 ≤ stagingCount (right.principalHistory owner) event := by
                        rw [← stageEq]
                        exact leftStage
                      have leftLaw := runtime.compilePlayerPolicy_bind_stage_two owner policy
                        (left.principalHistory owner) leftView event eventOwner payload outputEq
                        codeEq viewNode leftGrant leftNotSubmitted leftOwner ready actor leftStage
                      have rightLaw := runtime.compilePlayerPolicy_bind_stage_two owner policy
                        (right.principalHistory owner) rightView event eventOwner payload outputEq
                        codeEq viewNode rightGrant rightNotSubmitted rightOwner rightReady actor
                        rightStage
                      rw [leftLaw, FinDist.mem_support_pure] at leftChosen
                      rw [rightLaw, FinDist.mem_support_pure] at rightChosen
                      subst leftCommand
                      subst rightCommand
                      exact .submit _
          | resolve eventOwner payload binding checks outputEq codeEq =>
              have eventOwnerEq : eventOwner = owner := by
                apply Option.some.inj
                calc
                  some eventOwner = EventCode.actor
                      (cast (congrArg (EventCode graph.layout) outputEq)
                        (graph.nodes event)) := by rw [codeEq]; rfl
                  _ = EventCode.actor (graph.nodes event) :=
                    EventCode.actor_cast outputEq (graph.nodes event)
                  _ = some owner := actor
              subst eventOwner
              cases countEq : stagingCount (left.principalHistory owner) event with
              | zero =>
                  have rightCount : stagingCount (right.principalHistory owner) event = 0 := by
                    rw [← stageEq]
                    exact countEq
                  have leftLaw := runtime.compilePlayerPolicy_resolve_stage_zero owner policy
                    (left.principalHistory owner) leftView event owner payload binding checks
                    outputEq codeEq viewNode leftGrant leftNotSubmitted leftOwner ready actor
                    countEq
                  have rightLaw := runtime.compilePlayerPolicy_resolve_stage_zero owner policy
                    (right.principalHistory owner) rightView event owner payload binding checks
                    outputEq codeEq viewNode rightGrant rightNotSubmitted rightOwner rightReady
                    actor rightCount
                  rw [leftLaw, FinDist.support_map] at leftChosen
                  rw [rightLaw, FinDist.support_map] at rightChosen
                  obtain ⟨leftAction, _, rfl⟩ := leftChosen
                  obtain ⟨rightAction, _, rfl⟩ := rightChosen
                  exact .privateCommand _ _ (by intro query; simp [stagesEvent])
              | succ count =>
                  cases count with
                  | zero =>
                      have rightCount :
                          stagingCount (right.principalHistory owner) event = 1 := by
                        rw [← stageEq]
                        exact countEq
                      obtain ⟨leftAction, leftCached⟩ :=
                        (leftCoherent event actor).cached_of_stage (by omega)
                      obtain ⟨rightAction, rightCached⟩ :=
                        (rightCoherent event actor).cached_of_stage (by omega)
                      have leftRemembered : leftView.application.remembered event =
                          some leftAction := by
                        change (if graph.actor? event = some owner then
                          left.native.application.remembered event else none) = some leftAction
                        simp [actor, leftCached]
                      have rightRemembered : rightView.application.remembered event =
                          some rightAction := by
                        change (if graph.actor? event = some owner then
                          right.native.application.remembered event else none) = some rightAction
                        simp [actor, rightCached]
                      have leftLaw := runtime.compilePlayerPolicy_resolve_stage_one owner policy
                        (left.principalHistory owner) leftView event owner payload binding
                        checks outputEq codeEq viewNode leftAction leftGrant leftNotSubmitted
                        leftOwner ready actor countEq leftRemembered
                      have rightLaw := runtime.compilePlayerPolicy_resolve_stage_one owner policy
                        (right.principalHistory owner) rightView event owner payload binding
                        checks outputEq codeEq viewNode rightAction rightGrant rightNotSubmitted
                        rightOwner rightReady actor rightCount rightRemembered
                      rw [leftLaw, FinDist.mem_support_pure] at leftChosen
                      rw [rightLaw, FinDist.mem_support_pure] at rightChosen
                      subst leftCommand
                      subst rightCommand
                      exact .privateCommand _ _ (by intro query; simp [stagesEvent])
                  | succ extra =>
                      have leftStage : 2 ≤ stagingCount (left.principalHistory owner) event := by
                        omega
                      have rightStage : 2 ≤ stagingCount (right.principalHistory owner) event := by
                        rw [← stageEq]
                        exact leftStage
                      obtain ⟨leftAction, leftCached⟩ :=
                        (leftCoherent event actor).cached_of_stage (by omega)
                      obtain ⟨rightAction, rightCached⟩ :=
                        (rightCoherent event actor).cached_of_stage (by omega)
                      have leftRemembered : leftView.application.remembered event =
                          some leftAction := by
                        change (if graph.actor? event = some owner then
                          left.native.application.remembered event else none) = some leftAction
                        simp [actor, leftCached]
                      have rightRemembered : rightView.application.remembered event =
                          some rightAction := by
                        change (if graph.actor? event = some owner then
                          right.native.application.remembered event else none) = some rightAction
                        simp [actor, rightCached]
                      have leftLaw := runtime.compilePlayerPolicy_resolve_stage_two owner policy
                        (left.principalHistory owner) leftView event owner payload binding
                        checks outputEq codeEq viewNode leftAction leftGrant leftNotSubmitted
                        leftOwner ready actor leftStage leftRemembered
                      have rightLaw := runtime.compilePlayerPolicy_resolve_stage_two owner policy
                        (right.principalHistory owner) rightView event owner payload binding
                        checks outputEq codeEq viewNode rightAction rightGrant rightNotSubmitted
                        rightOwner rightReady actor rightStage rightRemembered
                      rw [leftLaw, FinDist.mem_support_pure] at leftChosen
                      rw [rightLaw, FinDist.mem_support_pure] at rightChosen
                      have packetEq := resolutionPayloadEq payload binding checks outputEq codeEq
                        viewNode actor
                        ((State.publicView_eventReady left.native.application event).mp ready)
                        ((State.publicView_eventReady right.native.application event).mp rightReady)
                        leftAction rightAction leftCached rightCached
                      simp only [resolutionSubmission] at leftChosen rightChosen
                      subst leftCommand
                      subst rightCommand
                      rw [packetEq]
                      exact .submit _
        · have leftLaw : runtime.compilePlayerPolicy owner policy
              (left.principalHistory owner) leftView = FinDist.pure .wait := by
            unfold compilePlayerPolicy
            rw [leftGrant]
            simp [leftNotSubmitted, leftOwner, ready, actor]
          have rightLaw : runtime.compilePlayerPolicy owner policy
              (right.principalHistory owner) rightView = FinDist.pure .wait := by
            unfold compilePlayerPolicy
            rw [rightGrant]
            simp [rightNotSubmitted, rightOwner, rightReady, actor]
          rw [leftLaw, FinDist.mem_support_pure] at leftChosen
          rw [rightLaw, FinDist.mem_support_pure] at rightChosen
          subst leftCommand
          subst rightCommand
          exact .wait
      · have rightReady : ¬rightView.application.publicView.EventReady event :=
          fun rightReady => ready (readyEq.mpr rightReady)
        have leftLaw : runtime.compilePlayerPolicy owner policy
            (left.principalHistory owner) leftView = FinDist.pure .wait := by
          unfold compilePlayerPolicy
          rw [leftGrant]
          simp [leftNotSubmitted, leftOwner, ready]
        have rightLaw : runtime.compilePlayerPolicy owner policy
            (right.principalHistory owner) rightView = FinDist.pure .wait := by
          unfold compilePlayerPolicy
          rw [rightGrant]
          simp [rightNotSubmitted, rightOwner, rightReady]
        rw [leftLaw, FinDist.mem_support_pure] at leftChosen
        rw [rightLaw, FinDist.mem_support_pure] at rightChosen
        subst leftCommand
        subst rightCommand
        exact .wait
  exact replay.nonfocalPlayerStep runtime focal owner different paired leftStep rightStep

/-- One invocation of a fixed pure focal policy selects the same command from
the equal authenticated input and therefore preserves native replay. -/
theorem purePlayer_afterInvoke
    (runtime : EventGraphRuntime graph) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (response : List runtime.application.PlayerEntry →
      runtime.application.View → runtime.application.PlayerCommand)
    (fixed : players focal = fun history view => FinDist.pure (response history view))
    (leftSupported : leftNext ∈ (runtime.application.invoke players environment left
      (.player focal)).support)
    (rightSupported : rightNext ∈ (runtime.application.invoke players environment right
      (.player focal)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    at leftSupported rightSupported
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftSupported
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightSupported
  rw [fixed, FinDist.mem_support_pure] at leftChosen rightChosen
  have inputEq :
      (left.principalHistory focal,
        MessageApplication.State.observe runtime.application left.native focal) =
      (right.principalHistory focal,
        MessageApplication.State.observe runtime.application right.native focal) :=
    Prod.ext replay.focalHistory replay.playerView
  have commandEq : response (left.principalHistory focal)
      (MessageApplication.State.observe runtime.application left.native focal) =
      response (right.principalHistory focal)
        (MessageApplication.State.observe runtime.application right.native focal) :=
    congrArg (fun input => response input.1 input.2) inputEq
  subst leftCommand
  subst rightCommand
  rw [commandEq] at leftStep
  exact replay.playerStep runtime focal _ leftStep rightStep

end NativeReplay

end Vegas.EventGraphRuntime
