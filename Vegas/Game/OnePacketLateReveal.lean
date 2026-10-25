/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateBadMass
import Vegas.Game.ServiceRevealDecode
import Vegas.Game.ServiceWithheldForfeit

/-! # Completions of a late reveal

From a history at which the event of the site's rank is ready, the configuration
stays put until the event completes, so every stop of play until it completes is
one step of the event from the history's configuration
(`Vegas.lateStop_mem_step`). At a reveal, the step publishes the resolution of
the disclosure the action chooses, and a refusal publishes a failure
(`Vegas.resolve_step_output`). So disclosing completes the source reveal at its
unique intended successor, and every runtime completion reaches that successor
or records a failed publication (`Vegas.disclosure_sourceKernel`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [Fintype Player] in
/-- A configuration step of a reveal stores the resolution of the disclosure its
action chooses. -/
theorem resolve_step_output {config next : (graph setup).Config}
    {event : (graph setup).EventId} {ready : config.cut.Ready event}
    {action : (graph setup).Action event} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (member : next ∈ (config.step event ready action).support) :
    next.outputs event =
      (EventGraph.EventCode.resolveOutput? binding checks
        (cast (congrArg EventGraph.EventField.Action outputEq) action) next.store).map
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)) := by
  have reach : ConfigReaches setup config next :=
    Relation.ReflTransGen.single (Or.inr ⟨event, ready, action, member⟩)
  exact ConfigReaches.resolve_output reach (by
    rw [config.step_history event ready action next member]
    exact List.mem_append_right _ (List.mem_singleton_self _)) ready.1 (outputEq := outputEq)
    (codeEq := codeEq)

/-- **Every stop is one step of the event.** Under a scheduler completing play,
from a history whose configuration `sent` is a prefix of `rank` events with
`event` ready, every stop of play of any profile until the event completes is
one step of the event from `sent`. -/
theorem lateStop_mem_step
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {sent : (graph setup).Config} {rank : Nat} (ordered : sent.cut.IsPrefix rank)
    {event : (graph setup).EventId} (ready : sent.cut.Ready event)
    (terminalCompleted : ∀ (final : (application setup leaks).Control),
      ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (atSent : control.execution.application.config = sent) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start).support,
      ∃ final, stop.state = some final ∧
        ∃ action, final.execution.application.config ∈ (sent.step event ready action).support := by
  intro stop member
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let held := fun reachedState : (application setup leaks).ProtocolState =>
    ∃ reachedControl, reachedState = some reachedControl ∧
      (reachedControl.execution.application.config = sent ∨
        ∃ action, reachedControl.execution.application.config ∈
          (sent.step event ready action).support)
  have closed := model.runBehavioralUntil_support_closed certificate players
    (LateStopped setup leaks bounds horizon scheduler rank) held
    (fun history going _ joint legal target holds reached => by
      obtain ⟨before, beforeState, atBefore⟩ := holds
      have reached' : target ∈ ((application setup leaks).transition (initialLaw setup) horizon
          scheduler history.state joint).support := reached
      rw [beforeState] at reached'
      clear reached
      have reached := reached'
      obtain ⟨next, rfl, _⟩ := (application setup leaks).transition_recall_prefix
        (initialLaw setup) horizon scheduler before target joint reached
      refine ⟨next, rfl, ?_⟩
      rcases atBefore with same | ⟨action, inStep⟩
      · rcases transition_configStep (initialLaw setup) horizon scheduler before next joint
            reached with stays | ⟨completed, completedReady, action, inStep⟩
        · exact Or.inl (stays.trans same)
        · right
          revert completedReady inStep
          rw [same]
          intro completedReady inStep
          have eventEq : completed = event := ready_unique (setup := setup) _ completedReady ready
          subst eventEq
          exact ⟨action, inStep⟩
      · exact (going ⟨before, beforeState, isPrefix_succ_of_mem_step ordered ready inStep⟩).elim)
    start ⟨control, current, Or.inl atSent⟩ stop member
  have ends := model.mem_support_runBehavioralUntil certificate players _ start stop member
  obtain ⟨final, finalState, atFinal⟩ := closed
  refine ⟨final, finalState, ?_⟩
  rcases atFinal with same | stepped
  · exfalso
    rcases ends with ⟨other, otherState, prefixed⟩ | ended
    · rw [finalState] at otherState
      cases Option.some.inj otherState
      rw [same] at prefixed
      exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
    · rw [finalState] at ended
      exact ready.1 (by
        rw [← same]
        exact terminalCompleted final (finalState ▸ stop.trace) ended same)
  · exact stepped

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A publication failure read at its own type is a failure. -/
theorem isFailure_cast_publication_failure {kind : EventGraph.EventField Player L}
    {payload : L.Ty} (kindEq : kind = .publication payload) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  subst kindEq
  rfl

/-- Disclosing completes the source reveal at its unique intended successor; every
runtime completion reaches that successor or records a failed publication. -/
theorem disclosure_sourceKernel
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment) {who : Player}
    (site : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).Choice who site.1))
    (history : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (terminalCompleted : ∀ (final : (application setup leaks).Control),
      ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed) :
    let installed := Profile.update (sig := (onePacketModel setup leaks bounds
      (initialLaw setup) horizon scheduler).behavioralSignature) assessment.strategy who
      ((assessment.strategy who).withLaw site.1 law)
    let phase := (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralUntil ((bounds.onePacketMenu (runtime setup) leaks).bounded
        (initialLaw setup) horizon scheduler).wellFoundedHistories installed
        (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1
    ∃ target, ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point = PMF.pure target ∧
      ProtocolState.Intended setup.program target ∧
      ∀ stop ∈ phase.support, ∃ final, stop.state = some final ∧
        (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
            (siteFresh who site.1) stop = some target ∨
          (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
              (siteFresh who site.1) stop = none ∧
            StoreEventFailed final.execution.application.config.store event)) := by
  classical
  intro installed phase
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  let profile := setup.intendedOpeningProfile source.strategy
  let rank := siteRank site.1
  let stopped := LateStopped setup leaks bounds horizon scheduler rank
  let untilLaw := model.runBehavioralUntil certificate installed stopped history.1
  let fresh := siteFresh (setup := setup) (leaks := leaks) who site.1
  have freshIff : ∀ control, fresh control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [fresh, siteFresh, pending]
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  -- The disclosing action and the point it reaches.
  let disclose : (graph setup).Action event :=
    cast (congrArg EventGraph.EventField.Action outputEq.symm) true
  have owned : (graph setup).actor? event = some who := nodeView_resolve_actor outputEq codeEq
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => decodeEventAction setup.program event disclose) (acts who)
  -- Every as-if-honest choice at the reveal is the disclosing one.
  have honestDiscloses : ∀ choice ∈ (asIfHonestProfile setup leaks source who
      (some (execution.recall who, execution.observe (application setup leaks) who))).support,
      choice = decodeEventAction setup.program event disclose := by
    intro choice member
    have encodes := asIfHonestProfile_encodes source who execution rank ordered point decoded
      (execution.recall who) event turn choice member
    obtain ⟨action, encoded⟩ := Option.isSome_iff_exists.mp encodes
    cases choice with
    | none => cases encoded
    | some sourceAction =>
    have back := decodeEventAction_encodeEventAction?_eq_some setup.program event sourceAction
      action encoded
    obtain ⟨noFailure, noWithholding⟩ := asIfHonestProfile_success source who execution rank
      ordered point decoded (execution.recall who) sourceAction member
    generalize resultEq : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Bool) = result
    have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) result := by
      rw [← resultEq]
      simp only [cast_cast, cast_eq]
    cases result with
    | true => rw [← back, actionEq]
    | false =>
        exfalso
        have failing : Failing (decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)) :=
          decodeEventAction_failing_publication setup.program event.val event.isLt outputEq
        rw [← actionEq, back] at failing
        cases sourceAction with
        | commit sourceOwner name sourcePayload result =>
            have failed := failing.1 sourceOwner name sourcePayload result rfl
            subst failed
            exact noFailure sourceOwner name sourcePayload rfl
        | reveal sourceOwner name withheld =>
            have withheldEq : withheld = false := failing.2
            subst withheldEq
            exact noWithholding sourceOwner name rfl
  have stepLaw := asIfHonest_bind_step_eq_behavioralStateStep source who execution ordered
    decoded intendedPoint turn (execution.recall who)
  have stepPure : ProtocolState.behavioralStateStep setup.program profile point =
      PMF.pure target := by
    rw [← stepLaw, ← stepEq]
    have constant : (asIfHonestProfile setup leaks source who
        (some (execution.recall who, execution.observe (application setup leaks) who))).bind
          (fun choice => ProtocolState.step setup.program point (fun _ => choice)) =
        (asIfHonestProfile setup leaks source who
          (some (execution.recall who, execution.observe (application setup leaks) who))).bind
          (fun _ => ProtocolState.step setup.program point
            (fun _ => decodeEventAction setup.program event disclose)) :=
      bind_congr_on_support _ fun choice member => by rw [honestDiscloses choice member]
    rw [constant, PMF.bind_const]
  have targetIntended : ProtocolState.Intended setup.program target := by
    obtain ⟨choice, member⟩ := (asIfHonestProfile setup leaks source who
      (some (execution.recall who,
        execution.observe (application setup leaks) who))).support_nonempty
    obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup leaks source who
      execution rank ordered point decoded (execution.recall who) _).mp member
    have legal := intended.2
    change ProtocolView.intendedMenu who setup.program
      (ProtocolState.observe who setup.program point) intended.1 at legal
    rw [same, honestDiscloses choice member] at legal
    refine ProtocolState.intended_step_of_actors setup.program point
      (fun _ => decodeEventAction setup.program event disclose) target intendedPoint
      (fun player active => by
        cases (acts player).symm.trans active
        cases decodedEq : decodeEventAction setup.program event disclose with
        | none =>
            rw [decodedEq] at legal
            exact (legal (acts who)).elim
        | some action =>
            rw [decodedEq] at legal
            exact ⟨action, rfl, legal.2⟩)
      (by rw [stepEq]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  -- Every stop completes the reveal at the target, or fails.
  obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    menu horizon scheduler traceHere _ rfl
  have foundEq : found = rank := isPrefix_unique residualFound.checkpoint.ordered ordered
  have residual := foundEq ▸ residualFound
  have stops : ∀ stop ∈ untilLaw.support, ∃ final, stop.state = some final ∧
      (completionPoint setup leaks bounds horizon scheduler rank fresh stop = some target ∨
        (completionPoint setup leaks bounds horizon scheduler rank fresh stop = none ∧
          StoreEventFailed final.execution.application.config.store event)) := by
    intro stop member
    obtain ⟨final, finalState, action, inStep⟩ := lateStop_mem_step certificate
      installed ordered ready terminalCompleted history.1 current rfl stop member
    refine ⟨final, finalState, ?_⟩
    have done : event ∈ final.execution.application.config.cut.completed := by
      rw [execution.application.config.step_cut event ready action _ inStep]
      exact Finset.mem_insert_self _ _
    generalize resultEq : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Bool) = result
    have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) result := by
      rw [← resultEq]
      simp only [cast_cast, cast_eq]
    cases result with
    | true =>
        rw [actionEq] at inStep
        have pointEq := completionPoint_of_mem_step (fresh := fresh) residual decoded ready stepEq
          finalState inStep
        by_cases freshHere : fresh final
        · left
          rw [pointEq, ite_eq_left ⟨targetIntended, freshHere⟩ ..]
        · right
          exact ⟨by rw [pointEq, ite_eq_right (fun good => freshHere good.2) ..],
            not_not.mp ((not_congr (freshIff final)).mp freshHere)⟩
    | false =>
        right
        have output := resolve_step_output (outputEq := outputEq) (codeEq := codeEq) inStep
        rw [actionEq, cast_cast, cast_eq] at output
        obtain ⟨stored, storedEq⟩ := Option.isSome_iff_exists.mp
          ((final.execution.application.config.output_available event).mpr done)
        rw [storedEq] at output
        cases resolved : EventGraph.EventCode.resolveOutput? binding checks false
            final.execution.application.config.store with
        | none =>
            rw [resolved] at output
            cases output
        | some result =>
            rw [resolved] at output
            have failedResult := resolveOutput?_false binding checks _ resolved
            subst failedResult
            have failedHere : StoreEventFailed final.execution.application.config.store event :=
              ⟨stored, by rw [EventGraph.Config.store_output, storedEq], by
                rw [Option.map_some, Option.some.injEq] at output
                first | rw [← output] | rw [output]
                exact isFailure_cast_publication_failure outputEq⟩
            exact ⟨completionPoint_eq_none_of_not_fresh finalState fun freshHere =>
              (freshIff final).mp freshHere failedHere, failedHere⟩
  exact ⟨target, stepPure, targetIntended, stops⟩

end Vegas
