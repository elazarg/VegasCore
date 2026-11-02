/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccessFree
import Vegas.Game.OnePacketSourceTurn
import Vegas.Game.OnePacketDecodedActor
import Vegas.EventGraph.ResolutionProvenance

/-! # Completions of a late reveal

A native completion consists of the ready event's primary graph step followed
by automatic completion. When the source step reaches an intended target,
that target has no defaults, so the automatic tail is empty. Withholding instead
stores a public failure that persists through automatic completion. Thus every
late-reveal completion reaches the intended authentic-opening successor or
records a failed publication (`Vegas.disclosure_sourceKernel`).
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

omit [Fintype Player] in
private theorem withheld_primary_drain_failed
    {sent : (graph setup).Config} {event : (graph setup).EventId}
    (ready : sent.cut.Ready event) {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (primary : EventGraphRuntime.State (graph setup))
    (member : primary.config ∈ (sent.step event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)).support) :
    StoreEventFailed primary.drain.config.store event := by
  have resolved := EventGraph.Config.resolution_step_output event owner payload binding checks
    outputEq codeEq sent primary.config ready _ member
  simp only [cast_cast, cast_eq, ite_self] at resolved
  have available : ∀ field ∈ insert binding.field (EventGraph.GuardCheck.listReadFields checks),
      (sent.store field).isSome = true := by
    intro field present
    apply sent.read_available ready
    rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
    exact present
  rw [EventGraph.EventCode.resolveOutput?_false_eq_failure binding checks sent.store available]
    at resolved
  have done : event ∈ primary.config.cut.completed := by
    rw [sent.step_cut event ready _ _ member, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  obtain ⟨stored, storedEq⟩ := Option.isSome_iff_exists.mp
    ((primary.config.output_available event).mpr done)
  have storedPrimary : primary.config.store (.inr event) = some stored := by
    rw [EventGraph.Config.store_output, storedEq]
  have storedFinal := primary.drain_store_of_some (.inr event) stored storedPrimary
  apply storeEventFailed_of_ref _ event ⟨.inr event, outputEq⟩ rfl _ rfl
  simp only [EventGraph.FieldRef.get?]
  rw [storedFinal]
  rw [storedEq] at resolved
  exact resolved.symm

/-- Disclosing completes the source reveal at its unique intended successor; every
runtime completion reaches that successor or records a failed publication. -/
theorem disclosure_sourceKernel
    [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment) {who : Player}
    (site : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    {event : (graph setup).EventId}
    (pending : pendingEvent setup runtime leaks who site.1 = some event)
    (law : PMF ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who site.1))
    (history : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (runtime := runtime) site.1))
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (runtime := runtime) site.1)
      execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (terminalCompleted : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed) :
    let installed := Profile.update (sig := (onePacketModel setup runtime leaks bounds
      (initialLaw setup) horizon scheduler).behavioralSignature) assessment.strategy who
      ((assessment.strategy who).withLaw site.1 law)
    let phase := (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralUntil ((bounds.onePacketMenu runtime leaks).bounded
        (initialLaw setup) horizon scheduler).wellFoundedHistories installed
        (LateStopped setup runtime leaks bounds horizon scheduler (siteRank (runtime := runtime)
          site.1)) history.1
    ∃ target, ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point = PMF.pure target ∧
      ProtocolState.Intended setup.program target ∧
      ∀ stop ∈ phase.support, ∃ final, stop.state = some final ∧
        (completionPoint setup runtime leaks bounds horizon scheduler (siteRank (runtime :=
          runtime) site.1)
            (siteFresh (runtime := runtime) who site.1) stop = some target ∨
          (completionPoint setup runtime leaks bounds horizon scheduler (siteRank (runtime :=
            runtime) site.1)
              (siteFresh (runtime := runtime) who site.1) stop = none ∧
            StoreEventFailed final.execution.application.config.store event)) := by
  classical
  intro installed phase
  let menu := bounds.onePacketMenu runtime leaks
  let model := onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  let profile := setup.intendedOpeningProfile source.strategy
  let rank := siteRank (runtime := runtime) site.1
  let stopped := LateStopped setup runtime leaks bounds horizon scheduler rank
  let untilLaw := model.runBehavioralUntil certificate installed stopped history.1
  let fresh := siteFresh (runtime := runtime) (setup := setup) (leaks := leaks) who site.1
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
  have clear := defaulted_eq_empty_of_decodedIntended pointDecoded intendedPoint
  have active : who ∉ execution.application.config.defaulted := by
    rw [clear]
    exact Finset.notMem_empty who
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := by
    intro player
    rw [decodedPoint_actor player ready pointDecoded, owned]
    simp [active]
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => decodeEventAction setup.program event disclose) (acts who)
  -- Every as-if-honest choice at the reveal is the disclosing one.
  have honestDiscloses : ∀ choice ∈ (asIfHonestProfile setup runtime leaks source who
      (some (execution.logs who, execution.observe (application setup runtime leaks)
        who))).support,
      choice = decodeEventAction setup.program event disclose := by
    intro choice member
    have encodes := asIfHonestProfile_encodes (runtime := runtime) source who execution rank
      ordered point decoded
      (execution.logs who) event turn active choice member
    obtain ⟨action, encoded⟩ := Option.isSome_iff_exists.mp encodes
    cases choice with
    | none => cases encoded
    | some sourceAction =>
    have back := decodeEventAction_encodeEventAction?_eq_some setup.program event sourceAction
      action encoded
    obtain ⟨noFailure, noWithholding⟩ := asIfHonestProfile_success (runtime := runtime) source who
      execution rank
      ordered point decoded (execution.logs who) sourceAction member
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
            obtain ⟨value, valueEq⟩ := noFailure
            rw [valueEq] at failed
            cases failed
        | reveal sourceOwner name withheld =>
            have withheldEq : withheld = false := failing.2
            subst withheldEq
            exact noWithholding sourceOwner name rfl
  have stepLaw := asIfHonest_bind_step_eq_behavioralStateStep (runtime := runtime) source who
    execution ordered
    decoded intendedPoint turn active (execution.logs who)
  have stepPure : ProtocolState.behavioralStateStep setup.program profile point =
      PMF.pure target := by
    rw [← stepLaw, ← stepEq]
    have constant : (asIfHonestProfile setup runtime leaks source who
        (some (execution.logs who, execution.observe (application setup runtime leaks) who))).bind
          (fun choice => ProtocolState.step setup.program point (fun _ => choice)) =
        (asIfHonestProfile setup runtime leaks source who
          (some (execution.logs who, execution.observe (application setup runtime leaks)
            who))).bind
          (fun _ => ProtocolState.step setup.program point
            (fun _ => decodeEventAction setup.program event disclose)) :=
      bind_congr_on_support _ fun choice member => by rw [honestDiscloses choice member]
    rw [constant, PMF.bind_const]
  have targetIntended : ProtocolState.Intended setup.program target := by
    obtain ⟨choice, member⟩ := (asIfHonestProfile setup runtime leaks source who
      (some (execution.logs who,
        execution.observe (application setup runtime leaks) who))).support_nonempty
    obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup runtime leaks
      source who
      execution rank ordered point decoded (execution.logs who) _).mp member
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
  obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
    setup.program)
    menu horizon scheduler traceHere _ rfl
  have foundEq : found = rank :=
    EventOrder.Cut.IsPrefix.unique residualFound.checkpoint.ordered ordered
  have residual := foundEq ▸ residualFound
  have stops : ∀ stop ∈ untilLaw.support, ∃ final, stop.state = some final ∧
      (completionPoint setup runtime leaks bounds horizon scheduler rank fresh stop = some target ∨
        (completionPoint setup runtime leaks bounds horizon scheduler rank fresh stop = none ∧
          StoreEventFailed final.execution.application.config.store event)) := by
    intro stop member
    obtain ⟨final, finalState, action, primary, inStep, drained⟩ :=
      lateStop_primary_drain (runtime := runtime) certificate
      installed ordered ready terminalCompleted history.1 current rfl stop member
    refine ⟨final, finalState, ?_⟩
    generalize resultEq : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Bool) = result
    have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) result := by
      rw [← resultEq]
      simp only [cast_cast, cast_eq]
    cases result with
    | true =>
        rw [actionEq] at inStep
        have primaryClear := defaulted_eq_empty_of_intended_source_step residual decoded ready
          stepEq targetIntended primary inStep
        have actualStep : final.execution.application.config ∈
            (execution.application.config.step event ready disclose).support := by
          rw [drained, primary.drain_eq_of_empty primaryClear]
          exact inStep
        have pointEq := completionPoint_of_mem_step (runtime := runtime) (fresh := fresh) residual
          decoded ready stepEq
          finalState actualStep
        by_cases freshHere : fresh final
        · left
          rw [pointEq, ite_eq_left ⟨targetIntended, freshHere⟩ ..]
        · right
          exact ⟨by rw [pointEq, ite_eq_right (fun good => freshHere good.2) ..],
            not_not.mp ((not_congr (freshIff final)).mp freshHere)⟩
    | false =>
        right
        rw [actionEq] at inStep
        have failedHere : StoreEventFailed final.execution.application.config.store event := by
          rw [drained]
          exact withheld_primary_drain_failed ready (outputEq := outputEq) codeEq primary inStep
        exact ⟨completionPoint_eq_none_of_not_fresh (runtime := runtime) finalState
          (fun freshHere => (freshIff final).mp freshHere failedHere), failedHere⟩
  exact ⟨target, stepPure, targetIntended, stops⟩

end Vegas
