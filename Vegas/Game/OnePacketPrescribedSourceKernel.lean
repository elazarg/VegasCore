module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/
public import Vegas.Game.OnePacketStoppedSourceLaw
public import Vegas.Game.SourceServiceContinuation
public import Vegas.Game.OnePacketIntendedProjection
public import Vegas.EventGraph.OwnedStep
public import Vegas.Game.OnePacketCompletion
public import Vegas.Game.OnePacketSourceTurn
public import Vegas.Game.OnePacketRetention
public import Vegas.Game.RevealServiceCalendarState
public import Vegas.Game.SourceServiceFirstTurnMixture
public import Vegas.Game.IntendedOpeningContinuation
public import Vegas.EventGraph.ResolutionProvenance
public import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
public import Interaction.ReactiveOwnPlay
public import Interaction.ReactiveLocalContinuation

@[expose] public section
/-! # Source continuation kernels of prescribed packets

A transmitting canonical packet at a genuine first callback is a supported owned
graph action. Counted native service and the compiler suffix correspondence identify
the entire terminal source continuation after the actual completion stop. Binding
and disclosure share the same typed acceptance and ordinary graph continuation laws.
-/

noncomputable section
namespace Vegas
open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "N" => ReactiveApplication.ResponseMenu.information menu (initialLaw setup)
  horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup)
  horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

/-- A canonical action followed by the compiled source continuation has the
full terminal source law at every counted completion stop. Authentic failed
publication retains its actual action and public default history. -/
theorem counted_canonical_source_continuation
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (source : BehavioralProfile setup.program)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup timeouts leaks).Execution}
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    (clear : execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.logs who, ¬ ActivatedAt setup timeouts leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup timeouts leaks).Submission)
    (submits : ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who) event action).transmission =
        some material)
    {rank : Nat} (residual : SourceResidual setup source rank execution.application.config)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : (E).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup timeouts leaks) who
        ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who) event action)⟩) :
    let plan := (graph setup).policyPlan (compileEventProfile setup.program source)
      (graph setup).canonicalScheduler
    let read := fun final : (graph setup).Config => decodeConfig? setup.program setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) [] (outputEmbedding setup.program)
      final.store final.history
    (((N).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).bind fun history => match history.state with
        | none => PMF.pure none
        | some final => ((graph setup).runPlan plan final.execution.application.config.remaining
            final.execution.application.config).map read) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).bind fun target =>
          (ProtocolState.continuationLaw setup.program source target).map some := by
  let response := (canonicalServiceDecision timeouts) leaks who (execution.logs who)
    (execution.observe (application setup timeouts leaks) who) event action
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have active : who ∉ execution.application.config.defaulted := by
    rw [clear]
    exact Finset.notMem_empty _
  have fits := firstActivation_inclusionFits_of_counted_opportunity setup timeouts leaks bounds
    horizon scheduler delay bound opportunity timely trace rfl clear event turn never
  have rawTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler trace
  have fresh := canonical_freshCall rawTrace bound who event turn fits action material submits
  have afterTrace := current ▸ start.trace
  obtain ⟨output, invariant⟩ := acceptanceInvariant_respond (timeouts := timeouts) bounds horizon
    scheduler trace event turn action material submits afterTrace
  have sameConfig := ((reactive_respond_application timeouts) leaks execution who response).1
  have supported := AcceptanceWitness.complete_mem_step invariant.2.2.2.2.1 sameConfig
    ready who owned active
  let after := execution.application.config.complete event ready action output
  obtain ⟨successor, _stepped, mass⟩ := residual.step_mass event ready action after supported
  have pointEq := Option.some.inj (residual.decode.symm.trans decoded)
  rw [pointEq] at mass
  obtain ⟨next, pureEq⟩ := execution.application.config.step_eq_pure_of_actor event ready action
    who owned
  have afterEq : after = next := (PMF.mem_support_pure_iff _ _).mp (pureEq ▸ supported)
  have one : (ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action))
      (successor.lift (ProtocolState.entry successor.program successor.source)) = 1 := by
    simpa only [pureEq, afterEq, PMF.pure_apply_self] using mass
  have sourcePure : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) =
      PMF.pure (successor.lift (ProtocolState.entry successor.program successor.source)) :=
    pmf_eq_pure_of_support_subset_singleton _ _ ((PMF.apply_eq_one_iff _ _).mp one).le
  have responseClear :
    (execution.respond (application setup timeouts leaks) who response).application.config.defaulted
        = ∅ := by rw [sameConfig, clear]
  have stopped := counted_accepted_stop_continuation (timeouts := timeouts) inclusion completes
    (compileEventProfile setup.program source) certificate players start current responseClear
    invariant sameConfig owned (by
      simpa only [respondEntry, submits, Option.map_some, sentEnvelope] using fresh)
  dsimp only
  rw [sourcePure, PMF.pure_bind]
  calc
    _ = (((N).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).bind fun _ => sourceContinuation setup source (rank + 1) after) := by
        apply bind_congr_on_support _
        intro history member
        obtain ⟨final, foundReady, state, _done, _actual, _config, law⟩ := stopped history member
        rw [state]
        dsimp only
        rw [law]
        exact successor.runPlan_readout_law
    _ = sourceContinuation setup source (rank + 1) after := PMF.bind_const _ _
    _ = _ := by
      change (setup.continuationLaw source (sourceServicePrefix? setup (rank + 1) after)).map
        some = _
      rw [successor.decode]
      rfl

/-- A transmitting action whose source successors are intended has exactly the
single source-step law at its first completion stop. Public defaults cannot
introduce an automatic tail because the certified completion remains clear. -/
theorem counted_canonical_intended_sourceLaw
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (source : BehavioralProfile setup.program)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup timeouts leaks).Execution}
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    (clear : execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.logs who, ¬ ActivatedAt setup timeouts leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup timeouts leaks).Submission)
    (submits : ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who) event action).transmission =
        some material)
    {rank : Nat} (residual : SourceResidual setup source rank execution.application.config)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (preserves : ∀ target ∈ (ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action)).support,
      ProtocolState.Intended setup.program target)
    (start : (E).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup timeouts leaks) who
        ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who) event action)⟩) :
    ((N).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).map (fun history => nativeDecodedState setup timeouts leaks history.state) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  let response := (canonicalServiceDecision timeouts) leaks who (execution.logs who)
    (execution.observe (application setup timeouts leaks) who) event action
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have active : who ∉ execution.application.config.defaulted := by
    rw [clear]
    exact Finset.notMem_empty _
  have fits := firstActivation_inclusionFits_of_counted_opportunity setup timeouts leaks bounds
    horizon scheduler delay bound opportunity timely trace rfl clear event turn never
  have rawTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler trace
  have fresh := canonical_freshCall rawTrace bound who event turn fits action material submits
  obtain ⟨output, invariant⟩ := acceptanceInvariant_respond (timeouts := timeouts) bounds horizon
    scheduler trace event turn action material submits (current ▸ start.trace)
  have sameConfig := ((reactive_respond_application timeouts) leaks execution who response).1
  have supported := AcceptanceWitness.complete_mem_step invariant.2.2.2.2.1 sameConfig
    ready who owned active
  let after := execution.application.config.complete event ready action output
  obtain ⟨successor, _stepped, mass⟩ := residual.step_mass event ready action after supported
  have pointEq := Option.some.inj (residual.decode.symm.trans decoded)
  rw [pointEq] at mass
  obtain ⟨next, pureEq⟩ := execution.application.config.step_eq_pure_of_actor event ready action
    who owned
  have afterEq : after = next := (PMF.mem_support_pure_iff _ _).mp (pureEq ▸ supported)
  have one : (ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action))
      (successor.lift (ProtocolState.entry successor.program successor.source)) = 1 := by
    simpa only [pureEq, afterEq, PMF.pure_apply_self] using mass
  have sourcePure : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) =
      PMF.pure (successor.lift (ProtocolState.entry successor.program successor.source)) :=
    pmf_eq_pure_of_support_subset_singleton _ _ ((PMF.apply_eq_one_iff _ _).mp one).le
  have nextIntended := preserves _ (by
    rw [sourcePure]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have afterDecoded : decodedPoint setup after =
      some (successor.lift (ProtocolState.entry successor.program successor.source)) :=
    decodedPoint_eq successor
  have afterClear := defaulted_eq_empty_of_decodedIntended afterDecoded nextIntended
  have responseClear : (execution.respond (application setup timeouts leaks) who
      response).application.config.defaulted = ∅ := by rw [sameConfig, clear]
  have stopped := counted_accepted_stop_continuation (timeouts := timeouts) inclusion completes
    (compileEventProfile setup.program source) certificate players start current responseClear
    invariant sameConfig owned (by
      simpa only [respondEntry, submits, Option.map_some, sentEnvelope] using fresh)
  rw [sourcePure, PMF.pure_map]
  apply pmf_eq_pure_of_support_subset_singleton
  rw [PMF.support_map]
  rintro _ ⟨history, member, rfl⟩
  obtain ⟨final, foundReady, state, _done, _actual, exactConfig, _law⟩ := stopped history member
  change nativeDecodedState setup timeouts leaks history.state =
    some (successor.lift (ProtocolState.entry successor.program successor.source))
  rw [state]
  change decodedPoint setup final.execution.application.config = _
  rw [exactConfig (Or.inl afterClear)]
  exact afterDecoded

omit [Fintype Player] in
private theorem clear_step_effective {before after : (graph setup).Config}
    {event : (graph setup).EventId} (ready : before.cut.Ready event)
    (action : (graph setup).Action event)
    (supported : after ∈ (before.step event ready action).support)
    (clear : after.defaulted = ∅) : EffectiveAction before event action := by
  unfold EffectiveAction
  cases node : nodeView (graph setup) event with
  | sample | bind => trivial
  | resolve owner payload binding checks outputEq codeEq =>
      intro _disclose
      have active : owner ∉ before.defaulted := by
        intro inactive
        have kept := before.defaulted_step event ready action after supported inactive
        rw [clear] at kept
        exact Finset.notMem_empty owner kept
      obtain ⟨output, member, rfl⟩ := PMF.support_map .. ▸ supported
      have defaults := before.complete_defaults_of_code event ready outputEq
        (.resolve owner payload binding checks) codeEq
        (cast (congrArg EventGraph.EventField.Action outputEq) action)
        (cast (congrArg EventGraph.EventField.Value outputEq) output)
      simp only [cast_cast, cast_eq] at defaults
      have succeeds : ∃ value,
          cast (congrArg EventGraph.EventField.Value outputEq) output =
            PublicationResult.success value := by
        cases valueEq : cast (congrArg EventGraph.EventField.Value outputEq) output with
        | success value => exact ⟨value, rfl⟩
        | failure =>
            have present : owner ∈ (before.complete event ready action output).defaulted := by
              change owner ∈ (before.complete event ready action output).defaults.defaulted
              rw [defaults, valueEq]
              simp only [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
                ite_eq_right active, Option.bind_some, EventGraph.EventCode.defaultEvent,
                EventGraph.EventCode.causesDefault, PublicationResult.isFailure,
                ite_true, DefaultHistory.defaulted_record_some, Finset.mem_insert_self]
            rw [clear] at present
            exact (Finset.notMem_empty owner present).elim
      obtain ⟨value, succeeds⟩ := succeeds
      have outputSupported : before.complete event ready action output ∈
          (before.step event ready action).support := by
        rw [EventGraph.Config.step, PMF.support_map]
        exact ⟨output, member, rfl⟩
      have resolved := EventGraph.Config.resolution_step_output event owner payload binding
        checks outputEq codeEq before (before.complete event ready action output) ready action
        outputSupported
      have resolvedSuccess : EventGraph.EventCode.resolveOutput? binding checks
          (cast (congrArg EventGraph.EventField.Action outputEq) action) before.store =
            some (.success value) := by
        rw [ite_eq_right active, EventGraph.Config.complete_output_same] at resolved
        have castSome : ∀ {α β : Type} (same : α = β) (value : α),
            cast (congrArg Option same) (some value) = some (cast same value) := by
          intro α β same value
          cases same
          rfl
        rw [castSome (congrArg EventGraph.EventField.Value outputEq) output, succeeds] at resolved
        exact resolved
      exact ⟨value, EventGraph.EventCode.binding_success_of_resolve_success binding checks
        _ before.store value resolvedSuccess⟩

/-- The honest law installed at an intended first callback has exactly the
source behavioral successor law at the native completion stop. -/
theorem counted_firstActivation_honest_sourceLaw
    [infoDecidable : ∀ player, DecidableEq ((N).InfoState player)]
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup timeouts leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup timeouts leaks who (some (execution.logs who,
      execution.observe (application setup timeouts leaks) who)) = some event)
    (never : ∀ entry ∈ execution.logs who, ¬ ActivatedAt setup timeouts leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info) :
    ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info
          (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler source who
            info)))
      (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) history).map
        (fun stop => nativeDecodedState setup timeouts leaks stop.state) =
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point).map some := by
  classical
  have infoEq : (N).infoOf who history.trace =
      some (execution.logs who, execution.observe (application setup timeouts leaks) who) := by
    refine ((menu).info (initialLaw setup) horizon scheduler who history.trace).trans ?_
    rw [current]
    simp only [ReactiveApplication.observe, ite_true]
  have atSite := observed.symm.trans infoEq
  subst atSite
  have trace : (E).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have turn := (pendingEvent_spec (timeouts := timeouts) pending).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have active : who ∉ execution.application.config.defaulted := by
    rw [clear]
    exact Finset.notMem_empty _
  have atRank := (ready_iff_rank setup _ rank ordered event).mp ready
  let profile := setup.intendedOpeningProfile source.strategy
  obtain ⟨found, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) profile menu
    horizon scheduler trace _ rfl
  have rankEq := residual.checkpoint.ordered.unique ordered
  subst found
  have pointEq := Option.some.inj (residual.decode.symm.trans decoded)
  have decodedHere : decodedPoint setup execution.application.config = some point := by
    rw [decodedPoint_eq residual, pointEq]
  have mixture := asIfHonest_bind_step_eq_behavioralStateStep (timeouts := timeouts) source who
    execution ordered decoded intendedPoint turn active (execution.logs who)
  have fits := firstActivation_inclusionFits_of_counted_opportunity setup timeouts leaks bounds
    horizon scheduler delay bound opportunity timely trace rfl clear event turn never
  have retains : RetainsCoveredCanonical setup timeouts leaks bounds horizon scheduler bound :=
    retainsCoveredCanonical_of_adequate (timeouts := timeouts) bounds covers capacity horizon
      scheduler bound
  have stopEq : (fun stop : (E).History =>
      LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state) =
      (fun stop => (∃ final, stop.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear stop.state) := by
    funext stop
    apply propext
    refine or_congr ?_ Iff.rfl
    constructor
    · rintro ⟨final, state, query, completed, queryRank⟩
      have same : query = event := Fin.ext (queryRank.trans atRank.symm)
      exact ⟨final, state, same ▸ completed⟩
    · rintro ⟨final, state, completed⟩
      exact ⟨final, state, event, completed, atRank⟩
  have going : ¬ (LateStopped setup timeouts leaks bounds horizon scheduler rank history ∨
      ¬ Clear history.state) := by
    rw [congrFun stopEq history]
    rintro (⟨final, state, completed⟩ | failed)
    · cases Option.some.inj (current.symm.trans state)
      exact ready.1 completed
    · exact failed (by rw [current]; exact clear)
  have running : ¬ (E).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have acting : (E).active history.state who := by rw [current]; rfl
  have actsOnce :=
    ((menu).decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  rw [← mixture, (N).runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce players who
    (players who) _ _ _ history observed going running acting, PMF.map_bind]
  change ((honestResponse setup timeouts leaks source who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who)).map
        (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
          (some (execution.logs who,
            execution.observe (application setup timeouts leaks) who)))).bind _ = _
  unfold honestResponse
  rw [turn]
  dsimp only
  rw [PMF.bind_map, PMF.bind_map, PMF.map_bind]
  refine bind_congr_on_support _ fun choice supported => ?_
  have encodes := asIfHonestProfile_encodes (timeouts := timeouts) source who execution rank
    ordered point decoded (execution.logs who) event turn active choice supported
  rcases choice with _ | action
  · simp at encodes
  cases encoded : encodeEventAction? setup.program event action with
  | none => simp [encoded] at encodes
  | some graphAction =>
      have decodeEq := decodeEventAction_encodeEventAction?_eq_some setup.program event action
        graphAction encoded
      have preserves : ∀ target ∈ (ProtocolState.step setup.program point
          (fun _ => decodeEventAction setup.program event graphAction)).support,
          ProtocolState.Intended setup.program target := by
        intro target reached
        rw [decodeEq] at reached
        have supportedStep : target ∈ (ProtocolState.behavioralStateStep setup.program profile
            point).support := by
          rw [← mixture]
          exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨some action, supported, reached⟩
        exact (setup.intendedOpening_step_closed source.strategy point target
          (decodedPoint_staticAt decodedHere) intendedPoint supportedStep).2
      obtain ⟨after, graphPure⟩ := execution.application.config.step_eq_pure_of_actor event ready
        graphAction who owned
      have graphSupport : after ∈
          (execution.application.config.step event ready graphAction).support := by
        rw [graphPure]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      obtain ⟨beforePoint, target, beforeDecoded, afterDecoded, stepped⟩ :=
        decodedPoint_step residual event ready graphAction after graphSupport
      cases Option.some.inj (decodedHere.symm.trans beforeDecoded)
      have afterClear := defaulted_eq_empty_of_decodedIntended afterDecoded (preserves target
        stepped)
      have effective := clear_step_effective ready graphAction graphSupport afterClear
      have success := asIfHonestProfile_success (timeouts := timeouts) source who execution rank
        ordered point decoded (execution.logs who) action supported
      have bindSuccess : ∀ owner payload outputEq codeEq,
          nodeView (graph setup) event = .bind owner payload outputEq codeEq →
            ∃ value, graphAction = cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (some (PublicationResult.success value)) := by
        intro owner payload outputEq _codeEq _node
        exact encodeEventAction?_commitsValue setup.program event action success.1 graphAction
          encoded owner payload outputEq
      have loud : ¬ SilentAction (setup := setup) (mode := .sequential) event graphAction := by
        cases node : nodeView (serviceGraph setup .sequential) event with
        | sample => simp only [SilentAction, node, not_false_eq_true]
        | bind owner payload outputEq codeEq =>
            obtain ⟨value, same⟩ := bindSuccess owner payload outputEq codeEq node
            simp only [SilentAction, node, same, cast_cast, cast_eq, reduceCtorEq,
              not_false_eq_true]
        | resolve owner payload binding checks outputEq codeEq =>
            have disclose := encodeEventAction?_discloses setup.program event action success.2
              graphAction encoded payload outputEq
            simp only [SilentAction, node, disclose, Bool.true_eq_false, not_false_eq_true]
      obtain ⟨material, submits⟩ :=
        canonicalServiceDecision_transmits_of_effective (setup := setup) timeouts _
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace) who event turn graphAction
        effective loud
      have bindingEffective : EffectiveDecision event graphAction := by
        unfold EffectiveDecision
        cases node : nodeView (graph setup) event with
        | bind owner payload outputEq codeEq =>
            obtain ⟨value, same⟩ := bindSuccess owner payload outputEq codeEq node
            exact ⟨value, same⟩
        | sample | resolve => trivial
      have offered := canonical_mem_onePacket_of_pending (timeouts := timeouts) bounds trace who
        event turn (pendingEvent_spec (timeouts := timeouts) pending).2.2.2 graphAction
        (retains trace who event graphAction turn (pendingEvent_spec (timeouts := timeouts)
          pending).2.2.2 fits bindingEffective (by rw [submits]; simp))
      have selected : (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler who (some (execution.logs who,
            execution.observe (application setup timeouts leaks) who))
          ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
            (execution.observe (application setup timeouts leaks) who) event graphAction)).1 =
          some ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
            (execution.observe (application setup timeouts leaks) who) event graphAction) := by
        simp only [responseChoice, dite_eq_left offered]
      have committed : ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) players who
            ((players who).commit (some (execution.logs who,
              execution.observe (application setup timeouts leaks) who))
              (responseChoice setup timeouts leaks bounds (initialLaw setup)
              horizon scheduler who (some (execution.logs who,
                execution.observe (application setup timeouts leaks) who))
                ((canonicalServiceDecision timeouts) leaks who
                (execution.logs who) (execution.observe (application setup timeouts leaks) who)
                  event graphAction))))
          (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
            ¬ Clear stop.state) history).map
            (fun stop => nativeDecodedState setup timeouts leaks stop.state) =
          (ProtocolState.step setup.program point
            (fun _ => decodeEventAction setup.program event graphAction)).map some := by
        revert selected
        rw [← infoEq]
        intro selected
        rw [(N).runBehavioralUntil_of_running certificate _ going running, PMF.map_bind]
        calc
          _ = ((N).runBehavioralFrom _ 1 history).bind (fun _ =>
              (ProtocolState.step setup.program point
                (fun _ => decodeEventAction setup.program event graphAction)).map some) := by
            apply bind_congr_on_support _
            intro next stepped
            have committedStep := (menu).run_commit_response (initialLaw setup) horizon scheduler
              players history who remaining execution current _ _ selected
            have commitDecidable : infoDecidable who =
                (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
            rw [← commitDecidable] at committedStep
            have nextState : next.state = some ⟨remaining, none, execution.respond
                (application setup timeouts leaks) who ((canonicalServiceDecision timeouts)
                  leaks who
                  (execution.logs who) (execution.observe (application setup timeouts leaks) who)
                    event graphAction)⟩ := by
              have inLaw : next.state ∈ (PMF.pure
                  (some ⟨remaining, none, execution.respond (application setup timeouts leaks) who
                    ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
                      (execution.observe (application setup timeouts leaks) who) event
                        graphAction)⟩)).support := by
                rw [← committedStep, PMF.support_map]
                exact ⟨next, stepped, rfl⟩
              exact (PMF.mem_support_pure_iff _ _).mp inLaw
            rw [stopEq]
            exact counted_canonical_intended_sourceLaw opportunity inclusion timely completes
              profile certificate _ trace clear event turn never graphAction material submits
              residual decoded preserves next nextState
          _ = _ := PMF.bind_const _ _
      simpa only [Function.comp_apply, Option.bind_some, encoded, decodeEq] using committed
end Vegas
