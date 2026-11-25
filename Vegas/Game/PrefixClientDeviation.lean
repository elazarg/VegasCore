module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.PrefixDeviation.Binding
public import Vegas.Game.PrefixDeviation.Chance
public import Vegas.Game.PrefixDeviation.Publication
public import Vegas.Game.SourceServiceFactorization

@[expose] public section

/-! # Native deviations of prescribed source-prefix clients -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem exists_binding_interval {graph : Vegas.EventGraph Player L}
    (start : graph.EventId) (privateOutput : ¬ (graph.outputLayout start).IsPublic) :
    ∃ finish, start.val < finish ∧ finish ≤ graph.order.eventCount ∧
      (∀ event : graph.EventId, start.val ≤ event.val → event.val < finish →
        ∃ owner payload, graph.outputLayout event = .binding owner payload) ∧
      ∀ event : graph.EventId, event.val = finish → (graph.outputLayout event).IsPublic := by
  classical
  let Ending := fun finish : Nat => start.val < finish ∧ (graph.order.eventCount ≤ finish ∨
      ∃ event : graph.EventId, event.val = finish ∧ (graph.outputLayout event).IsPublic)
  have existsEnd : ∃ finish, Ending finish := ⟨graph.order.eventCount, start.isLt, Or.inl le_rfl⟩
  obtain ⟨finish, ⟨after, ending⟩, minimal⟩ : ∃ finish, Ending finish ∧
      ∀ smaller < finish, ¬ Ending smaller :=
    ⟨Nat.find existsEnd, Nat.find_spec existsEnd, fun _ below => Nat.find_min existsEnd below⟩
  have inside (smaller : Nat) (below : smaller < finish) (beyond : start.val < smaller) :
      smaller < graph.order.eventCount ∧ ∀ event : graph.EventId, event.val = smaller →
        ¬ (graph.outputLayout event).IsPublic := by
    have notEnd := minimal smaller below
    simp only [Ending, not_and, not_or, not_exists, not_le] at notEnd
    obtain ⟨small, everyPrivate⟩ := notEnd beyond
    exact ⟨small, fun event same => by simpa using everyPrivate event same⟩
  have bounded : finish ≤ graph.order.eventCount := by
    rcases ending with large | ⟨event, same, _⟩
    · by_contra above
      push Not at above
      obtain ⟨small, _⟩ := inside graph.order.eventCount above start.isLt
      omega
    · have := event.isLt
      omega
  refine ⟨finish, after, bounded, ?_, ?_⟩
  · intro event lower upper
    have hidden : ¬ (graph.outputLayout event).IsPublic := by
      rcases Nat.lt_or_ge start.val event.val with beyond | atStart
      · exact (inside event.val upper beyond).2 event rfl
      · have same : event = start := Fin.ext (le_antisymm atStart lower)
        rwa [same]
    cases actor : graph.actor? event with
    | none => exact (hidden (EventCode.output_public_of_actor_none (graph.nodes event) actor)).elim
    | some owner =>
        obtain ⟨payload, binding⟩ :=
          (EventCode.output_public_or_binding_of_actor (graph.nodes event) owner actor).resolve_left
            hidden
        exact ⟨owner, payload, binding⟩
  · intro event same
    rcases ending with large | ⟨other, otherSame, publicOutput⟩
    · exact (Nat.not_lt.mpr large (same ▸ event.isLt)).elim
    · have equal : event = other := Fin.ext (same.trans otherSame.symm)
      rwa [equal]

end Vegas

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nativeSourceContinuation_of_private_blocks [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wellFormed : setup.WellFormed)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy) :
    let whole := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
      target
    let reference := setup.informationGraph.submitProfile (compileEventProfile setup.program whole)
    let nativePayoff := fun final : (serviceApplication setup deps duration leaks).Execution =>
      setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (Setup.leastUtility utility) focal
    (∀ start finish {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole start point),
      start < finish → finish ≤ (serviceGraph setup deps).order.eventCount →
      (∀ event : (serviceGraph setup deps).EventId, start ≤ event.val → event.val < finish →
        ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload) →
      (∀ event : (serviceGraph setup deps).EventId, event.val = finish →
        ((serviceGraph setup deps).outputLayout event).IsPublic) →
      (∀ {tailPoint : setup.informationGraph.Config}
        (tail : SourceResidual setup whole finish tailPoint),
        nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
          reference focal deviation nativePayoff sourcePayoff tail) →
      nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff start finish frame) →
    ∀ {rank : Nat} {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole rank point),
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff frame := by
  classical
  intro whole reference nativePayoff sourcePayoff privateBlocks
  let G := serviceGraph setup deps
  let Compare := fun {rank : Nat} {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole rank point) =>
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
      reference focal deviation nativePayoff sourcePayoff frame
  suffices proof : ∀ gap rank (point : setup.informationGraph.Config)
      (frame : SourceResidual setup whole rank point), G.order.eventCount - rank = gap →
      Compare frame by
    intro rank point frame
    exact proof _ rank point frame rfl
  intro gap
  induction gap using Nat.strong_induction_on with
  | ind gap ih =>
    intro rank point frame gapEq
    have bounded : rank ≤ G.order.eventCount := frame.checkpoint.ordered.1
    have tailOf (finish : Nat) (later : rank < finish) (within : finish ≤ G.order.eventCount)
        {tailPoint : setup.informationGraph.Config} (tail : SourceResidual setup whole finish
          tailPoint) : Compare tail :=
      ih (G.order.eventCount - finish) (by omega) finish tailPoint tail rfl
    by_cases ended : eventCount frame.program = 0
    · exact nativeSourceContinuation_terminal setup deps duration leaks horizon scheduler bound
        turns
        whole reference focal deviation parameter utility forfeit spread frame ended
    have active : rank < G.order.eventCount := by
      have countEq := frame.aligned.graphSuffix.countEq
      change rank + eventCount frame.program = G.order.eventCount at countEq
      omega
    rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
      aligned, admitted, authentic, supports, disclosure, lift, commutes, steps, injective,
      transport, checkpoint⟩
    cases program with
    | ret payoffs =>
        exact (ended rfl).elim
    | @sample Γ names name payload fresh distribution next =>
        let frame : SourceResidual setup whole rank point :=
          ⟨Γ, names, .sample name fresh distribution next, residualProfile, source, refs, embedding,
            refsBefore, aligned, admitted, authentic, supports, disclosure, lift, commutes,
            steps, injective, transport, checkpoint⟩
        exact nativeSourceContinuation_sample setup deps duration leaks horizon scheduler bound
          turns wellFormed relaxed contract intended target agrees reference focal deviation
          nativePayoff sourcePayoff frame fresh distribution next rfl
          (tailOf (rank + 1) (by omega) (by omega) _)
    | @commit Γ names name owner payload fresh guard next =>
        let frame : SourceResidual setup whole rank point :=
          ⟨Γ, names, .commit name owner fresh guard next, residualProfile, source, refs, embedding,
            refsBefore, aligned, admitted, authentic, supports, disclosure, lift, commutes,
            steps, injective, transport, checkpoint⟩
        let index : Fin (eventCount (.commit name owner fresh guard next)) :=
          ⟨0, by simp [eventCount]⟩
        let event := embedding.event index
        have atRank : event.val = rank := by
          simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
        have binding : G.outputLayout event = .binding owner payload :=
          (embedding.layout_eq index).trans rfl
        have privateOutput : ¬ (G.outputLayout event).IsPublic := by
          rw [binding]
          exact False.elim
        obtain ⟨finish, later, within, bindings, barrier⟩ :=
          exists_binding_interval (graph := G) event privateOutput
        rw [atRank] at later bindings
        apply nativeSourceContinuation_of_binding_interval setup deps duration leaks horizon
          scheduler bound turns whole reference focal deviation nativePayoff sourcePayoff rank
          finish frame relaxed wellFormed later.le within bindings barrier
        exact privateBlocks rank finish frame later within bindings barrier
          (tailOf finish later within)
    | @reveal Γ names published owner name payload fresh selected unresolved next =>
        let frame : SourceResidual setup whole rank point :=
          ⟨Γ, names, .reveal published owner name fresh selected unresolved next, residualProfile,
            source, refs, embedding, refsBefore, aligned, admitted, authentic, supports, disclosure,
            lift, commutes, steps, injective, transport, checkpoint⟩
        let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next))
            :=
          ⟨0, by simp [eventCount]⟩
        let event := embedding.event index
        have atRank : event.val = rank := by
          simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
        have publication : (G.outputLayout event).IsPublication := by
          have output : G.outputLayout event = .publication payload :=
            (embedding.layout_eq index).trans rfl
          rw [output]
          trivial
        obtain ⟨finish, run⟩ := exists_revealRun publication
        rw [atRank] at run
        exact nativeSourceContinuation_public scheduler bound relaxed contract timely wellFormed
          intended target agrees submits disclosing parameter utility spread focal deviation frame
          run
          (tailOf finish run.nonempty run.bounded)

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nativeSourceContinuation_initialized
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile)
    (submitted : (serviceGraph setup deps).SubmitsBindings reference) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    (continuation : ∀ initial : State L setup.context,
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
        wholeProfile reference focal deviation nativePayoff sourcePayoff
          (SourceResidual.initial setup wholeProfile initial)) :
    let players := Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening
          ((serviceGraph setup deps).prefixProfile reference))) focal deviation
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect ((serviceApplication setup deps duration leaks).roundsFrom
        (serviceInitialDistribution setup deps) scheduler players horizon) nativePayoff ≤
      expect (setup.initialDistribution.bind fun initial => setup.informationGraph.runPolicies
        setup.informationGraph.canonicalScheduler
        (Function.update (setup.informationGraph.prefixProfile reference) focal policy)
          (setup.eventInputs initial)) sourcePayoff := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening
        ((serviceGraph setup deps).prefixProfile reference))) focal deviation
  let ghost := fun initial : State L setup.context =>
    EventGraph.Config.initial (graph := setup.informationGraph) (setup.eventInputs initial)
  let execution := fun initial : State L setup.context => ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (graph := serviceGraph setup deps) (setup.eventInputs initial))
  let representative := setup.initialDistribution.support_nonempty.choose
  let frame := SourceResidual.initial setup wholeProfile representative
  obtain ⟨noise, initialFactor⟩ := source_initial_traffic_factorization setup
    (deps := deps) (duration := duration) leaks focal
  let augment := fun point : Config Player L setup.context ×
      MessageNetwork Player app.Payload × List (MessageId Player × Bool) ×
      List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps) =>
    ((point.1, ghost point.1.state), point.2)
  have factor : setup.initialDistribution.map (fun initial =>
      ((Config.initial initial, ghost initial),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution initial))) =
      (setup.initialDistribution.map (fun initial => (Config.initial initial, ghost initial))).bind
        fun hidden => (noise (hidden.1.view focal)).map fun observed => (hidden, observed) := by
    have tagged := congrArg (PMF.map augment) initialFactor
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def, augment,
      SourceProgram.Config.initial, ghost, execution] using tagged
  have boundary (initial : State L setup.context) (supported : initial ∈
    setup.initialDistribution.support) :
      CompletionBoundary setup leaks scheduler players 0 (execution initial) := by
    refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
    · change execution initial ∈ (app.roundsFrom (serviceInitialDistribution setup deps) scheduler
        players 0).support
      unfold ReactiveApplication.roundsFrom
      simp only [ReactiveApplication.runRounds, serviceInitialDistribution]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨_,
        (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, supported, rfl⟩,
        (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    · intro event _ owner entry member
      cases member
  have intendedHistory (initial : State L setup.context)
      (supported : initial ∈ setup.initialDistribution.support) :
      ∃ history : setup.intendedProtocol.History,
        history.state = some (ProtocolState.entry setup.program (Config.initial initial)) := by
    have legal : setup.intendedProtocol.Legal setup.intendedProtocol.initHistory.state
        (fun _ => none) := setup.intendedProtocol.legal_of_legalOption
          (fun impossible => impossible) (fun _ impossible => impossible)
    have reached : some (ProtocolState.entry setup.program (Config.initial initial)) ∈
        (setup.intendedProtocol.step setup.intendedProtocol.initHistory.state ⟨_, legal⟩).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, supported, rfl⟩
    exact ⟨setup.intendedProtocol.initHistory.extend legal reached, rfl⟩
  have initialContinuation := continuation representative
  obtain ⟨policy, comparison⟩ := initialContinuation
    (ContextRefs.initial_coversPrefix setup.program) setup.initialDistribution Config.initial ghost
    (fun _ _ => rfl) (fun _ _ => rfl) (fun initial _ => SourceCheckpoint.initial setup initial)
    (fun initial _ => ⟨setup.eventInputs initial, .initial⟩) intendedHistory
    (fun _ => reference) (fun _ _ => submitted) (fun _ _ _ _ _ _ _ _ => rfl)
    execution boundary (fun _ _ => Nat.zero_le _) (fun _ _ => rfl) noise factor
  refine ⟨policy, ?_⟩
  have countEq : setup.informationGraph.order.eventCount = eventCount setup.program := rfl
  simpa only [countEq, Function.comp_def, ReactiveApplication.roundsFrom,
    serviceInitialDistribution,
    PMF.bind_map,
    ReactiveApplication.runToHorizon, ReactiveApplication.Execution.initial, List.length_nil,
    Nat.sub_zero, EventGraph.runPolicies, EventGraph.run, execution, ghost, app, frame,
    SourceResidual.initial] using comparison

end Vegas

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every raw native unilateral deviation is bounded by one policy in the canonical
information graph. Initial source correlation and the complete physical observation history
are retained by the comparison; no independent-prior or scheduler-erasure premise is needed. -/
theorem native_prefix_deviation_bound [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wellFormed : setup.WellFormed)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy) :
    let whole := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
      target
    let reference := setup.informationGraph.submitProfile (compileEventProfile setup.program whole)
    let nativePayoff := fun final : (serviceApplication setup deps duration leaks).Execution =>
      setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (Setup.leastUtility utility) focal
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect ((serviceApplication setup deps duration leaks).roundsFrom
        (serviceInitialDistribution setup deps) scheduler
        (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
          (firstTurnTiming setup turns deps) (effectiveOpening
            ((serviceGraph setup deps).prefixProfile reference))) focal deviation) horizon)
        nativePayoff ≤
      expect ((setup.graphInputs setup.informationDependencies).bind
        (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler
          (Function.update (setup.informationGraph.prefixProfile reference) focal policy)))
        sourcePayoff := by
  intro whole reference nativePayoff sourcePayoff
  have continuation : ∀ {rank : Nat} {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole rank point),
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff frame :=
    nativeSourceContinuation_of_private_blocks setup deps duration leaks horizon scheduler bound
      turns wellFormed relaxed contract timely intended target agrees submits disclosing parameter
      utility forfeit spread focal deviation (by
        intro start finish point frame later bounded bindings barrier outer
        exact nativeBindingContinuation_binding_interval setup deps duration leaks horizon scheduler
          bound turns wellFormed relaxed contract timely intended target agrees submits parameter
          utility forfeit spread focal deviation start finish later bounded bindings barrier outer
          frame)
  obtain ⟨policy, comparison⟩ := nativeSourceContinuation_initialized setup deps duration leaks
    horizon scheduler bound turns whole reference
    (submitsBindings_submitProfile (serviceGraph setup deps) _) focal deviation nativePayoff
    sourcePayoff (fun initial => continuation (SourceResidual.initial setup whole initial))
  refine ⟨policy, ?_⟩
  simpa only [Setup.graphInputs, PMF.bind_map, Function.comp_def] using comparison

end Vegas
