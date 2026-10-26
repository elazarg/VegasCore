/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalStoppedSample
import Vegas.Pending.PhaseServiceContract

/-! # Actual raw sampling windows under physical completion -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Any raw response stutters semantically during a pending chance phase. -/
theorem sourcePhase_sample_raw_control_harmonic
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (profile : ∀ who, ((PhaseCount.rawMenu runtime leaks bounds).information initial
      horizon scheduler).BehavioralPolicy who)
    (history : ((PhaseCount.rawMenu runtime leaks bounds).protocol initial horizon
      scheduler).History)
    (current : (phaseApplication runtime leaks).Control) (state : history.state = some current)
    (frontier : current.execution.application.Frontier)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : current.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .sample) (event : graph.EventId) (rank : event.val = phase.low)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (output : graph.outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode graph.layout) output) (graph.nodes event) =
      .sample payload law)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? current.execution.application.current.native.config.store = some draw) :
    let field : FieldRef graph.layout (.publicData payload) := ⟨.inr event, output⟩
    let potential : (phaseApplication runtime leaks).ProtocolState → PMF (Option (L.Val payload)) :=
      fun state => match state with
      | none => PMF.pure none
      | some control =>
          if control.execution.application.attempt = current.execution.application.attempt then
            draw.map some
          else PMF.pure (field.get? control.execution.application.current.native.config.store)
    (((PhaseCount.rawMenu runtime leaks bounds).information
      initial horizon scheduler).runBehavioralFrom profile 1 history).bind
        (fun after => potential after.state) =
        draw.map some := by
  classical
  intro field potential
  let app := phaseApplication runtime leaks
  let menu := (PhaseCount.rawMenu runtime leaks bounds)
  let model := menu.information initial horizon scheduler
  let policies := menu.decodeProfile initial horizon scheduler profile
  have environment (count : Nat) (command : app.Command) :
      (current.execution.environmentStep app command).bind (fun next =>
        potential (some ⟨count, command.actor? app, next⟩)) = draw.map some := by
    rcases phaseProposal_sample_environment_configuration runtime leaks current.execution phase
      remaining installed kind event rank ready payload law output code command with sample | stays
    · subst command
      exact (phaseProposal_sample_application_laws runtime leaks current.execution frontier
        phase remaining installed kind event rank ready payload law output code draw evaluates).2.1
    · calc
        _ = (current.execution.environmentStep app command).bind
            (fun _ => draw.map some) := by
          apply bind_congr_on_support
          intro next supported
          have observed : (next.application.current.native.config, next.application.attempt) ∈
              ((current.execution.environmentStep app command).map (fun after =>
                (after.application.current.native.config, after.application.attempt))).support :=
            (PMF.mem_support_map_iff _ _ _).mpr ⟨next, supported, rfl⟩
          rw [stays, PMF.mem_support_pure_iff] at observed
          have sameAttempt : next.application.attempt =
              current.execution.application.attempt := congrArg Prod.snd observed
          simp only [potential, sameAttempt, ite_true]
        _ = _ := PMF.bind_const _ _
  have response (count : Nat) (owner : Player) (action : app.Action) :
      potential (some ⟨count, none, current.execution.respond app owner action⟩) =
        draw.map some := by
    have sameAttempt : (current.execution.respond app owner action).application.attempt =
        current.execution.application.attempt := by
      rcases action with ⟨transmission⟩
      cases transmission <;> rfl
    simp only [potential, sameAttempt, ite_true]
  have evaluated := congrArg (fun distribution : PMF app.ProtocolState =>
      distribution.bind potential)
    (menu.run_map_controlSteps initial horizon scheduler profile 1 history)
  simp only [Function.iterate_one, PMF.pure_bind, PMF.bind_map] at evaluated
  change (model.runBehavioralFrom profile 1 history).bind (fun after => potential after.state) = _
  refine evaluated.trans ?_
  rw [state]
  rcases current with ⟨count, actor, execution⟩
  cases actor with
  | none =>
      cases count with
      | zero =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            Option.bind_some, ReactiveApplication.transition, PMF.pure_bind, potential, ite_true]
      | succ count =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            Option.bind_some, ReactiveApplication.transition, PMF.bind_bind, PMF.bind_map]
          exact (bind_congr_on_support _ (fun command _ => environment count command)).trans
            (PMF.bind_const _ _)
  | some owner =>
      simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
        ReactiveApplication.transition, ↓reduceIte, Option.getD_some, PMF.bind_bind,
        PMF.pure_bind]
      calc
        _ = (policies owner (execution.recall owner) (execution.observe app owner)).bind
          (fun _ => draw.map some) := by
          apply bind_congr_on_support
          intro action _supported
          exact response count owner action
        _ = _ := PMF.bind_const _ _


/-- Physical completion makes the original sample law exact at the actual phase exit. -/
theorem sourcePhase_sample_raw_stopped_draw_law
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (completes : PhaseService.CompletesPlay runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((PhaseCount.rawMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace
        (some anchor))
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .sample) (event : graph.EventId) (rank : event.val = phase.low)
    (ready : anchor.execution.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (output : graph.outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode graph.layout) output) (graph.nodes event) =
      .sample payload law)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? anchor.execution.application.current.native.config.store = some draw)
    (profile : ∀ who, ((PhaseCount.rawMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).BehavioralPolicy who) :
    let initial := inputs.map (PhaseRuntimeState.initial plan)
    let menu := (PhaseCount.rawMenu runtime leaks bounds)
    let model := menu.information initial horizon scheduler
    let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
    let field : FieldRef graph.layout (.publicData payload) := ⟨.inr event, output⟩
    let read : (menu.protocol initial horizon scheduler).History → Option (L.Val payload) :=
      fun history => history.state.bind fun control =>
        field.get? control.execution.application.current.native.config.store
    let stopped := fun history : (menu.protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.execution.application.attempt
    (model.runBehavioralUntil certificate profile stopped ⟨some anchor, anchorTrace⟩).map read =
      draw.map some := by
  classical
  intro initial menu model certificate field read stopped
  let app := phaseApplication runtime leaks
  let potential : app.ProtocolState → PMF (Option (L.Val payload)) := fun state =>
    match state with
    | none => PMF.pure none
    | some control =>
        if control.execution.application.attempt = anchor.execution.application.attempt then
          draw.map some
        else PMF.pure (field.get? control.execution.application.current.native.config.store)
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan input
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized (menu.toRawTrace initial horizon scheduler anchorTrace)
  have stoppedLaw : ∀ history : (menu.protocol initial horizon scheduler).History,
      TracePrefix anchorTrace history.trace →
      (∃ current : app.Control, history.state = some current ∧
        (current.execution.application.attempt = anchor.execution.application.attempt →
          current.execution.application.phases = anchor.execution.application.phases)) →
      (model.runBehavioralUntil certificate profile stopped history).map read =
        potential history.state := by
    intro history
    induction history using certificate.induction with
    | _ history ih =>
      rintro kept ⟨current, state, phasesKept⟩
      by_cases halt : stopped history
      · rw [model.runBehavioralUntil_of_stopped certificate profile halt, PMF.pure_map]
        have changed : current.execution.application.attempt ≠
            anchor.execution.application.attempt :=
          by simpa only [stopped, state] using halt
        simp only [read, state, Option.bind_some, potential, ite_eq_right changed]
      have same : current.execution.application.attempt = anchor.execution.application.attempt :=
        by simpa only [stopped, state, not_not] using halt
      have phases : current.execution.application.phases = phase :: remaining :=
        (phasesKept same).trans installed
      let raw := menu.toRawTrace initial horizon scheduler (state ▸ history.trace)
      have currentOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        scheduler initialized raw
      by_cases ended : (menu.protocol initial horizon scheduler).terminal history.state
      · have terminal : app.terminal (some current) := by
          change app.terminal history.state at ended
          rwa [state] at ended
        have complete := completes current raw terminal
        have live := (phaseApplication_live runtime leaks).history initial horizon scheduler
          (fun state supported => by
            obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
            exact ⟨PhaseRuntimeState.initial_frontier plan input,
              PhaseRuntimeState.initial_live plan input⟩) raw
        have member : phase ∈ current.execution.application.phases.head? := by
          rw [phases]
          exact Option.mem_some_iff.mpr rfl
        exact (live.2 phase member
          (fun event _inside => complete.symm ▸ Finset.mem_univ event)).elim
      have geometry := (phaseApplication_quiescent runtime leaks ordered).history initial horizon
        scheduler (fun state supported => by
          obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
          exact phaseApplication_initial_quiescent plan ordered maximal input) raw
      have living := (phaseApplication_live runtime leaks).history initial horizon scheduler
        (fun state supported => by
          obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨PhaseRuntimeState.initial_frontier plan input,
            PhaseRuntimeState.initial_live plan input⟩) raw
      have head : current.execution.application.phases.head? = some phase := by
        simp only [phases, List.head?_cons]
      obtain ⟨selected, selectedRank, selectedReady, _actorless⟩ :=
        current.execution.application.sample_ready_of_live geometry.1 living.2 geometry.2.2 phase
          head kind
      have selectedEq : selected = event := Fin.ext (selectedRank.trans rank.symm)
      subst selected
      have keptState : TracePrefix anchorTrace (state ▸ history.trace) := by
        have transport : ∀ target (equal : history.state = target),
            TracePrefix anchorTrace (equal ▸ history.trace) := by
          intro target equal
          cases equal
          exact kept
        exact transport _ state
      have preserved := (phase_prefix_semantic_extension runtime leaks menu initial horizon
        scheduler anchor current anchorTrace (state ▸ history.trace) keptState anchorOrdered
          same.symm).1
      have agrees : Store.AgreeOn anchor.execution.application.current.native.config.store
          current.execution.application.current.native.config.store law.readFields := by
        intro selected selectedRead
        have available := anchor.execution.application.current.native.config.read_available ready
          (show selected ∈ (graph.nodes event).readFields from by
            rw [← EventCode.readFields_cast output (graph.nodes event), code]
            exact selectedRead)
        obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp available
        exact present.trans (preserved selected value present).symm
      have actualEval : law.eval? current.execution.application.current.native.config.store =
          some draw := (law.eval?_congr _ _ agrees).symm.trans evaluates
      have row := sourcePhase_sample_raw_control_harmonic runtime leaks bounds initial horizon
        scheduler profile history current state geometry.1 phase remaining phases kind event rank
          selectedReady payload law output code draw actualEval
      have actualRow : (model.runBehavioralFrom profile 1 history).bind
          (fun after => potential after.state) = potential history.state := by
        have right : potential history.state = draw.map some := by
          simp only [potential, state, same, ite_true]
        rw [right]
        convert row using 1
        congr 1
        funext after
        cases after.state with
        | none => rfl
        | some control =>
            change (if control.execution.application.attempt =
                anchor.execution.application.attempt then _ else _) =
              (if control.execution.application.attempt =
                current.execution.application.attempt then _ else _)
            rw [same]
      rw [model.runBehavioralUntil_of_running certificate profile halt ended, PMF.map_bind]
      calc
        _ = (model.runBehavioralFrom profile 1 history).bind
            (fun after => potential after.state) := by
          apply bind_congr_on_support
          intro after supported
          obtain ⟨⟨joint, legal, realized⟩, _future⟩ :=
            model.mem_support_runBehavioralFrom_one profile ended supported
          have moved : after.state ∈
              (app.transition initial horizon scheduler (some current) joint).support := by
            change after.state ∈
              (app.transition initial horizon scheduler history.state joint).support at realized
            simpa only [state] using realized
          obtain ⟨next, nextState, _recall⟩ := app.transition_recall_prefix initial horizon
            scheduler current after.state joint moved
          have retained := (model.runBehavioralFrom_reachesWithin profile 1 history after
            supported).tracePrefix
          apply ih after ⟨joint, legal, realized⟩ (kept.trans retained)
          refine ⟨next, nextState, ?_⟩
          intro nextSame
          have actual : some next ∈
              (app.transition initial horizon scheduler (some current) joint).support := by
            rwa [nextState] at moved
          exact (((phaseApplication_sameAttempt_controls runtime leaks).transition initial horizon
            scheduler current next joint actual currentOrdered (same.trans nextSame.symm)).1).trans
              (phasesKept same)
        _ = _ := actualRow
  have result := stoppedLaw ⟨some anchor, anchorTrace⟩ .refl ⟨anchor, rfl, fun _ => rfl⟩
  simpa only [potential, ite_true] using result


end Vegas
