/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingInformation
import Interaction.ReactiveScheduleEvaluation
import Interaction.ReactiveBayes
import GameTheoryExtensions.Analysis.Protocol.ConsistentLikelihood

/-! # Actual native reach probabilities at Bob's first binding

The original scheduler fixes activation actors only before Bob's first
binding. Its later conditional callback remains unchanged. Every actual raw
history at the first binding has protocol depth seventeen. The behavioral
law at this depth is exactly eleven complete rounds followed by the next
Bob activation, with its actual pending sample and full private recalls.
Grouped reach weights consequently equal physical information-event masses
over all raw histories, including private submission aliases.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBindingPrefix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private def prefixSchedule : List (Option Player) :=
  [some alice, none, none, some alice, some bob, none,
    none, some alice, none, none, none, some bob]

private theorem prefix_actor (position : Nat) (early : position < 12)
    (view : app.EnvironmentView) (command : app.Command)
    (selected : command ∈ (stageChoice weight nonnegative position view).support) :
    command.actor? app = (prefixSchedule[position]?).join := by
  interval_cases position <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
  all_goals try subst command
  all_goals first
    | exact (latestAuthor_passive _ _).1
    | exact (lottery_passive weight nonnegative view command selected).1
    | rfl

private theorem prefix_counts (position : Nat) (early : position < 12) :
    ((prefixSchedule.take (position + 1)).filterMap id).length =
      ((prefixSchedule.take position).filterMap id).length +
        (prefixSchedule[position]?).join.toList.length := by
  interval_cases position <;> decide

private def PrefixDepth (state : app.ProtocolState) (depth : Nat) : Prop :=
  match state with
  | none => depth = 0
  | some control => control.execution.environmentRecall.length ≤ 12 →
      depth + control.actor.toList.length =
        1 + control.execution.environmentRecall.length +
          ((prefixSchedule.take control.execution.environmentRecall.length).filterMap id).length

private theorem trace_prefix_depth :
    ∀ {state} (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace state),
      PrefixDepth state trace.length
  | _, .start => rfl
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := trace_prefix_depth before
      have reached : target ∈ (app.transition initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) source joint).support := realized
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          have counted : before.length = 0 := inherited
          intro _
          simp only [Trace.length, ReactiveApplication.Execution.initial, List.length_nil,
            Option.toList_none, Nat.add_zero, List.take_zero, List.filterMap_nil, counted]
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some owner =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro early
              have depth := inherited early
              simpa only [Trace.length, app.respond_environmentRecall, Option.toList_some,
                Option.toList_none, List.length_singleton, List.length_nil, Nat.add_zero]
                  using depth
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have advanced : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment app, command⟩] := by
                    obtain ⟨updated, _, equal⟩ := PMF.support_map .. ▸ supported
                    cases equal
                    rfl
                  intro early
                  have position : execution.environmentRecall.length < 12 := by
                    rw [advanced, List.length_append, List.length_singleton] at early
                    omega
                  have priorEarly : execution.environmentRecall.length ≤ 12 := by omega
                  have depth := inherited priorEarly
                  simp only [Option.toList_none, List.length_nil, Nat.add_zero] at depth
                  have actorEq := prefix_actor weight nonnegative execution.environmentRecall.length
                    position (execution.observeEnvironment app) command selected
                  have increments := prefix_counts execution.environmentRecall.length position
                  simp only [Trace.length, advanced, List.length_append, List.length_singleton]
                  rw [actorEq]
                  omega

/-- Every raw active history at the original first Bob binding has the same
protocol depth, independently of all transmitted packets and their samples. -/
theorem binding_trace_length (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩)) : trace.length = 17 := by
  have cursor := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change execution.environmentRecall.length + 14 = 26 at cursor
  have atBinding : execution.environmentRecall.length = 12 := by omega
  have depth := trace_prefix_depth weight nonnegative trace (by
    change execution.environmentRecall.length ≤ 12
    omega)
  rw [atBinding] at depth
  change trace.length + 1 = 1 + 12 + 5 at depth
  omega

private theorem prefix_control_steps (players : Player → app.Policy)
    (count : Nat) (early : count ≤ 11) :
    (fun law => law.bind (app.controlStep initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) players))^[
        count + ((prefixSchedule.take count).filterMap id).length + 1] (PMF.pure none) =
      (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
        players count).map (fun execution => some ⟨26 - count, none, execution⟩) := by
  induction count with
  | zero =>
      change (fun law => law.bind (app.controlStep initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) players))^[1] (PMF.pure none) = _
      rw [Function.iterate_one, PMF.pure_bind]
      change initial.map (fun state => (some ⟨26, none,
        ReactiveApplication.Execution.initial app state⟩ : app.ProtocolState)) =
          (initial.bind fun state => PMF.pure
            (ReactiveApplication.Execution.initial app state)).map
              (fun execution => (some ⟨26, none, execution⟩ : app.ProtocolState))
      rw [PMF.map_bind]
      simp only [PMF.pure_map]
      rfl
  | succ count ih =>
      let actor := (prefixSchedule[count]?).join
      have oldEarly : count ≤ 11 := by omega
      have increments := prefix_counts count (by omega)
      have depth : count + 1 + ((prefixSchedule.take (count + 1)).filterMap id).length + 1 =
          (1 + actor.toList.length) +
            (count + ((prefixSchedule.take count).filterMap id).length + 1) := by
        dsimp only [actor]
        omega
      rw [depth, Function.iterate_add_apply, ih oldEarly]
      rw [← PMF.bind_pure_comp, Function.comp_def, iterate_bind]
      rw [ReactiveApplication.roundsFrom_succ, PMF.map_bind]
      apply bind_congr_on_support
      intro execution supported
      have cursor := app.roundsFrom_recall initial
        (LateOpeningRuntimeService.scheduler weight nonnegative) players count execution supported
      have remaining : 26 - count = 26 - (count + 1) + 1 := by omega
      rw [remaining]
      exact app.control_round initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) players (26 - (count + 1))
          execution actor (by
            intro command selected
            change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
              (execution.observeEnvironment app)).support at selected
            rw [cursor] at selected
            exact prefix_actor weight nonnegative count (by omega)
              (execution.observeEnvironment app) command selected)

def bindingPrefix
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    PMF app.ProtocolState :=
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile
  (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative) players 11).bind
    fun execution => (execution.environmentStep app (.activate bob)).map
      (fun next => some ⟨14, some bob, next⟩)

/-- The exact original evaluator law before Bob's binding response. -/
theorem binding_prefix_law
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile 17).map History.state =
      bindingPrefix weight nonnegative profile := by
  classical
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile
  have covered : ∀ who, rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (players who) := by
    intro who
    exact rawMenu.admissible_of_covered initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (fun actor past view response supported => rawMenu.decode_embedPolicy_covered initial
          LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
            actor (profile actor) past view response supported) who
  have restricted : (fun who => rawMenu.restrictPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (players who)) = profile := by
    funext who
    exact rawMenu.restrict_decode_embedPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (profile who)
  have runner := rawMenu.run_restrict_control_steps initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players covered 17
      (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).initHistory
  rw [restricted] at runner
  change ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile 17).map
      History.state = _ at runner
  rw [runner]
  change (fun law : PMF app.ProtocolState => law.bind (app.controlStep initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      players))^[17] (PMF.pure none) = _
  rw [show 17 = 1 + (11 + ((prefixSchedule.take 11).filterMap id).length + 1) from rfl,
    Function.iterate_add_apply, prefix_control_steps weight nonnegative players 11 (by omega),
    Function.iterate_one]
  unfold bindingPrefix
  rw [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind]
  apply bind_congr_on_support
  intro execution supported
  have cursor := app.roundsFrom_recall initial (LateOpeningRuntimeService.scheduler weight
    nonnegative) players 11 execution supported
  rw [PMF.pure_bind]
  change app.controlStep initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (some ⟨15, none, execution⟩) = _
  unfold ReactiveApplication.controlStep ReactiveApplication.actor ReactiveApplication.transition
  simp only [Option.bind_some]
  change (stageChoice weight nonnegative execution.environmentRecall.length
    (execution.observeEnvironment app)).bind _ = _
  rw [cursor]
  exact PMF.pure_bind _ _

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (current : representative.1.state = some ⟨14, some bob, execution⟩)
  (ready : execution.application.config.cut.Ready bobBindEvent)

include current ready in
/-- Full raw information fibers of a fresh first binding have depth seventeen. -/
theorem binding_common_depth : InformationModel.InformationSite.CommonDepth
    (LateOpeningRuntimeNash.model weight nonnegative) site 17 := by
  intro history
  have active := InformationModel.InformationSite.active _ site history
  obtain ⟨control, stateEq, actor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawHistory _ _ _ history.1) bob active
  change history.1.state = some control at stateEq
  let rawTrace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.1.trace
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace =
    (rawMenu.signals _ _ _).infoOf bob history.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe bob representative.1.state = app.observe bob history.1.state at information
  rw [current, stateEq] at information
  simp only [ReactiveApplication.observe, actor, ↓reduceIte] at information
  have sameView := congrArg Prod.snd (Option.some.inj information)
  change execution.observe app bob = control.execution.observe app bob at sameView
  have inheritedReady := LateOpeningRuntimeBobBindingInformation.ready_same_view
    execution control.execution sameView ready
  have representativeTrace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩) := current ▸ rawMenu.toRawTrace initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      representative.1.trace
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) representativeTrace
  have originalCursor : execution.environmentRecall.length = 12 := by
    change execution.environmentRecall.length + 14 = 26 at accounted
    omega
  have originalClock : execution.application.clock = 3 := by
    rw [clock_history weight nonnegative _ representativeTrace, originalCursor]
    decide
  have sameClock := congrArg (fun view : app.PlayerView => view.application.publicView.clock)
    sameView
  change execution.application.clock = control.execution.application.clock at sameClock
  have actualClock : LateOpeningRuntimeService.clockAt
      control.execution.environmentRecall.length = 3 :=
    (clock_history weight nonnegative control rawTrace).symm.trans
      (sameClock.symm.trans originalClock)
  have slot := active_cursor weight nonnegative control rawTrace bob actor
  have remaining : control.remaining = 14 := by
    rcases slot with ⟨impossible, _⟩ | ⟨_, positions | ⟨position, completed⟩⟩
    · cases impossible
    · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
      rcases positions with position | position | position
      · rw [position] at actualClock
        exact ((by decide : LateOpeningRuntimeService.clockAt 5 ≠ 3) actualClock).elim
      · have budget := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) rawTrace
        change control.execution.environmentRecall.length + control.remaining = 26 at budget
        omega
      · rw [position] at actualClock
        exact ((by decide : LateOpeningRuntimeService.clockAt 20 ≠ 3) actualClock).elim
    · exact (inheritedReady.1
        ((control.execution.application.config.history_exact bobBindEvent).mp completed)).elim
  have sameControl : control = ⟨14, some bob, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor remaining ⊢
    exact ⟨remaining, actor, trivial⟩
  have transported_length {first second : app.ProtocolState} (equal : first = second)
      (trace : (app.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace first) :
      (equal ▸ trace).length = trace.length := by
    cases equal
    rfl
  have depth := binding_trace_length weight nonnegative control.execution
    ((congrArg some sameControl) ▸ rawTrace)
  rw [transported_length] at depth
  dsimp only [rawTrace] at depth
  rw [transported_length, rawMenu.toRawTrace_length] at depth
  exact depth

include current ready in
theorem information_mass_eq_prefix
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    (LateOpeningRuntimeNash.model weight nonnegative).informationMass profile bob site =
      (bindingPrefix weight nonnegative profile).toOuterMeasure
        {state | app.observe bob state = site.1} := by
  have exactDepth := binding_common_depth weight nonnegative site representative execution
    current ready
  rw [(LateOpeningRuntimeNash.model weight nonnegative).informationMass_eq_fixedDepth_toOuterMeasure
    profile bob site 17 exactDepth, ← binding_prefix_law weight nonnegative profile,
    PMF.toOuterMeasure_map_apply]
  congr 1
  ext history
  change (LateOpeningRuntimeNash.model weight nonnegative).infoOf bob history.trace = site.1 ↔
    app.observe bob history.state = site.1
  rw [show (LateOpeningRuntimeNash.model weight nonnegative).infoOf bob history.trace =
    app.observe bob history.state from rawMenu.info initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) bob history.trace]

include current ready in
theorem state_belief_eq_prefix
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (LateOpeningRuntimeNash.model weight nonnegative) assessment
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))) :
    assessment.stateBelief bob site =
      fiberPosterior (bindingPrefix weight nonnegative assessment.strategy) (app.observe bob)
        site.1 := by
  rw [rawMenu.stateBelief_eq_conditional_prefix initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment mixed bayes bob site 17
      (binding_common_depth weight nonnegative site representative execution current ready),
    binding_prefix_law weight nonnegative assessment.strategy]

include current ready in
theorem readout_reach_eq_prefix {Label : Type}
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (readout : app.ProtocolState → Label) (value : Label) :
    (LateOpeningRuntimeNash.model weight nonnegative).readoutReach profile bob site
        (readout ∘ History.state) value =
      (bindingPrefix weight nonnegative profile).toOuterMeasure
        {state | app.observe bob state = site.1 ∧ readout state = value} := by
  classical
  rw [(LateOpeningRuntimeNash.model weight nonnegative).readoutReach_eq_informationReadout
    profile bob site (readout ∘ History.state) 17
      (binding_common_depth weight nonnegative site representative execution current ready) value,
    ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    ← binding_prefix_law weight nonnegative profile, PMF.toOuterMeasure_map_apply]
  congr 1
  ext history
  change (LateOpeningRuntimeNash.model weight nonnegative).informationReadout bob site
      (readout ∘ History.state) history = some value ↔
    app.observe bob history.state = site.1 ∧ readout history.state = value
  unfold InformationModel.informationReadout
  have info := rawMenu.info initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bob history.trace
  rw [show (LateOpeningRuntimeNash.model weight nonnegative).infoOf bob history.trace =
    app.observe bob history.state from info]
  by_cases observed : app.observe bob history.state = site.1
  · simp only [observed, ↓reduceIte, Function.comp_def, Option.some.injEq, true_and]
  · simp only [observed, ↓reduceIte, reduceCtorEq, false_and]

open Classical in
/-- Every actual history in the information fiber whose existing physical
readout has the given value. No raw representation or pending trace is omitted. -/
def readoutHistories {Label : Type} (readout : app.ProtocolState → Label) (value : Label) :
    Finset ((LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :=
  Finset.univ.filter (fun history => readout history.1.state = value)

include current ready in
theorem finite_history_reach_eq_prefix {Label : Type}
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (readout : app.ProtocolState → Label) (value : Label) :
    InformationModel.finiteHistoryReach profile bob site
        (readoutHistories weight nonnegative site readout value) =
      ((bindingPrefix weight nonnegative profile).toOuterMeasure
        {state | app.observe bob state = site.1 ∧ readout state = value}).toReal := by
  classical
  have mass : (LateOpeningRuntimeNash.model weight nonnegative).readoutReach profile bob site
      (readout ∘ History.state) value =
      ∑ history ∈ readoutHistories weight nonnegative site readout value,
        (LateOpeningRuntimeNash.model weight nonnegative).historyReachWeight profile history.1 := by
    rw [InformationModel.readoutReach, tsum_fintype, readoutHistories, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro history _
    change (if value = readout history.1.state then _ else 0) =
      (if readout history.1.state = value then _ else 0)
    rw [eq_comm (a := value) (b := readout history.1.state)]
  unfold InformationModel.finiteHistoryReach
  rw [← ENNReal.toReal_sum (fun history _ =>
    (LateOpeningRuntimeNash.model weight nonnegative).historyReachWeight_ne_top profile history.1),
    ← mass, readout_reach_eq_prefix weight nonnegative site representative execution current ready]

/-- The complete immutable initialized inputs, used only as a mathematical
readout for grouping hidden histories. They are not exposed to Bob's policy. -/
def initializedInputs (state : app.ProtocolState) : Option nativeGraph.Inputs :=
  state.map (fun control => control.execution.application.config.inputs)

include current ready in
theorem initialized_type_reach_eq_prefix
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) :
    InformationModel.finiteHistoryReach profile bob site
        (readoutHistories weight nonnegative site initializedInputs
          (some (setup.eventInputs (sourceInitial bit label)))) =
      ((bindingPrefix weight nonnegative profile).toOuterMeasure
        {state | app.observe bob state = site.1 ∧
          initializedInputs state = some (setup.eventInputs (sourceInitial bit label))}).toReal :=
  finite_history_reach_eq_prefix weight nonnegative site representative execution current ready
    profile initializedInputs (some (setup.eventInputs (sourceInitial bit label)))

end Vegas.Examples.LateOpeningRuntimeBindingPrefix
