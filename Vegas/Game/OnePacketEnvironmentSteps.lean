module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketFactorization
public import Vegas.Pending.ExclusionInvariant
public import Vegas.Pending.ReactiveGraphSteps
public import Interaction.ReactiveResponseAccounting

@[expose] public section

/-! # Scheduler rounds factor through the operational record

The mass of a scheduler round of the one-packet game is the chance mass of the
first event it completes, times a function of the operational states before and after
the round (`Vegas.environment_stepProb`). That function reads the command from
the scheduler's recall after the round, takes its mass under the scheduler at
the recall and view before it, and at an activation multiplies by the mass the
observation rule gives the leaked packets (`Vegas.environmentMass`). The network
is recorded whole in the operational state (`Vegas.OperationalState.network`),
so no hypothesis on the scheduler or the observation rule is needed for this.

Automatic completions retain the primary output and contribute no extra mass.
So the operational steps of the factorization reduce to their component part:
any response mass satisfying the component bound at regular responses of other
players gives operational steps, with the round mass at scheduler rounds
(`Vegas.OperationalSteps.ofComponents`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The network an operational state records. -/
def OperationalState.network (state : OperationalState setup timeouts leaks) :
    MessageNetwork Player (application setup timeouts leaks).Payload :=
  ⟨state.environment.network.pending, state.environment.network.ledger, state.leaked,
    state.environment.network.inputs, state.environment.network.nextSerial⟩

/-- The mass of the network effect of a command: at an activation, the mass the
observation rule gives the packets the activated player learns; one
otherwise. -/
def commandMass (before after : OperationalState setup timeouts leaks) :
    (application setup timeouts leaks).Command → ℝ
  | .activate who =>
      ((leaks who before.network.pending).toOuterMeasure
        {selected | before.network.learn who selected = after.network
          (timeouts := timeouts)}).toReal
  | _ => 1

variable (scheduler : (application setup timeouts leaks).Scheduler)

/-- **The operational mass of a scheduler round.** The scheduler's mass for the
command recorded by the round, at the recall and view before it, times the
mass of the command's network effect. -/
def environmentMass :
    Option (OperationalState setup timeouts leaks) → Option (OperationalState setup timeouts leaks)
      → ℝ
  | some before, some after =>
      match after.environmentRecall.drop before.environmentRecall.length with
      | [entry] => (scheduler before.environmentRecall before.environment entry.command).toReal *
          commandMass setup timeouts leaks before after entry.command
      | _ => 1
  | _, _ => 1

variable {setup timeouts leaks scheduler}

/-- No new graph record contributes no chance mass. -/
theorem completionMass_of_config_eq {before after : EventGraphRuntime.State (graph setup)}
    (same : after.config = before.config) : completionMass setup before after = 1 := by
  unfold completionMass
  rw [same, List.drop_length]

/-- The completion mass of a completion with the given event and action is the
graph step's mass for a chance event. -/
theorem completionMass_of_chance (before after : EventGraphRuntime.State (graph setup))
    {event : (graph setup).EventId} (ready : before.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.config ∈ (before.config.step event ready action).support)
    (chance : (graph setup).actor? event = none) :
    completionMass setup before after =
      ((before.config.step event ready action) after.config).toReal := by
  let available := EventGraph.EventCode.eval?_isSome_of_reads ((graph setup).nodes event)
    (before.config.effectiveAction event action) before.config.store
    (fun _ read => before.config.read_available ready read)
  let law := (((graph setup).nodes event).eval?
    (before.config.effectiveAction event action) before.config.store).get available
  have evaluate : ((graph setup).nodes event).eval?
      (EventGraph.EventCode.actionOfActorNone _ chance) before.config.store = some law := by
    rw [← EventGraph.EventCode.action_eq_of_actor_none ((graph setup).nodes event) chance
      (before.config.effectiveAction event action)
      (EventGraph.EventCode.actionOfActorNone _ chance)]
    exact (Option.some_get available).symm
  change after.config ∈ (law.map (before.config.complete event ready action)).support at member
  obtain ⟨value, _supported, reached⟩ := PMF.support_map .. ▸ member
  have injective : Function.Injective (before.config.complete event ready action) := by
    intro first second equal
    have outputs := congrArg (fun config : (graph setup).Config => config.outputs event) equal
    simp only [EventGraph.Config.complete_output_same] at outputs
    exact Option.some.inj outputs
  unfold completionMass
  rw [← reached]
  simp only [EventGraph.Config.complete_history, List.drop_left,
    EventGraph.completion, chance, ↓reduceDIte,
    EventGraph.Config.complete_output_same, evaluate]
  change (law value).toReal =
    ((law.map (before.config.complete event ready action))
      (before.config.complete event ready action value)).toReal
  rw [pmf_map_apply_of_injective _ injective]

/-- A primary graph step contributes its chance atom mass, or one for an owned event. -/
theorem completionMass_of_step {before after : EventGraphRuntime.State (graph setup)}
    {event : (graph setup).EventId} {ready : before.config.cut.Ready event}
    {action : (graph setup).Action event}
    (member : after.config ∈ (before.config.step event ready action).support) :
    completionMass setup before after =
      match (graph setup).actor? event with
      | none => (before.config.step event ready action after.config).toReal
      | some _ => 1 := by
  cases acting : (graph setup).actor? event with
  | none => exact completionMass_of_chance before after ready member acting
  | some owner =>
      obtain ⟨value, _output, history⟩ := before.config.step_completion event ready action
        after.config member
      unfold completionMass
      rw [history, List.drop_left]
      simp only [EventGraph.completion, acting, reduceCtorEq, ↓reduceDIte]

private theorem completionMass_of_step_path
    {before middle after : EventGraphRuntime.State (graph setup)}
    {event : (graph setup).EventId} {ready : before.config.cut.Ready event}
    {action : (graph setup).Action event}
    (member : middle.config ∈ (before.config.step event ready action).support)
    (path : Relation.ReflTransGen EventGraph.Config.Step middle.config after.config) :
    completionMass setup before after = completionMass setup before middle := by
  obtain ⟨value, stored, history⟩ := before.config.step_completion event ready action
    middle.config member
  have retained : after.config.outputs event = some value := by
    change after.config.store (.inr event) = some value
    have retain {first last : (graph setup).Config}
        (steps : Relation.ReflTransGen EventGraph.Config.Step first last)
        (present : first.store (.inr event) = some value) :
        last.store (.inr event) = some value := by
      induction steps using Relation.ReflTransGen.head_induction_on with
      | refl => exact present
      | @head current next moved _ ih =>
          obtain ⟨query, available, choice, supported⟩ := moved
          exact ih (current.step_store_of_some next query available choice supported
            (.inr event) value present)
    exact retain path stored
  obtain ⟨extra, extension⟩ := EventGraph.Config.Step.path_history_prefix path
  unfold completionMass
  rw [← extension, history, List.append_assoc]
  simp only [List.drop_left, List.singleton_append, EventGraph.completion]
  rw [retained, stored]

private theorem completionMass_of_automatic_path
    {before after : EventGraphRuntime.State (graph setup)}
    (path : Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep before after) :
    completionMass setup before after = 1 := by
  rcases path.cases_head with same | ⟨middle, moved, tail⟩
  · exact completionMass_of_config_eq (congrArg EventGraphRuntime.State.config same.symm)
  · obtain ⟨event, eligible, rfl⟩ := moved
    obtain ⟨action, supported⟩ := before.completeAutomatic_step event eligible
    obtain ⟨owner, acting, _inactive⟩ := eligible.owned
    rw [completionMass_of_step_path supported (State.automatic_path_graph_steps tail),
      completionMass_of_step supported]
    simp only [acting]

/-- A point mass at a reached point has mass one there. -/
private theorem pure_apply_of_mem {α : Type*} {point reached : α}
    (member : reached ∈ (PMF.pure point).support) : (PMF.pure point reached).toReal = 1 := by
  rw [(PMF.mem_support_pure_iff _ _).mp member, PMF.pure_apply_self, ENNReal.toReal_one]

/-- An expiry that completes an event completes one with an actor. -/
theorem expire_completion_actor (state next : EventGraphRuntime.State (graph setup))
    (expired : (graph setup).EventId)
    (changed : next ∈ (EventGraphRuntime.environmentStep timeouts state
      (.expire expired)).support)
    {event : (graph setup).EventId} {ready : state.config.cut.Ready event}
    {action : (graph setup).Action event}
    (member : next.config ∈ (state.config.step event ready action).support) :
    ∃ actor, (graph setup).actor? event = some actor := by
  have stutter : next = state → False := fun same => config_ne_of_step member (by rw [same])
  obtain ⟨_, effect⟩ := environmentStep_expire_config_activated timeouts state next
    expired changed
  rcases effect with ⟨configEq, _⟩ | ⟨expiredReady, expiredAction, expiredMember, _⟩
  · exact (config_ne_of_step member configEq).elim
  · cases step_event_unique expiredMember member
    cases view : nodeView (graph setup) expired with
    | bind owner _ outputEq codeEq => exact ⟨owner, nodeView_bind_actor outputEq codeEq⟩
    | resolve owner _ _ _ outputEq codeEq => exact ⟨owner, nodeView_resolve_actor outputEq codeEq⟩
    | sample payload law outputEq codeEq =>
        exfalso
        apply stutter
        cases activated : state.activatedAt expired with
        | none =>
            rw [environmentStep_expire_of_not_activated timeouts _ expired ready activated,
              PMF.mem_support_pure_iff] at changed
            exact changed
        | some entered =>
            by_cases due : timeouts.duration expired ≤ state.clock - entered
            · rw [environmentStep_expire_sample_eq timeouts _ expired ready entered activated
                due payload law outputEq codeEq view, PMF.mem_support_pure_iff] at changed
              exact changed
            · rw [environmentStep_expire_of_not_due timeouts _ expired ready entered
                activated due, PMF.mem_support_pure_iff] at changed
              exact changed


/-- The native operation includes its deterministic automatic tail. -/
theorem applicationStep_mass (state next : EventGraphRuntime.State (graph setup))
    (command : EnvironmentCommand (graph setup))
    (changed : next ∈ ((application setup timeouts leaks).environment state command).support) :
    ((application setup timeouts leaks).environment state command next).toReal =
      completionMass setup state next := by
  let app := application setup timeouts leaks
  have pureCase (native : EventGraphRuntime.State (graph setup))
      (law : EventGraphRuntime.environmentStep timeouts state command = PMF.pure native)
      (mass : completionMass setup state native.drain = 1) :
      (app.environment state command next).toReal = completionMass setup state next := by
    change ENNReal.toReal
      (((EventGraphRuntime.environmentStep timeouts state command).map State.drain) next) = _
    change next ∈ ((EventGraphRuntime.environmentStep timeouts state command).map
      State.drain).support at changed
    rw [law, PMF.pure_map] at changed ⊢
    rw [pure_apply_of_mem changed]
    cases (PMF.mem_support_pure_iff _ _).mp changed
    exact mass.symm
  cases command with
  | advanceClock =>
      apply pureCase { state with clock := state.clock + 1 } rfl
      simpa only [completionMass] using completionMass_of_automatic_path
        (State.drain_trace { state with clock := state.clock + 1 })
  | expire expired =>
      obtain ⟨native, nativeLaw⟩ : ∃ native,
          EventGraphRuntime.environmentStep timeouts state (.expire expired) = PMF.pure native :=
        ⟨_, rfl⟩
      have member : native ∈ (EventGraphRuntime.environmentStep timeouts state
          (.expire expired)).support := by
        rw [nativeLaw]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      apply pureCase native nativeLaw
      obtain ⟨_, effect⟩ :=
        environmentStep_expire_config_activated timeouts state native expired member
      rcases effect with ⟨same, _⟩ | ⟨ready, action, supported, _⟩
      · simpa only [completionMass, same] using
          (completionMass_of_automatic_path native.drain_trace)
      · obtain ⟨owner, acting⟩ := expire_completion_actor state native expired member supported
        rw [completionMass_of_step_path supported native.drain_graph_steps,
          completionMass_of_step supported]
        simp only [acting]
  | executeSample event =>
      by_cases ready : state.config.cut.Ready event
      · cases view : nodeView (graph setup) event with
        | sample payload distribution outputEq codeEq =>
            let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit
            let available := EventGraph.EventCode.eval?_isSome_of_reads ((graph setup).nodes event)
              (state.config.effectiveAction event action) state.config.store
              (fun _ read => state.config.read_available ready read)
            let draw := (((graph setup).nodes event).eval?
              (state.config.effectiveAction event action) state.config.store).get available
            have evaluates : ((graph setup).nodes event).eval?
                (state.config.effectiveAction event action) state.config.store = some draw :=
              (Option.some_get available).symm
            have graphLaw := state.config.step_eq_map_of_eval event ready action draw evaluates
            let native := fun value => state.complete event ready action value
            have law : app.environment state (.executeSample event) =
                draw.map (fun value => (native value).drain) := by
              change (EventGraphRuntime.environmentStep timeouts state (.executeSample event)).map
                State.drain = _
              rw [environmentStep_executeSample_eq timeouts state event ready payload distribution
                outputEq codeEq view, graphLaw, PMF.map_comp, PMF.map_comp]
              rfl
            have retained (value : ((graph setup).outputLayout event).Value) :
                (native value).drain.config.outputs event = some value :=
              (native value).drain_store_of_some (.inr event) value
                (state.config.complete_output_same event ready action value)
            have injective : Function.Injective (fun value => (native value).drain) := by
              intro first second same
              have values := congrArg (fun result : EventGraphRuntime.State (graph setup) =>
                result.config.outputs event) same
              rw [retained first, retained second] at values
              exact Option.some.inj values
            rw [law] at changed ⊢
            obtain ⟨value, chosen, rfl⟩ := PMF.support_map .. ▸ changed
            have member : (native value).config ∈
                (state.config.step event ready action).support := by
              rw [graphLaw, PMF.support_map]
              exact ⟨value, chosen, rfl⟩
            have graphInjective : Function.Injective
                (state.config.complete event ready action) := by
              intro first second same
              have outputs := congrArg (fun config : (graph setup).Config =>
                config.outputs event) same
              simp only [EventGraph.Config.complete_output_same] at outputs
              exact Option.some.inj outputs
            change ((draw.map (fun output => (native output).drain))
              (native value).drain).toReal = completionMass setup state (native value).drain
            rw [pmf_map_apply_of_injective draw injective,
              completionMass_of_step_path member (native value).drain_graph_steps,
              completionMass_of_chance _ _ ready member (nodeView_sample_actor outputEq codeEq),
              graphLaw]
            exact (congrArg ENNReal.toReal
              (pmf_map_apply_of_injective draw graphInjective value)).symm
        | bind owner payload outputEq codeEq =>
            apply pureCase state (environmentStep_executeSample_of_nonsample timeouts state event
              ready (fun _ _ _ _ sampled => by rw [view] at sampled; cases sampled))
            exact completionMass_of_automatic_path state.drain_trace
        | resolve owner payload binding checks outputEq codeEq =>
            apply pureCase state (environmentStep_executeSample_of_nonsample timeouts state event
              ready (fun _ _ _ _ sampled => by rw [view] at sampled; cases sampled))
            exact completionMass_of_automatic_path state.drain_trace
      · apply pureCase state (environmentStep_executeSample_of_not_ready timeouts state event ready)
        exact completionMass_of_automatic_path state.drain_trace


private theorem include_primary
    (execution : (application setup timeouts leaks).Execution) (id : MessageId Player) :
    (execution.includePending (application setup timeouts leaks) id).application.config =
        execution.application.config ∨
      ∃ (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
        (action : (graph setup).Action event) (native : EventGraphRuntime.State (graph setup))
        (owner : Player),
        native.config ∈ (execution.application.config.step event ready action).support ∧
        (graph setup).actor? event = some owner ∧
        (execution.includePending (application setup timeouts leaks) id).application.config =
          native.drain.config := by
  cases found : execution.network.lookup id with
  | none =>
      left
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  | some message =>
      cases accepted :
          (application setup timeouts leaks).handle execution.application message with
      | none =>
          left
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, accepted, Option.getD_none]
      | some next =>
          obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
          obtain ⟨event, named, ready, action, member⟩ :=
            handle_config_mem_step timeouts execution.application native _ handled
          refine Or.inr ⟨event, ready, action, native, message.sender, member,
            handle_sender_actor timeouts execution.application native _ handled event named, ?_⟩
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, accepted, Option.getD_some]
          rw [drained]

/-- An included packet whose complete endpoint is one graph step has an owned primary event. -/
theorem include_completion_actor (execution : (application setup timeouts leaks).Execution)
    (id : MessageId Player) {event : (graph setup).EventId}
    {ready : execution.application.config.cut.Ready event} {action : (graph setup).Action event}
    (member : (execution.includePending (application setup timeouts leaks) id).application.config ∈
      (execution.application.config.step event ready action).support) :
    ∃ actor, (graph setup).actor? event = some actor := by
  rcases include_primary execution id with same | ⟨primary, primaryReady, chosen, native, owner,
      moved, acting, drained⟩
  · exact (config_ne_of_step member same).elim
  · have completed : primary ∈ native.config.cut.completed := by
      rw [execution.application.config.step_cut primary primaryReady chosen native.config moved]
      exact Finset.mem_insert_self _ _
    have finalDone := EventGraph.Config.Step.path_completed_mono native.drain_graph_steps completed
    rw [← drained, execution.application.config.step_cut event ready action _ member] at finalDone
    rcases Finset.mem_insert.mp finalDone with same | old
    · subst primary
      exact ⟨owner, acting⟩
    · exact (primaryReady.1 old).elim

private theorem include_completionMass
    (execution : (application setup timeouts leaks).Execution) (id : MessageId Player) :
    completionMass setup execution.application
      (execution.includePending (application setup timeouts leaks) id).application = 1 := by
  rcases include_primary execution id with same | ⟨event, ready, action, native, owner,
      moved, acting, drained⟩
  · exact completionMass_of_config_eq same
  · calc
      _ = completionMass setup execution.application native.drain := by
        unfold completionMass
        rw [drained]
      _ = completionMass setup execution.application native :=
        completionMass_of_step_path moved native.drain_graph_steps
      _ = 1 := by
        rw [completionMass_of_step moved]
        simp only [acting]

/-- **The mass of one command.** The environment step of a command gives a
reached execution the chance mass of its completed event times the mass of the
command's network effect. -/
theorem environmentStep_mass (execution reached : (application setup timeouts leaks).Execution)
    (command : (application setup timeouts leaks).Command)
    (member : reached ∈ (execution.environmentStep (application setup timeouts leaks)
      command).support)
    (before after : OperationalState setup timeouts leaks) (beforeNetwork : before.network (timeouts
      := timeouts) =
      execution.network) (afterNetwork : after.network = reached.network) :
    (execution.environmentStep (application setup timeouts leaks) command reached).toReal =
      completionMass setup execution.application reached.application *
        commandMass setup timeouts leaks before after command := by
  let app := application setup timeouts leaks
  let record := execution.environmentRecall ++ [⟨execution.observeEnvironment app, command⟩]
  cases command with
  | activate who =>
      let place : MessageNetwork Player app.Payload → app.Execution := fun network =>
        { execution with network := network, environmentRecall := record }
      have lawEq : execution.environmentStep app (.activate who) =
          (leaks who execution.network.pending).map
            (fun selected => place (execution.network.learn who selected)) := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.map_comp]
        rfl
      rw [lawEq] at member ⊢
      obtain ⟨chosen, _, rfl⟩ := PMF.support_map .. ▸ member
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
        completionMass_of_config_eq rfl, one_mul]
      unfold commandMass
      rw [beforeNetwork, afterNetwork]
      congr 2
      ext selected
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro same
        exact congrArg ReactiveApplication.Execution.network same
      · intro same
        change place _ = place _
        rw [show (place (execution.network.learn who chosen)).network =
          execution.network.learn who chosen from rfl] at same
        rw [same]
  | wait =>
      have lawEq : execution.environmentStep app .wait =
          PMF.pure { execution with environmentRecall := record } := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.pure_map]
      rw [lawEq] at member ⊢
      rw [pure_apply_of_mem member, (PMF.mem_support_pure_iff _ _).mp member,
        completionMass_of_config_eq rfl]
      simp [commandMass]
  | «include» id =>
      have lawEq : execution.environmentStep app (.include id) =
          PMF.pure { execution.includePending app id with environmentRecall := record } := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.pure_map]
      rw [lawEq] at member ⊢
      rw [pure_apply_of_mem member]
      have applicationEq : reached.application = (execution.includePending app id).application := by
        rw [(PMF.mem_support_pure_iff _ _).mp member]
      have mass : completionMass setup execution.application reached.application = 1 := by
        rw [applicationEq]
        exact include_completionMass execution id
      rw [mass]
      simp only [commandMass, mul_one]
  | application command =>
      let place : EventGraphRuntime.State (graph setup) → app.Execution := fun state =>
        { execution with application := state, environmentRecall := record }
      have lawEq : execution.environmentStep app (.application command) =
          (app.environment execution.application command).map place := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.map_comp]
        rfl
      rw [lawEq] at member ⊢
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ member
      rw [pmf_map_apply_of_injective _ (fun first second same =>
        congrArg ReactiveApplication.Execution.application same) state]
      change ((application setup timeouts leaks).environment execution.application command
        state).toReal = completionMass setup execution.application state * 1
      exact (applicationStep_mass (timeouts := timeouts) (leaks := leaks)
        execution.application state command changed).trans (mul_one _).symm

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}

/-- **Scheduler rounds factor through the operational record.** The mass of a
scheduler round of the one-packet game, under any profile, is the chance mass
of the event it completes times the operational mass of the round. -/
theorem environment_stepProb
    (profile : ∀ player,
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy player)
    {before after : (application setup timeouts leaks).ProtocolState}
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup timeouts leaks).Action)
    (legal : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup timeouts leaks bounds horizon scheduler).step
      before
      ⟨joint, legal⟩).support) (control : (application setup timeouts leaks).Control)
    (initialized : before = some control) (idle : control.actor = none)
    (next : (application setup timeouts leaks).Control) (reachedNext : after = some next) :
    InformationModel.stepProb (onePacketInformation setup timeouts leaks bounds horizon scheduler)
        profile prior ⟨joint, legal⟩ after =
      completionMass setup control.execution.application next.execution.application *
        environmentMass setup timeouts leaks scheduler (operationalState setup timeouts leaks
          before)
          (operationalState setup timeouts leaks after) := by
  let app := application setup timeouts leaks
  subst initialized reachedNext
  rw [stepProb_of_idle (timeouts := timeouts) profile prior joint legal idle]
  change some next ∈ (app.transition (initialLaw setup) horizon scheduler (some control)
    joint).support at realized
  rcases control with ⟨remaining, current, execution⟩
  change current = none at idle
  subst idle
  cases remaining with
  | zero =>
      have lawEq : app.transition (initialLaw setup) horizon scheduler (some ⟨0, none, execution⟩)
          joint = PMF.pure (some ⟨0, none, execution⟩) := rfl
      rw [lawEq] at realized ⊢
      rw [pure_apply_of_mem realized]
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
      rw [completionMass_of_config_eq rfl]
      simp [environmentMass, operationalState]
  | succ remaining =>
      let shift : app.Command → app.Execution → app.ProtocolState := fun command reached =>
        some ⟨remaining, command.actor? app, reached⟩
      have lawEq : app.transition (initialLaw setup) horizon scheduler
          (some ⟨remaining + 1, none, execution⟩) joint =
          (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
            fun command => (execution.environmentStep app command).map (shift command) := rfl
      rw [lawEq] at realized ⊢
      obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
      obtain ⟨reached, member, same⟩ := PMF.support_map .. ▸ moved
      cases same
      have recallEq := app.environmentStep_environmentRecall execution reached command member
      rw [PMF.bind_apply, tsum_eq_single command]
      · rw [pmf_map_apply_of_injective _ (fun first second equal => by
            have inner := Option.some.inj equal
            exact congrArg ReactiveApplication.Control.execution inner) reached,
          ENNReal.toReal_mul]
        obtain ⟨first, firstEq⟩ : ∃ first, operationalState setup timeouts leaks
            (some ⟨remaining + 1, none, execution⟩) = some first := ⟨_, rfl⟩
        obtain ⟨second, secondEq⟩ : ∃ second, operationalState setup timeouts leaks
            (some ⟨remaining, command.actor? app, reached⟩) = some second := ⟨_, rfl⟩
        have firstRecall : first.environmentRecall =
          execution.environmentRecall := by
          rw [← Option.some.inj firstEq]
        have firstView : first.environment = execution.observeEnvironment app
          := by
          rw [← Option.some.inj firstEq]
        have firstNetwork : first.network = execution.network := by
          rw [← Option.some.inj firstEq]
          rfl
        have secondRecall : second.environmentRecall =
          reached.environmentRecall := by
          rw [← Option.some.inj secondEq]
        have secondNetwork : second.network = reached.network := by
          rw [← Option.some.inj secondEq]
          rfl
        rw [firstEq, secondEq, environmentStep_mass (timeouts := timeouts) execution reached command
          member first second
          firstNetwork secondNetwork]
        simp only [environmentMass, firstRecall, secondRecall, recallEq, List.drop_left, firstView]
        ring
      · intro other different
        rw [mul_eq_zero]
        right
        rw [PMF.apply_eq_zero_iff]
        intro present
        obtain ⟨otherReached, otherMember, otherSame⟩ := PMF.support_map .. ▸ present
        have inner := congrArg ReactiveApplication.Control.execution (Option.some.inj otherSame)
        change otherReached = reached at inner
        subst inner
        have otherRecall := app.environmentStep_environmentRecall execution otherReached other
          otherMember
        rw [recallEq] at otherRecall
        have entries := List.append_cancel_left otherRecall
        exact different (congrArg ReactiveApplication.EnvironmentEntry.command
          (List.singleton_injective entries)).symm

omit [Fintype Player] in
theorem environmentMass_nonneg (before after : Option (OperationalState setup timeouts leaks)) :
    0 ≤ environmentMass setup timeouts leaks scheduler before after := by
  unfold environmentMass
  split
  · split
    · rename_i entry _
      refine mul_nonneg ENNReal.toReal_nonneg ?_
      unfold commandMass
      split
      · exact ENNReal.toReal_nonneg
      · exact zero_le_one
    · exact zero_le_one
  · exact zero_le_one

/-- The operational mass of a transition: the round's mass at a scheduler round
and a given response mass at a response. -/
def roundOrResponseMass
    (response : Option (OperationalState setup timeouts leaks) → Option (OperationalState setup
      timeouts leaks) → ℝ)
    (before after : Option (OperationalState setup timeouts leaks)) : ℝ :=
  match before with
  | some state =>
      if state.actor = none then environmentMass setup timeouts leaks
        scheduler before after
      else response before after
  | none => 1

/-- **Operational steps from component steps.** Scheduler rounds need no
hypothesis: given a response mass for which every regular response of another
player satisfies the component bound, the operational steps hold with the round
mass at scheduler rounds. -/
def OperationalSteps.ofComponents {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player}
    (response : ℕ → Option (OperationalState setup timeouts leaks) →
      Option (OperationalState setup timeouts leaks) → ℝ)
    (error : ℕ → ℝ) (response_nonneg : ∀ n before after, 0 ≤ response n before after)
    (error_nonneg : ∀ n, 0 ≤ error n) (error_tendsto : Filter.Tendsto error Filter.atTop (nhds 0))
    (component : ∀ n {before after}
      (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace before)
        joint legal
      (_ : after ∈ ((onePacketProtocol setup timeouts leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup timeouts leaks).Control)
      (actor : Player), before = some control → after = some next →
      control.actor = some actor → actor ≠ who →
      forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw setup)
        horizon
        scheduler actor ((application setup timeouts leaks).observe actor (some control)) →
      ForcedState setup timeouts leaks who (some control) →
      0 < contentFactor setup timeouts leaks (sequence n) actor control.execution next.execution
        ((joint actor).getD ⟨none⟩) →
      |InformationModel.stepProb (onePacketInformation setup timeouts leaks bounds horizon
        scheduler)
          (profiles n) prior ⟨joint, legal⟩ after -
        contentFactor setup timeouts leaks (sequence n) actor control.execution next.execution
            ((joint actor).getD ⟨none⟩) *
          response n (operationalState setup timeouts leaks before) (operationalState setup timeouts
            leaks after)| ≤
        error n * (contentFactor setup timeouts leaks (sequence n) actor control.execution
          next.execution
            ((joint actor).getD ⟨none⟩) *
          response n (operationalState setup timeouts leaks before) (operationalState setup timeouts
            leaks after))) :
    OperationalSteps setup timeouts leaks bounds horizon scheduler sequence profiles who where
  mass n := roundOrResponseMass (timeouts := timeouts) (scheduler := scheduler)
    (response n)
  error := error
  mass_nonneg n before after := by
    unfold roundOrResponseMass
    split
    · split
      · exact environmentMass_nonneg (timeouts := timeouts) _ _
      · exact response_nonneg _ _ _
    · exact zero_le_one
  error_nonneg := error_nonneg
  error_tendsto := error_tendsto
  environment n before after prior joint legal realized control initialized
    idle next reached := by
    rw [environment_stepProb (timeouts := timeouts) (profiles n) prior joint legal realized control
      initialized idle next
      reached]
    subst initialized
    congr 1
    change _ = if control.actor = none then _ else _
    simp only [idle, ↓reduceIte]
  component n before after prior joint legal realized control next actor
    initialized reached
      acting other forced observerForced positive := by
    have bound := component n prior joint legal realized control next actor initialized reached
      acting other forced observerForced positive
    subst initialized
    have active : ¬ control.actor = none := by rw [acting]; exact Option.some_ne_none _
    have massEq : roundOrResponseMass (timeouts := timeouts) (scheduler := scheduler) (response n)
        (operationalState setup timeouts leaks (some control)) (operationalState setup timeouts
          leaks after) =
        response n (operationalState setup timeouts leaks (some control))
          (operationalState setup timeouts leaks after) := by
      change (if control.actor = none then _ else _) = _
      simp only [active, ↓reduceIte]
    rw [massEq]
    exact bound

end Vegas
