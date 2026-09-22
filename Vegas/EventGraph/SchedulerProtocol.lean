/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerReplay
import GameTheory.Protocol.Information

/-! # The public scheduler as a probability-analysis protocol

The singleton decision maker is the scheduler, not an additional game player.
Player policies and node chance remain transition kernels. The initial chance
step samples the entire input law, so a predrawn scheduler is chosen before
private setup. The application of this presentation to the actual graph runner
belongs to the scheduler predrawing law.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Exactly the arguments supplied to a public scheduling decision. -/
structure SchedulerSite (graph : Vegas.EventGraph Player L) where
  observation : graph.PublicObservation
  enabled : Finset graph.EventId
  nonempty : enabled.Nonempty

/-- Player and chance execution after a ready event has been selected. -/
def selectedPolicyStep (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) : FinDist graph.Config :=
  match actor : graph.actor? event with
  | some owner =>
      (profile owner event actor (graph.playerObserve owner config)).bind
        (config.step event ready)
  | none => config.step event ready (EventCode.actionOfActorNone (graph.nodes event) actor)

theorem selectedPolicyStep_history_length (profile : graph.BehavioralProfile)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (next : graph.Config)
    (member : next ∈ (selectedPolicyStep profile config event ready).support) :
    next.history.length = config.history.length + 1 := by
  unfold selectedPolicyStep at member
  split at member
  · rw [FinDist.support_bind] at member
    obtain ⟨action, _, supported⟩ := Set.mem_iUnion₂.mp member
    rw [config.step_history event ready action next supported]
    simp
  · rw [config.step_history event ready _ next member]
    simp

/-- There is no scheduler decision during setup or after termination. -/
def schedulerSite? : Option graph.Config → Option (SchedulerSite graph)
  | none => none
  | some config =>
      if terminal : config.cut.Terminal then none
      else some ⟨graph.publicObserve config, config.cut.enabled,
        enabled_nonempty_of_not_terminal config terminal⟩

private def schedulerTransition (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) (state : Option graph.Config)
    (choice : Option graph.EventId) : FinDist (Option graph.Config) :=
  match state with
  | none => inputs.map (fun initial => some (Config.initial initial))
  | some config => match choice with
    | none => FinDist.pure state
    | some event =>
        if ready : config.cut.Ready event then
          (selectedPolicyStep profile config event ready).map some
        else FinDist.pure state

/-- An analysis presentation whose only choices select ready graph events. -/
abbrev schedulerProtocol (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) : ExecutionProtocol Unit where
  State := Option graph.Config
  Action _ := graph.EventId
  init := none
  active state _ := match state with
    | none => False
    | some config => ¬ config.cut.Terminal
  available state _ := match state with
    | none => ∅
    | some config => {event | config.cut.Ready event}
  terminal state := match state with
    | none => False
    | some config => config.cut.Terminal
  step state choice := schedulerTransition profile inputs state (choice.1 ())
  progress state notTerminal := by
    cases state with
    | none => exact ⟨fun _ => none, fun _ => not_false⟩
    | some config =>
        obtain ⟨event, ready⟩ := config.cut.exists_ready_of_not_terminal notTerminal
        exact ⟨fun _ => some event, fun _ => ⟨notTerminal, ready⟩⟩

private abbrev schedulerSignals (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) : InfoSignals (schedulerProtocol profile inputs) where
  PublicSignal := Option (SchedulerSite graph)
  PrivateSignal _ := Unit
  initialPublic := none
  initialPrivate _ := ()
  publicSignal event := schedulerSite? event.target
  privateSignal _ _ := ()
  InfoState _ := Option (SchedulerSite graph)
  initInfo _ _ signal := signal
  pushInfo _ _ _ _ signal := signal

private theorem schedulerSignals_infoOf (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) {state : (schedulerProtocol profile inputs).State}
    (trace : (schedulerProtocol profile inputs).Trace state) :
    (schedulerSignals profile inputs).infoOf () trace = schedulerSite? state := by
  cases trace <;> rfl

/-- The scheduler's menu depends only on its public observation and enabled set. -/
abbrev schedulerInformation (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) : InformationModel (schedulerProtocol profile inputs) where
  toInfoSignals := schedulerSignals profile inputs
  menu _ site := match site with
    | none => {choice | choice = none}
    | some site => {choice | ∃ event, choice = some event ∧ event ∈ site.enabled}
  menu_adequate := by
    intro who state trace choice
    cases who
    rw [schedulerSignals_infoOf]
    cases state with
    | none => cases choice <;> simp [schedulerSite?, LegalOption]
    | some config =>
        by_cases terminal : config.cut.Terminal
        · cases choice <;> simp [schedulerSite?, terminal, LegalOption]
        · cases choice <;>
            simp [schedulerSite?, terminal, LegalOption, EventOrder.Cut.mem_enabled]

@[simp] theorem schedulerInformation_infoOf (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) {state : (schedulerProtocol profile inputs).State}
    (trace : (schedulerProtocol profile inputs).Trace state) :
    (schedulerInformation profile inputs).infoOf () trace = schedulerSite? state :=
  schedulerSignals_infoOf profile inputs trace

/-- The scheduler's actual behavioral response, with no player policy changed. -/
def schedulerBehavioral (profile : graph.BehavioralProfile) (inputs : FinDist graph.Inputs)
    (scheduler : graph.PublicScheduler) :
    (schedulerInformation profile inputs).BehavioralPolicy () :=
  fun site => match site with
  | none => FinDist.pure ⟨none, rfl⟩
  | some site => (scheduler site.observation site.enabled site.nonempty).map fun selected =>
      ⟨some selected.1, ⟨selected.1, rfl, selected.2⟩⟩

theorem schedulerBehavioral_of_some (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler)
    (info : Option (SchedulerSite graph)) (site : SchedulerSite graph)
    (same : info = some site) :
    schedulerBehavioral profile inputs scheduler info =
      (scheduler site.observation site.enabled site.nonempty).map
        (fun selected => ⟨some selected.1, by
          change some selected.1 ∈ (schedulerInformation profile inputs).menu () info
          rw [same]
          exact ⟨selected.1, rfl, selected.2⟩⟩) := by
  subst info
  rfl

/-- Extract a total deterministic public scheduler from a pure analysis policy. -/
def schedulerOfPolicy (profile : graph.BehavioralProfile) (inputs : FinDist graph.Inputs)
    (policy : (schedulerInformation profile inputs).Policy ()) :
    graph.DeterministicPublicScheduler := fun observation enabled nonempty => by
  let choice := policy (some ⟨observation, enabled, nonempty⟩)
  have present : choice.1.isSome := by
    obtain ⟨event, choiceEq, _⟩ := choice.2
    simp [choiceEq]
  refine ⟨choice.1.get present, ?_⟩
  obtain ⟨event, choiceEq, member⟩ := choice.2
  simpa [choiceEq] using member

private def schedulerDepth : Option graph.Config → Nat
  | none => 0
  | some config => config.history.length + 1

private theorem scheduler_step_depth (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs)
    (state next : (schedulerProtocol profile inputs).State)
    (joint : Unit → Option graph.EventId)
    (legal : (schedulerProtocol profile inputs).Legal state joint)
    (supported : next ∈ ((schedulerProtocol profile inputs).step state ⟨joint, legal⟩).support) :
    schedulerDepth next = schedulerDepth state + 1 := by
  change next ∈ (schedulerTransition profile inputs state (joint ())).support at supported
  cases state with
  | none =>
      rw [schedulerTransition, FinDist.support_map] at supported
      obtain ⟨initial, _, rfl⟩ := supported
      rfl
  | some config =>
      cases choiceEq : joint () with
      | none =>
          have inactive := legal.2 ()
          rw [choiceEq] at inactive
          exact False.elim (inactive legal.1)
      | some event =>
          have valid := legal.2 ()
          rw [choiceEq] at valid
          have ready : config.cut.Ready event := valid.2
          rw [choiceEq, schedulerTransition, dite_eq_left ready, FinDist.support_map] at supported
          obtain ⟨result, member, rfl⟩ := supported
          simp only [schedulerDepth, selectedPolicyStep_history_length profile config
            event ready result member]

private theorem scheduler_active_site (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) (state : (schedulerProtocol profile inputs).State)
    (active : (schedulerProtocol profile inputs).active state ()) :
    ∃ site, schedulerSite? state = some site ∧
      site.observation.completionOrder.length + 1 = schedulerDepth state := by
  cases state with
  | none => exact False.elim active
  | some config =>
      change ¬ config.cut.Terminal at active
      refine ⟨⟨graph.publicObserve config, config.cut.enabled,
        enabled_nonempty_of_not_terminal config active⟩, ?_, ?_⟩
      · simp [schedulerSite?, active]
      · simp [schedulerDepth, publicObserve]

private theorem scheduler_actedAt_depth_lt (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) {state : (schedulerProtocol profile inputs).State}
    (trace : (schedulerProtocol profile inputs).Trace state) :
    ∀ info ∈ (schedulerInformation profile inputs).actedAt () trace,
      ∃ site, info = some site ∧
        site.observation.completionOrder.length + 1 < schedulerDepth state := by
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint legal realized ih =>
      intro info member
      rw [InfoSignals.actedAt] at member
      have depth := scheduler_step_depth profile inputs source target joint legal realized
      cases choiceEq : joint () with
      | none =>
          rw [choiceEq] at member
          obtain ⟨site, same, smaller⟩ := ih info member
          exact ⟨site, same, by omega⟩
      | some event =>
          rw [choiceEq] at member
          have valid := legal.2 ()
          rw [choiceEq] at valid
          obtain ⟨site, siteEq, siteDepth⟩ := scheduler_active_site profile inputs source valid.1
          rcases List.mem_cons.mp member with now | before
          · refine ⟨site, ?_, by omega⟩
            exact now.trans ((schedulerInformation_infoOf profile inputs prior).trans siteEq)
          · obtain ⟨oldSite, same, smaller⟩ := ih info before
            exact ⟨oldSite, same, by omega⟩

/-- Completed-event count strictly separates the scheduler's decision sites.
Setup and terminal observations never contribute a scheduler action. -/
theorem scheduler_actsOnce (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) :
    (schedulerInformation profile inputs).ActsOnceWhereItMatters := by
  apply InformationModel.actsOnceWhereItMatters_of_actsOnce
  intro who state trace
  cases who
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint legal realized ih =>
      rw [InfoSignals.actedAt]
      cases choiceEq : joint () with
      | none => exact ih
      | some event =>
          rw [List.nodup_cons]
          refine ⟨?_, ih⟩
          intro member
          obtain ⟨oldSite, same, smaller⟩ :=
            scheduler_actedAt_depth_lt profile inputs prior _ member
          have valid := legal.2 ()
          rw [choiceEq] at valid
          obtain ⟨site, siteEq, siteDepth⟩ := scheduler_active_site profile inputs source valid.1
          rw [schedulerInformation_infoOf, siteEq] at same
          have siteSame := Option.some.inj same
          subst oldSite
          omega

/-- Recovering a pure scheduler and presenting it behaviorally recovers the
same singleton policy, including its uniquely determined inactive response. -/
theorem schedulerBehavioral_schedulerOfPolicy (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs)
    (policy : (schedulerInformation profile inputs).Policy ()) :
    schedulerBehavioral profile inputs (schedulerOfPolicy profile inputs policy).toPublic =
      policy.toBehavioral := by
  funext site
  cases site with
  | none =>
      apply congrArg FinDist.pure
      apply Subtype.ext
      exact (policy none).2.symm
  | some site =>
      simp only [schedulerBehavioral, DeterministicPublicScheduler.toPublic, FinDist.map_pure]
      apply congrArg FinDist.pure
      apply Subtype.ext
      exact Option.some_get _

/-- Separate the actual scheduler draw from the retained player/chance kernel. -/
theorem policyPlan_step_bind {Outcome : Type} (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal) (continuation : graph.Config → FinDist Outcome) :
    ((graph.policyPlan profile scheduler config notTerminal).bind fun choice =>
      (config.step choice.1.1 choice.1.2 choice.2).bind continuation) =
      (scheduler (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config notTerminal)).bind fun selected =>
          (selectedPolicyStep profile config selected.1
            ((EventOrder.Cut.mem_enabled _ _).mp selected.2)).bind continuation := by
  unfold policyPlan
  rw [FinDist.bind_bind]
  apply FinDist.bind_congr
  intro selected _
  split <;> rename_i actor
  · rw [FinDist.bind_map]
    unfold selectedPolicyStep
    split
    · rename_i owner actualActor
      have same := Option.some.inj (actualActor.symm.trans actor)
      subst owner
      rw [FinDist.bind_bind]
    · rename_i ownerless
      simp [ownerless] at actor
  · rw [FinDist.pure_bind]
    unfold selectedPolicyStep
    split
    · rename_i owner actualActor
      simp [actor] at actualActor
    · rfl

/-- The probability presentation takes exactly the actual scheduled graph
transition from a nonterminal initialized configuration. -/
theorem scheduler_step_bind {Outcome : Type} (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler)
    (config : graph.Config)
    (trace : (schedulerProtocol profile inputs).Trace (some config))
    (notTerminal : ¬ config.cut.Terminal)
    (continuation : Option graph.Config → FinDist Outcome) :
    ((schedulerInformation profile inputs).behavioralJoint
      (fun _ => schedulerBehavioral profile inputs scheduler) trace notTerminal).bind
        (fun draw =>
          ((schedulerProtocol profile inputs).step (some config) draw).bind continuation) =
      (graph.policyPlan profile scheduler config notTerminal).bind fun choice =>
        (config.step choice.1.1 choice.1.2 choice.2).bind
          (fun next => continuation (some next)) := by
  let M := schedulerInformation profile inputs
  let site : SchedulerSite graph := ⟨graph.publicObserve config, config.cut.enabled,
    enabled_nonempty_of_not_terminal config notTerminal⟩
  have infoEq : M.infoOf () trace = some site := by
    rw [schedulerInformation_infoOf]
    simp only [schedulerSite?, dite_eq_right notTerminal, site]
  let chosen (selected : {event : graph.EventId // event ∈ site.enabled}) :
      M.Choice () (M.infoOf () trace) := ⟨some selected.1, by
        change some selected.1 ∈ M.menu () _
        rw [infoEq]
        exact ⟨selected.1, rfl, selected.2⟩⟩
  have policyEq : schedulerBehavioral profile inputs scheduler (M.infoOf () trace) =
      (scheduler site.observation site.enabled site.nonempty).map chosen := by
    simpa only [chosen] using
      schedulerBehavioral_of_some profile inputs scheduler _ site infoEq
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (M := M) _ trace notTerminal () (fun _ _ => rfl), policyEq]
  simp only [FinDist.bind_map]
  rw [policyPlan_step_bind]
  apply FinDist.bind_congr
  intro selected _
  have ready : config.cut.Ready selected.1 :=
    (EventOrder.Cut.mem_enabled _ _).mp selected.2
  change (schedulerTransition profile inputs (some config) (some selected.1)).bind continuation = _
  rw [schedulerTransition, dite_eq_left ready, FinDist.bind_map]

/-- Reference readout of the existing graph runner, with its setup draw kept
inside the initial transition. This defines no additional graph steps. -/
def schedulerRun (profile : graph.BehavioralProfile) (inputs : FinDist graph.Inputs)
    (scheduler : graph.PublicScheduler) (fuel : Nat) :
    Option graph.Config → FinDist (Option graph.Config)
  | some config => (graph.runPlan (graph.policyPlan profile scheduler) fuel config).map some
  | none => match fuel with
    | 0 => FinDist.pure none
    | fuel + 1 => inputs.bind fun initial =>
        (graph.runPlan (graph.policyPlan profile scheduler) fuel (Config.initial initial)).map some

/-- The analysis protocol and the actual graph runner have identical state
laws, at every horizon and history. -/
theorem scheduler_runBehavioralFrom (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler) :
    ∀ fuel (history : (schedulerProtocol profile inputs).History),
      ((schedulerInformation profile inputs).runBehavioralFrom
        (fun _ => schedulerBehavioral profile inputs scheduler) fuel history).map
          ExecutionProtocol.History.state =
        schedulerRun profile inputs scheduler fuel history.state := by
  intro fuel
  induction fuel with
  | zero =>
      intro history
      simp only [InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
      cases history.state <;> simp [schedulerRun, runPlan]
  | succ fuel ih =>
      intro history
      let E := schedulerProtocol profile inputs
      let M := schedulerInformation profile inputs
      let policies := fun (_ : Unit) => schedulerBehavioral profile inputs scheduler
      by_cases terminal : E.terminal history.state
      · rw [InformationModel.runBehavioralFrom_of_terminal (M := M) _ _ terminal,
          FinDist.map_pure]
        rcases history with ⟨state, trace⟩
        cases state with
        | none => exact False.elim terminal
        | some config =>
            change config.cut.Terminal at terminal
            simp only [schedulerRun, runPlan, dite_eq_left terminal, FinDist.map_pure]
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal (M := M) _ fuel terminal,
          FinDist.map_bind]
        calc
          _ = (M.behavioralJoint policies history.trace terminal).bind fun draw =>
              (E.step history.state draw).bind
                (schedulerRun profile inputs scheduler fuel) := by
            apply FinDist.bind_congr
            intro draw _
            rw [FinDist.map_bindOnSupport]
            apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
            intro next realized
            exact ih (history.extend draw.2 realized)
          _ = _ := by
            rcases history with ⟨state, trace⟩
            cases state with
            | none =>
                rw [InformationModel.behavioralJoint_eq_pure_of_no_active (M := M) _ trace terminal
                  (fun _ => not_false), FinDist.pure_bind]
                change (inputs.map (fun initial => some (Config.initial initial))).bind _ = _
                rw [FinDist.bind_map]
                rfl
            | some config =>
                rw [scheduler_step_bind profile inputs scheduler config trace terminal]
                change _ = (graph.runPlan _ (fuel + 1) config).map some
                rw [runPlan, dite_eq_right terminal, FinDist.map_bind]
                apply FinDist.bind_congr
                intro choice _
                rw [FinDist.map_bind]
                rfl

end Vegas.EventGraph
