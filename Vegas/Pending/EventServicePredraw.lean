/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventServiceProtocol
import GameTheory.Protocol.Information

/-! # Probability presentation of bounded event service

Only the focal player, ordinary wire, and epoch order are decision sites.
Private setup, unchanged players, native application chance, and mandatory
service instructions remain transition kernels.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

inductive ServiceDecision (runtime : EventGraphRuntime graph) where
  | player (command : runtime.application.PlayerCommand)
  | wire (command : WireCommand Player)
  | order (chosen : ServiceOrder graph)

inductive ServiceDecisionSite (runtime : EventGraphRuntime graph) where
  | player (history : List runtime.application.PlayerEntry)
      (view : runtime.application.View)
  | wire (history : List runtime.application.EnvironmentEntry)
      (view : runtime.application.EnvironmentObservation)
  | order (history : List runtime.application.EnvironmentEntry)
      (view : runtime.application.EnvironmentObservation)

def serviceDecisionSite? (runtime : EventGraphRuntime graph) (focal : Player) :
    ServiceControl runtime → Option (ServiceDecisionSite runtime)
  | ⟨0, [], _⟩ => none
  | ⟨_ + 1, [], execution⟩ => some (.order execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native))
  | ⟨_, .player who :: _, execution⟩ =>
      if _same : who = focal then some (.player (execution.principalHistory focal)
        (MessageApplication.State.observe runtime.application execution.native focal)) else none
  | ⟨_, .wire :: _, execution⟩ => some (.wire execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native))
  | ⟨_, _ :: _, _⟩ => none

def serviceDecisionAvailable (runtime : EventGraphRuntime graph) :
    ServiceDecisionSite runtime → Set (ServiceDecision runtime)
  | .player _ _ => {decision | ∃ command, decision = .player command}
  | .wire _ _ => {decision | ∃ command, decision = .wire command}
  | .order _ _ => {decision | ∃ chosen, decision = .order chosen}

abbrev ServiceProtocolState (runtime : EventGraphRuntime graph) := Option (ServiceControl runtime)

def serviceProtocolSite? (runtime : EventGraphRuntime graph) (focal : Player) :
    ServiceProtocolState runtime → Option (ServiceDecisionSite runtime)
  | none => none
  | some control => runtime.serviceDecisionSite? focal control

private def serviceProtocolTransition (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player)
    (state : ServiceProtocolState runtime) (decision : Option (ServiceDecision runtime)) :
    FinDist (ServiceProtocolState runtime) :=
  match state with
  | none => inputs.map fun input => some
      { epochs := runtime.serviceEpochs
        plan := []
        execution := MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial input)) }
  | some control => match control.plan with
    | [] => match control.epochs, decision with
      | 0, _ => FinDist.pure state
      | epochs + 1, some (.order chosen) => FinDist.pure <| some
          { epochs := epochs
            plan := epochPlan chosen roster reactionRounds
            execution := control.execution }
      | _, _ => FinDist.pure state
    | instruction :: rest =>
        let next := match instruction, decision with
          | .player who, some (.player command) =>
              if _same : who = focal then runtime.application.playerStep who
                control.execution command
              else runtime.serviceStep players wire instruction control.execution
          | .wire, some (.wire command) =>
              runtime.application.environmentPolicyStep control.execution
                (WireCommand.toEnvironmentCommand runtime.application command)
          | _, _ => runtime.serviceStep players wire instruction control.execution
        next.map fun execution => some { control with plan := rest, execution := execution }

/-- Bounded service as a protocol with one analysis decision maker. Tagged
actions distinguish the three original policy interfaces. -/
abbrev serviceProtocol (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player) : ExecutionProtocol Unit where
  State := ServiceProtocolState runtime
  Action _ := ServiceDecision runtime
  init := none
  active state _ := ∃ control, state = some control ∧
    (runtime.serviceDecisionSite? focal control).isSome
  available state _ := match state with
    | none => ∅
    | some control => match runtime.serviceDecisionSite? focal control with
      | none => ∅
      | some site => runtime.serviceDecisionAvailable site
  terminal state := match state with
    | some ⟨0, [], _⟩ => True
    | _ => False
  step state choice := serviceProtocolTransition runtime inputs roster reactionRounds
    players wire focal state (choice.1 ())
  progress state notTerminal := by
    cases state with
    | none =>
        refine ⟨fun _ => none, ?_⟩
        intro i
        simp
    | some control =>
        cases siteEq : runtime.serviceDecisionSite? focal control with
        | none =>
            refine ⟨fun _ => none, ?_⟩
            intro i
            simp [siteEq]
        | some site =>
            let decision : ServiceDecision runtime := match site with
              | .player _ _ => .player .wait
              | .wire _ _ => .wire .wait
              | .order _ _ => .order (ServiceOrder.increasing graph)
            refine ⟨fun _ => some decision, ?_⟩
            intro i
            refine ⟨?_, ?_⟩
            · exact ⟨control, rfl, by simp [siteEq]⟩
            · cases site <;> simp [decision, serviceDecisionAvailable, siteEq]

private abbrev serviceSignals (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player) :
    InfoSignals (runtime.serviceProtocol inputs roster reactionRounds players wire focal) where
  PublicSignal := Option (ServiceDecisionSite runtime)
  PrivateSignal _ := Unit
  initialPublic := none
  initialPrivate _ := ()
  publicSignal event := runtime.serviceProtocolSite? focal event.target
  privateSignal _ _ := ()
  InfoState _ := Option (ServiceDecisionSite runtime)
  initInfo _ _ signal := signal
  pushInfo _ _ _ _ signal := signal

private theorem serviceSignals_infoOf (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player)
    {state : (runtime.serviceProtocol inputs roster reactionRounds players wire focal).State}
    (trace :
      (runtime.serviceProtocol inputs roster reactionRounds players wire focal).Trace state) :
    (runtime.serviceSignals inputs roster reactionRounds players wire focal).infoOf () trace =
      runtime.serviceProtocolSite? focal state := by
  cases trace with
  | start => rfl
  | extend prior joint legal realized =>
      cases state <;> rfl

/-- Information states are exactly the invocation arguments of the original
focal, wire, and order policy interfaces. -/
abbrev serviceInformation (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player) :
    InformationModel (runtime.serviceProtocol inputs roster reactionRounds players wire focal) where
  toInfoSignals := runtime.serviceSignals inputs roster reactionRounds players wire focal
  menu _ info := match info with
    | none => {decision | decision = none}
    | some site => {decision | ∃ actual, decision = some actual ∧
        actual ∈ runtime.serviceDecisionAvailable site}
  menu_adequate := by
    intro who state trace choice
    cases who
    rw [runtime.serviceSignals_infoOf inputs roster reactionRounds players wire focal trace]
    cases state with
    | none => cases choice <;> simp [LegalOption, serviceProtocolSite?]
    | some control =>
        cases siteEq : runtime.serviceDecisionSite? focal control <;>
          cases choice <;> simp [LegalOption, serviceProtocolSite?, siteEq]

private structure ServiceControlGrowth (runtime : EventGraphRuntime graph)
    (focal : Player) (before after : ServiceControl runtime) : Prop where
  focalHistory : (before.execution.principalHistory focal).length ≤
    (after.execution.principalHistory focal).length
  environmentHistory : before.execution.environmentHistory.length ≤
    after.execution.environmentHistory.length
  progress : before.progress runtime ≤ after.progress runtime
  playerStrict : ∀ history view,
    runtime.serviceDecisionSite? focal before = some (.player history view) →
      history.length < (after.execution.principalHistory focal).length
  wireStrict : ∀ history view,
    runtime.serviceDecisionSite? focal before = some (.wire history view) →
      history.length < after.execution.environmentHistory.length
  orderStrict : ∀ history view,
    runtime.serviceDecisionSite? focal before = some (.order history view) →
      history.length < after.progress runtime

private theorem serviceProtocol_step_growth (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player)
    (control : ServiceControl runtime)
    (joint : Unit → Option (ServiceDecision runtime))
    (legal : (runtime.serviceProtocol inputs roster reactionRounds players wire focal).Legal
      (some control) joint)
    (target : ServiceProtocolState runtime)
    (supported : target ∈
      ((runtime.serviceProtocol inputs roster reactionRounds players wire focal).step
        (some control) ⟨joint, legal⟩).support) :
    ∃ next, target = some next ∧ ServiceControlGrowth runtime focal control next := by
  change target ∈ (serviceProtocolTransition runtime inputs roster reactionRounds players wire
    focal (some control) (joint ())).support at supported
  rcases control with ⟨epochs, plan, execution⟩
  cases plan with
  | nil =>
      cases epochs with
      | zero =>
          simp only [serviceProtocolTransition, FinDist.mem_support_pure] at supported
          subst target
          refine ⟨_, rfl, ⟨le_rfl, le_rfl, le_rfl, ?_, ?_, ?_⟩⟩ <;>
            intro history view site <;> simp [serviceDecisionSite?] at site
      | succ epochs =>
          cases choiceEq : joint () with
          | none =>
              have inactive := legal.2 ()
              rw [choiceEq] at inactive
              simp [serviceDecisionSite?] at inactive
          | some decision =>
              have available := legal.2 ()
              rw [choiceEq] at available
              have available := available.2
              cases decision with
              | player command =>
                  simp [serviceProtocol, serviceDecisionSite?,
                    serviceDecisionAvailable] at available
              | wire command =>
                  simp [serviceProtocol, serviceDecisionSite?,
                    serviceDecisionAvailable] at available
              | order chosen =>
                  simp only [choiceEq, serviceProtocolTransition,
                    FinDist.mem_support_pure] at supported
                  subst target
                  let before : ServiceControl runtime := ⟨epochs + 1, [], execution⟩
                  let after := before.selectOrder runtime roster reactionRounds chosen
                  have strict := before.progress_selectOrder_lt runtime rfl (by simp)
                    roster reactionRounds chosen
                  refine ⟨after, rfl, ⟨le_rfl, le_rfl, strict.le, ?_, ?_, ?_⟩⟩
                  · intro history view site
                    simp [serviceDecisionSite?] at site
                  · intro history view site
                    simp [serviceDecisionSite?] at site
                  · intro history view site
                    have site' : some (ServiceDecisionSite.order execution.environmentHistory
                        (MessageApplication.State.environmentView runtime.application
                          execution.native)) =
                        some (ServiceDecisionSite.order history view) := by
                      simpa [before, serviceDecisionSite?] using site
                    have historyEq := (ServiceDecisionSite.order.inj
                      (Option.some.inj site')).1
                    rw [← historyEq]
                    simpa [before, after, ServiceControl.progress] using strict
  | cons instruction rest =>
      cases instruction with
      | player who =>
          by_cases same : who = focal
          · subst who
            cases choiceEq : joint () with
            | none =>
                have inactive := legal.2 ()
                rw [choiceEq] at inactive
                simp [serviceDecisionSite?] at inactive
            | some decision =>
                cases decision with
                | player command =>
                    simp only [choiceEq, serviceProtocolTransition,
                      FinDist.support_map] at supported
                    obtain ⟨nextExecution, step, rfl⟩ := supported
                    have focalLength := runtime.application.playerStep_history_self focal execution
                      command nextExecution step
                    have envHistory := runtime.application.playerStep_environmentHistory focal
                      execution command nextExecution step
                    let before : ServiceControl runtime :=
                      ⟨epochs, .player focal :: rest, execution⟩
                    let after : ServiceControl runtime := ⟨epochs, rest, nextExecution⟩
                    have progressEq : before.progress runtime = after.progress runtime := by
                      simp [before, after, ServiceControl.progress,
                        ServiceInstruction.isEnvironment, envHistory]
                    refine ⟨after, rfl, ⟨?_, ?_, progressEq.le, ?_, ?_, ?_⟩⟩
                    · rw [focalLength]
                      simp
                    · rw [envHistory]
                    · intro history view site
                      have site' : some (ServiceDecisionSite.player
                          (execution.principalHistory focal)
                          (MessageApplication.State.observe runtime.application execution.native
                            focal)) = some (ServiceDecisionSite.player history view) := by
                        simpa [before, serviceDecisionSite?] using site
                      have historyEq := (ServiceDecisionSite.player.inj
                        (Option.some.inj site')).1
                      rw [← historyEq]
                      rw [focalLength]
                      simp
                    · intro history view site
                      simp [serviceDecisionSite?] at site
                    · intro history view site
                      simp [serviceDecisionSite?] at site
                | wire command =>
                    have available := legal.2 ()
                    rw [choiceEq] at available
                    have available := available.2
                    simp [serviceProtocol, serviceDecisionSite?,
                      serviceDecisionAvailable] at available
                | order chosen =>
                    have available := legal.2 ()
                    rw [choiceEq] at available
                    have available := available.2
                    simp [serviceProtocol, serviceDecisionSite?,
                      serviceDecisionAvailable] at available
          · have inactive : joint () = none := by
              cases choiceEq : joint () with
              | none => rfl
              | some decision =>
                  have active := legal.2 ()
                  rw [choiceEq] at active
                  have active := active.1
                  simp [serviceDecisionSite?, same] at active
            simp only [inactive, serviceProtocolTransition,
              FinDist.support_map] at supported
            obtain ⟨nextExecution, step, rfl⟩ := supported
            have focalLength := runtime.serviceStep_focalHistory_length players wire focal
              (.player who) execution nextExecution step
            have envLength := runtime.serviceStep_environmentHistory_length players wire
              (.player who) execution nextExecution step
            let before : ServiceControl runtime := ⟨epochs, .player who :: rest, execution⟩
            let after : ServiceControl runtime := ⟨epochs, rest, nextExecution⟩
            have progressEq : before.progress runtime = after.progress runtime := by
              simp [before, after, ServiceControl.progress, ServiceInstruction.isEnvironment,
                envLength]
            refine ⟨after, rfl, ⟨?_, ?_, progressEq.le, ?_, ?_, ?_⟩⟩
            · simpa [ServiceInstruction.isFocalPlayer, same] using focalLength.ge
            · change execution.environmentHistory.length ≤
              nextExecution.environmentHistory.length
              rw [envLength]
              simp [ServiceInstruction.isEnvironment]
            · intro history view site
              simp [serviceDecisionSite?, same] at site
            · intro history view site
              simp [serviceDecisionSite?, same] at site
            · intro history view site
              simp [serviceDecisionSite?, same] at site
      | wire =>
          cases choiceEq : joint () with
          | none =>
              have inactive := legal.2 ()
              rw [choiceEq] at inactive
              simp [serviceDecisionSite?] at inactive
          | some decision =>
              cases decision with
              | player command =>
                  have available := legal.2 ()
                  rw [choiceEq] at available
                  have available := available.2
                  simp [serviceProtocol, serviceDecisionSite?,
                    serviceDecisionAvailable] at available
              | order chosen =>
                  have available := legal.2 ()
                  rw [choiceEq] at available
                  have available := available.2
                  simp [serviceProtocol, serviceDecisionSite?,
                    serviceDecisionAvailable] at available
              | wire command =>
                  simp only [choiceEq, serviceProtocolTransition, FinDist.support_map] at supported
                  obtain ⟨nextExecution, step, rfl⟩ := supported
                  have focalHistory := runtime.application.environmentStep_principalHistory
                    execution (WireCommand.toEnvironmentCommand runtime.application command)
                    nextExecution step
                  have envLength := runtime.application.environmentStep_history_length execution
                    (WireCommand.toEnvironmentCommand runtime.application command)
                    nextExecution step
                  let before : ServiceControl runtime := ⟨epochs, .wire :: rest, execution⟩
                  let after : ServiceControl runtime := ⟨epochs, rest, nextExecution⟩
                  have progressEq : before.progress runtime = after.progress runtime := by
                    simp [before, after, ServiceControl.progress, ServiceInstruction.isEnvironment,
                      envLength]
                    omega
                  refine ⟨after, rfl, ⟨?_, ?_, progressEq.le, ?_, ?_, ?_⟩⟩
                  · rw [congrFun focalHistory focal]
                  · change execution.environmentHistory.length ≤
                      nextExecution.environmentHistory.length
                    omega
                  · intro history view site
                    simp [serviceDecisionSite?] at site
                  · intro history view site
                    have site' : some (ServiceDecisionSite.wire execution.environmentHistory
                        (MessageApplication.State.environmentView runtime.application
                          execution.native)) = some (ServiceDecisionSite.wire history view) := by
                      simpa [before, serviceDecisionSite?] using site
                    have historyEq := (ServiceDecisionSite.wire.inj
                      (Option.some.inj site')).1
                    rw [← historyEq]
                    change execution.environmentHistory.length <
                      nextExecution.environmentHistory.length
                    omega
                  · intro history view site
                    simp [serviceDecisionSite?] at site
      | grant event | includeLatest event who | sample event | tick | expire event =>
          have inactive : joint () = none := by
            cases choiceEq : joint () with
            | none => rfl
            | some decision =>
                have active := legal.2 ()
                rw [choiceEq] at active
                have active := active.1
                simp [serviceDecisionSite?] at active
          simp only [serviceProtocolTransition, FinDist.support_map] at supported
          obtain ⟨nextExecution, step, rfl⟩ := supported
          have focalLength := runtime.serviceStep_focalHistory_length players wire focal _
            execution nextExecution step
          have envLength := runtime.serviceStep_environmentHistory_length players wire _
            execution nextExecution step
          refine ⟨⟨epochs, rest, nextExecution⟩, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
          · simpa [ServiceInstruction.isFocalPlayer] using focalLength.ge
          · rw [envLength]
            simp [ServiceInstruction.isEnvironment]
          · simp [ServiceControl.progress, ServiceInstruction.isEnvironment, envLength]
            omega
          · intro history view site
            simp [serviceDecisionSite?] at site
          · intro history view site
            simp [serviceDecisionSite?] at site
          · intro history view site
            simp [serviceDecisionSite?] at site

private def serviceSitePrecedes (runtime : EventGraphRuntime graph) (focal : Player)
    (site : ServiceDecisionSite runtime) (control : ServiceControl runtime) : Prop :=
  match site with
  | .player history _ => history.length < (control.execution.principalHistory focal).length
  | .wire history _ => history.length < control.execution.environmentHistory.length
  | .order history _ => history.length < control.progress runtime

private theorem ServiceControlGrowth.precedes (runtime : EventGraphRuntime graph)
    (focal : Player) {before after : ServiceControl runtime}
    (growth : ServiceControlGrowth runtime focal before after)
    (site : ServiceDecisionSite runtime)
    (precedes : serviceSitePrecedes runtime focal site before) :
    serviceSitePrecedes runtime focal site after := by
  cases site with
  | player history view => exact precedes.trans_le growth.focalHistory
  | wire history view => exact precedes.trans_le growth.environmentHistory
  | order history view => exact precedes.trans_le growth.progress

private theorem ServiceControlGrowth.active_precedes (runtime : EventGraphRuntime graph)
    (focal : Player) {before after : ServiceControl runtime}
    (growth : ServiceControlGrowth runtime focal before after)
    (site : ServiceDecisionSite runtime)
    (active : runtime.serviceDecisionSite? focal before = some site) :
    serviceSitePrecedes runtime focal site after := by
  cases site with
  | player history view => exact growth.playerStrict history view active
  | wire history view => exact growth.wireStrict history view active
  | order history view => exact growth.orderStrict history view active

private theorem active_serviceSite_not_precedes (runtime : EventGraphRuntime graph)
    (focal : Player) (control : ServiceControl runtime) (site : ServiceDecisionSite runtime)
    (active : runtime.serviceDecisionSite? focal control = some site) :
    ¬serviceSitePrecedes runtime focal site control := by
  rcases control with ⟨epochs, plan, execution⟩
  cases plan with
  | nil =>
      cases epochs with
      | zero => simp [serviceDecisionSite?] at active
      | succ epochs =>
          simp only [serviceDecisionSite?, Option.some.injEq] at active
          subst site
          simp [serviceSitePrecedes, ServiceControl.progress]
  | cons instruction rest =>
      cases instruction with
      | player who =>
          by_cases same : who = focal
          · subst who
            simp [serviceDecisionSite?] at active
            subst site
            simp [serviceSitePrecedes]
          · simp [serviceDecisionSite?, same] at active
      | wire =>
          simp only [serviceDecisionSite?, Option.some.injEq] at active
          subst site
          simp [serviceSitePrecedes]
      | grant event | includeLatest event who | sample event | tick | expire event =>
          simp [serviceDecisionSite?] at active

private theorem service_actedAt_precedes (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player)
    {state : (runtime.serviceProtocol inputs roster reactionRounds players wire focal).State}
    (trace :
      (runtime.serviceProtocol inputs roster reactionRounds players wire focal).Trace state) :
    ∀ info ∈ (runtime.serviceSignals inputs roster reactionRounds players wire focal).actedAt ()
        trace,
      ∃ control site, state = some control ∧ info = some site ∧
        serviceSitePrecedes runtime focal site control := by
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint legal realized ih =>
      intro info member
      rw [InfoSignals.actedAt] at member
      cases choiceEq : joint () with
      | none =>
          rw [choiceEq] at member
          obtain ⟨control, site, sourceEq, infoEq, precedes⟩ := ih info member
          subst source
          obtain ⟨next, targetEq, growth⟩ := runtime.serviceProtocol_step_growth inputs
            roster reactionRounds players wire focal control joint legal target realized
          exact ⟨next, site, targetEq, infoEq, growth.precedes runtime focal site precedes⟩
      | some decision =>
          have valid := legal.2 ()
          rw [choiceEq] at valid
          obtain ⟨control, rfl, active⟩ := valid.1
          cases siteEq : runtime.serviceDecisionSite? focal control with
          | none => simp [siteEq] at active
          | some currentSite =>
              obtain ⟨next, targetEq, growth⟩ := runtime.serviceProtocol_step_growth inputs
                roster reactionRounds players wire focal control joint legal target realized
              have currentInfo :
                  (runtime.serviceSignals inputs roster reactionRounds players wire focal).infoOf
                      () prior = some currentSite := by
                rw [runtime.serviceSignals_infoOf inputs roster reactionRounds players wire focal]
                simp [serviceProtocolSite?, siteEq]
              rw [choiceEq] at member
              rcases List.mem_cons.mp member with now | earlier
              · exact ⟨next, currentSite, targetEq, now.trans currentInfo,
                  growth.active_precedes runtime focal currentSite siteEq⟩
              · obtain ⟨oldControl, oldSite, sourceEq, infoEq, precedes⟩ :=
                  ih info earlier
                rw [Option.some.injEq] at sourceEq
                subst oldControl
                exact ⟨next, oldSite, targetEq, infoEq,
                  growth.precedes runtime focal oldSite precedes⟩

/-- The original focal, wire, and order interfaces never revisit a decision
site.  Setup is inactive, ordinary instructions preserve the relevant cursor,
and selecting a nonempty epoch plan strictly advances the order cursor. -/
theorem service_actsOnceWhereItMatters (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player) :
    (runtime.serviceInformation inputs roster reactionRounds players wire
      focal).ActsOnceWhereItMatters := by
  apply InformationModel.actsOnceWhereItMatters_of_actsOnce
  intro who state trace
  cases who
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint legal realized ih =>
      rw [InfoSignals.actedAt]
      cases choiceEq : joint () with
      | none => simpa [choiceEq] using ih
      | some decision =>
          simp only [List.nodup_cons]
          refine ⟨?_, ih⟩
          intro member
          obtain ⟨oldControl, oldSite, sourceEq, oldInfo, precedes⟩ :=
            runtime.service_actedAt_precedes inputs roster reactionRounds players wire focal prior
              _ member
          have valid := legal.2 ()
          rw [choiceEq] at valid
          obtain ⟨control, controlEq, active⟩ := valid.1
          rw [controlEq] at sourceEq
          rw [Option.some.injEq] at sourceEq
          subst oldControl
          cases siteEq : runtime.serviceDecisionSite? focal control with
          | none => simp [siteEq] at active
          | some currentSite =>
              have currentInfo :
                  (runtime.serviceSignals inputs roster reactionRounds players wire focal).infoOf
                      () prior = some currentSite := by
                rw [runtime.serviceSignals_infoOf inputs roster reactionRounds players wire focal]
                simp [serviceProtocolSite?, controlEq, siteEq]
              have siteSame : oldSite = currentSite :=
                Option.some.inj (oldInfo.symm.trans currentInfo)
              subst oldSite
              exact runtime.active_serviceSite_not_precedes focal control currentSite siteEq
                precedes

/-- The three live randomized interfaces as one behavioral protocol policy. -/
def serviceBehavioral (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (modelWire behaviorWire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy)
    (focal : Player) (replacement : runtime.application.PlayerPolicy) :
    (runtime.serviceInformation inputs roster reactionRounds players modelWire
      focal).BehavioralPolicy () := fun info => match info with
  | none => FinDist.pure ⟨none, rfl⟩
  | some (.player history view) =>
      (replacement history view).map fun command =>
        ⟨some (.player command), ⟨.player command, rfl, command, rfl⟩⟩
  | some (.wire history view) =>
      (behaviorWire history view).map fun command =>
        ⟨some (.wire command), ⟨.wire command, rfl, command, rfl⟩⟩
  | some (.order history view) =>
      (order history view).map fun chosen =>
        ⟨some (.order chosen), ⟨.order chosen, rfl, chosen, rfl⟩⟩

/-- Deterministic responses in the three original policy interfaces. -/
structure PureServiceResponses (runtime : EventGraphRuntime graph) where
  player : List runtime.application.PlayerEntry → runtime.application.View →
    runtime.application.PlayerCommand
  wire : List runtime.application.EnvironmentEntry →
    runtime.application.EnvironmentObservation → WireCommand Player
  order : List runtime.application.EnvironmentEntry →
    runtime.application.EnvironmentObservation → ServiceOrder graph

/-- Read the three original response functions from a pure protocol policy. -/
def pureServiceResponsesOfPolicy (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player)
    (policy :
      (runtime.serviceInformation inputs roster reactionRounds players wire focal).Policy ()) :
    PureServiceResponses runtime where
  player history view :=
    match (policy (some (.player history view))).1 with
    | some (.player command) => command
    | _ => .wait
  wire history view :=
    match (policy (some (.wire history view))).1 with
    | some (.wire command) => command
    | _ => .wait
  order history view :=
    match (policy (some (.order history view))).1 with
    | some (.order chosen) => chosen
    | _ => ServiceOrder.increasing graph

def PureServiceResponses.playerPure {runtime : EventGraphRuntime graph}
    (response : PureServiceResponses runtime) :
    runtime.application.PlayerPolicy := fun history view =>
  FinDist.pure (response.player history view)

def PureServiceResponses.wirePure {runtime : EventGraphRuntime graph}
    (response : PureServiceResponses runtime) :
    runtime.application.WirePolicy := fun history view =>
  FinDist.pure (response.wire history view)

def PureServiceResponses.orderPure {runtime : EventGraphRuntime graph}
    (response : PureServiceResponses runtime) :
    runtime.ServiceOrderPolicy := fun history view =>
  FinDist.pure (response.order history view)

private theorem serviceBehavioral_pureServiceResponsesOfPolicy
    (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player)
    (policy :
      (runtime.serviceInformation inputs roster reactionRounds players wire focal).Policy ()) :
    runtime.serviceBehavioral inputs roster reactionRounds players wire
        (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players wire focal
          policy).wirePure
        (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players wire focal
          policy).orderPure
        focal
        (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players wire focal
          policy).playerPure =
      policy.toBehavioral := by
  funext info
  cases info with
  | none =>
      apply congrArg FinDist.pure
      apply Subtype.ext
      exact (policy none).2.symm
  | some site =>
      cases site with
      | player history view =>
          let choice := policy (some (.player history view))
          cases choiceEq : choice.1 with
          | none =>
              have menu := choice.2
              simp [choice, choiceEq] at menu
          | some decision =>
              cases decision with
              | player command =>
                  simp only [serviceBehavioral, PureServiceResponses.playerPure,
                    FinDist.map_pure, InformationModel.Policy.toBehavioral]
                  rw [show policy (some (.player history view)) = choice from rfl]
                  apply congrArg FinDist.pure
                  apply Subtype.ext
                  have direct : (policy (some (.player history view))).1 =
                      some (.player command) := by
                    simpa [choice] using choiceEq
                  have extracted :
                      (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players
                        wire focal policy).player history view = command := by
                    simp only [pureServiceResponsesOfPolicy]
                    rw [direct]
                  rw [extracted, choiceEq]
              | wire command =>
                  have menu := choice.2
                  rcases menu with ⟨_, same, _, tagged⟩
                  simp only [choiceEq, Option.some.injEq] at same
                  cases same
                  cases tagged
              | order chosen =>
                  have menu := choice.2
                  rcases menu with ⟨_, same, _, tagged⟩
                  simp only [choiceEq, Option.some.injEq] at same
                  cases same
                  cases tagged
      | wire history view =>
          let choice := policy (some (.wire history view))
          cases choiceEq : choice.1 with
          | none =>
              have menu := choice.2
              simp [choice, choiceEq] at menu
          | some decision =>
              cases decision with
              | player command =>
                  have menu := choice.2
                  rcases menu with ⟨_, same, _, tagged⟩
                  simp only [choiceEq, Option.some.injEq] at same
                  cases same
                  cases tagged
              | wire command =>
                  simp only [serviceBehavioral, PureServiceResponses.wirePure,
                    FinDist.map_pure, InformationModel.Policy.toBehavioral]
                  rw [show policy (some (.wire history view)) = choice from rfl]
                  apply congrArg FinDist.pure
                  apply Subtype.ext
                  have direct : (policy (some (.wire history view))).1 =
                      some (.wire command) := by
                    simpa [choice] using choiceEq
                  have extracted :
                      (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players
                        wire focal policy).wire history view = command := by
                    simp only [pureServiceResponsesOfPolicy]
                    rw [direct]
                  rw [extracted, choiceEq]
              | order chosen =>
                  have menu := choice.2
                  rcases menu with ⟨_, same, _, tagged⟩
                  simp only [choiceEq, Option.some.injEq] at same
                  cases same
                  cases tagged
      | order history view =>
          let choice := policy (some (.order history view))
          cases choiceEq : choice.1 with
          | none =>
              have menu := choice.2
              simp [choice, choiceEq] at menu
          | some decision =>
              cases decision with
              | player command =>
                  have menu := choice.2
                  rcases menu with ⟨_, same, _, tagged⟩
                  simp only [choiceEq, Option.some.injEq] at same
                  cases same
                  cases tagged
              | wire command =>
                  have menu := choice.2
                  rcases menu with ⟨_, same, _, tagged⟩
                  simp only [choiceEq, Option.some.injEq] at same
                  cases same
                  cases tagged
              | order chosen =>
                  simp only [serviceBehavioral, PureServiceResponses.orderPure,
                    FinDist.map_pure, InformationModel.Policy.toBehavioral]
                  rw [show policy (some (.order history view)) = choice from rfl]
                  apply congrArg FinDist.pure
                  apply Subtype.ext
                  have direct : (policy (some (.order history view))).1 =
                      some (.order chosen) := by
                    simpa [choice] using choiceEq
                  have extracted :
                      (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players
                        wire focal policy).order history view = chosen := by
                    simp only [pureServiceResponsesOfPolicy]
                    rw [direct]
                  rw [extracted, choiceEq]

private theorem serviceBehavioral_choice_law (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (modelWire behaviorWire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    {state : (runtime.serviceProtocol inputs roster reactionRounds players modelWire focal).State}
    (trace : (runtime.serviceProtocol inputs roster reactionRounds players modelWire focal).Trace
      state) :
    ((runtime.serviceBehavioral inputs roster reactionRounds players modelWire behaviorWire order
      focal replacement
      ((runtime.serviceInformation inputs roster reactionRounds players modelWire focal).infoOf ()
      trace)).map Subtype.val) =
      match runtime.serviceProtocolSite? focal state with
      | none => FinDist.pure none
      | some (.player history view) => (replacement history view).map
          (fun command => some (.player command))
      | some (.wire history view) => (behaviorWire history view).map
          (fun command => some (.wire command))
      | some (.order history view) => (order history view).map
          (fun chosen => some (.order chosen)) := by
  rw [runtime.serviceSignals_infoOf inputs roster reactionRounds players modelWire focal trace]
  cases siteEq : runtime.serviceProtocolSite? focal state with
  | none => simp [serviceBehavioral]
  | some site =>
      cases site <;> rw [serviceBehavioral, FinDist.map_comp] <;> rfl

private theorem serviceBehavioral_step (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (modelWire behaviorWire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (control : ServiceControl runtime)
    (trace : (runtime.serviceProtocol inputs roster reactionRounds players modelWire focal).Trace
      (some control))
    (notTerminal : ¬
      (runtime.serviceProtocol inputs roster reactionRounds players modelWire focal).terminal
        (some control)) :
    ((runtime.serviceInformation inputs roster reactionRounds players modelWire
      focal).behavioralJoint
      (fun _ => runtime.serviceBehavioral inputs roster reactionRounds players modelWire
        behaviorWire order focal replacement) trace notTerminal).bind
        ((runtime.serviceProtocol inputs roster reactionRounds players modelWire focal).step
          (some control)) =
      (runtime.serviceControlStep roster reactionRounds
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          players focal replacement) behaviorWire order control).map some := by
  let M := runtime.serviceInformation inputs roster reactionRounds players modelWire focal
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (M := M) _ trace notTerminal () (fun _ _ => rfl), FinDist.bind_map]
  calc
    _ = ((runtime.serviceBehavioral inputs roster reactionRounds players modelWire behaviorWire
          order focal replacement (M.infoOf () trace)).map Subtype.val).bind
        (serviceProtocolTransition runtime inputs roster reactionRounds players modelWire focal
          (some control)) := by
      rw [FinDist.bind_map]
      apply FinDist.bind_congr
      intro choice _
      rfl
    _ = _ := by
      rw [runtime.serviceBehavioral_choice_law inputs roster reactionRounds players modelWire
        behaviorWire order focal replacement trace]
      cases control with
      | mk epochs plan execution =>
          cases plan with
          | nil =>
              cases epochs with
              | zero => exact False.elim (notTerminal trivial)
              | succ epochs =>
                  simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                    serviceControlStep, FinDist.map_eq_bind]
          | cons instruction rest =>
              cases instruction with
              | player who =>
                  by_cases same : who = focal
                  · subst who
                    simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                      serviceControlStep, serviceStep, MessageApplication.invoke,
                      FinDist.map_bind, FinDist.bind_map, Function.comp_def]
                  · simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                      serviceControlStep, serviceStep, MessageApplication.invoke, same,
                      FinDist.map_bind, Function.comp_def]
              | wire =>
                  simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                    serviceControlStep, serviceStep, MessageApplication.invoke,
                    MessageApplication.wireEnvironment, FinDist.map_bind, FinDist.bind_map,
                    Function.comp_def]
              | grant event =>
                  simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                    serviceControlStep, serviceStep, Function.comp_def]
              | includeLatest event owner =>
                  simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                    serviceControlStep, serviceStep, Function.comp_def]
              | sample event =>
                  simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                    serviceControlStep, serviceStep, Function.comp_def]
              | tick =>
                  simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                    serviceControlStep, serviceStep, Function.comp_def]
              | expire event =>
                  simp [serviceProtocolSite?, serviceDecisionSite?, serviceProtocolTransition,
                    serviceControlStep, serviceStep, Function.comp_def]

private def serviceControlRun (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (replacement : runtime.application.PlayerPolicy) :
    Nat → ServiceProtocolState runtime → FinDist (ServiceProtocolState runtime)
  | fuel, some control =>
      (runtime.runServiceControlSteps roster reactionRounds
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          players focal replacement) wire order fuel control).map some
  | 0, none => FinDist.pure none
  | fuel + 1, none => inputs.bind fun input =>
      (runtime.runServiceControlSteps roster reactionRounds
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          players focal replacement) wire order fuel
        { epochs := runtime.serviceEpochs
          plan := []
          execution := MessageApplication.PolicyExecution.initial runtime.application
            (MessageApplication.State.initial runtime.application (State.initial input)) }).map some

private theorem service_runBehavioralFrom (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (modelWire behaviorWire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy)
    (focal : Player) (replacement : runtime.application.PlayerPolicy) :
    ∀ fuel
      (history :
        (runtime.serviceProtocol inputs roster reactionRounds players modelWire focal).History),
      ((runtime.serviceInformation inputs roster reactionRounds players modelWire
        focal).runBehavioralFrom
        (fun _ => runtime.serviceBehavioral inputs roster reactionRounds players modelWire
          behaviorWire order focal replacement) fuel history).map
          ExecutionProtocol.History.state =
        runtime.serviceControlRun inputs roster reactionRounds players behaviorWire order focal
          replacement fuel history.state := by
  intro fuel
  induction fuel with
  | zero =>
      intro history
      rcases history with ⟨state, trace⟩
      cases state <;> simp [InformationModel.runBehavioralFrom, serviceControlRun,
        runServiceControlSteps]
  | succ fuel ih =>
      intro history
      let E := runtime.serviceProtocol inputs roster reactionRounds players modelWire focal
      let M := runtime.serviceInformation inputs roster reactionRounds players modelWire focal
      let policies := fun (_ : Unit) => runtime.serviceBehavioral inputs roster reactionRounds
        players modelWire behaviorWire order focal replacement
      by_cases terminal : E.terminal history.state
      · rw [InformationModel.runBehavioralFrom_of_terminal (M := M) policies _ terminal,
          FinDist.map_pure]
        rcases history with ⟨state, trace⟩
        cases state with
        | none => exact False.elim terminal
        | some control =>
            rcases control with ⟨epochs, plan, execution⟩
            cases epochs <;> cases plan <;>
              simp [E, serviceControlRun, runServiceControlSteps] at *
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal (M := M) policies fuel
          terminal, FinDist.map_bind]
        calc
          _ = (M.behavioralJoint policies history.trace terminal).bind fun draw =>
              (E.step history.state draw).bind
                (runtime.serviceControlRun inputs roster reactionRounds players behaviorWire order
                  focal replacement fuel) := by
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
                rw [InformationModel.behavioralJoint_eq_pure_of_no_active (M := M) policies
                  trace terminal (fun _ => by simp), FinDist.pure_bind]
                simp only [E, serviceProtocol, serviceProtocolTransition, serviceControlRun,
                  FinDist.bind_map]
            | some control =>
                dsimp only [M, E, policies]
                rw [← FinDist.bind_bind]
                rw [runtime.serviceBehavioral_step inputs roster reactionRounds players modelWire
                  behaviorWire order focal replacement control trace terminal, FinDist.bind_map]
                rcases control with ⟨epochs, plan, execution⟩
                cases epochs <;> cases plan
                · exact False.elim (terminal trivial)
                · simp [serviceControlRun, runServiceControlSteps, FinDist.map_bind]
                · simp [serviceControlRun, runServiceControlSteps, FinDist.map_bind]
                · simp [serviceControlRun, runServiceControlSteps, FinDist.map_bind]

private def serviceExecution? (runtime : EventGraphRuntime graph) :
    ServiceProtocolState runtime → Option runtime.application.PolicyExecution
  | none => none
  | some control => some control.execution

private theorem service_runBehavioral_execution (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (modelWire behaviorWire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy)
    (focal : Player) (replacement : runtime.application.PlayerPolicy) :
    let fuel := runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []
    let E := runtime.serviceProtocol inputs roster reactionRounds players modelWire focal
    let M := runtime.serviceInformation inputs roster reactionRounds players modelWire focal
    (M.runBehavioralFrom
      (fun _ => runtime.serviceBehavioral inputs roster reactionRounds players modelWire
        behaviorWire order focal replacement) (fuel + 1) E.initHistory).map
        (fun result => serviceExecution? runtime result.state) =
      ((runtime.servicedEventGame inputs roster reactionRounds behaviorWire order).play
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          players focal replacement)).map some := by
  dsimp only
  change ((runtime.serviceInformation inputs roster reactionRounds players modelWire
      focal).runBehavioralFrom
        (fun _ => runtime.serviceBehavioral inputs roster reactionRounds players modelWire
          behaviorWire order focal replacement)
        (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs [] + 1)
        (runtime.serviceProtocol inputs roster reactionRounds players modelWire
          focal).initHistory).map
      (serviceExecution? runtime ∘ ExecutionProtocol.History.state) = _
  rw [← FinDist.map_comp]
  rw [runtime.service_runBehavioralFrom inputs roster reactionRounds players modelWire
    behaviorWire order focal replacement]
  simp only [ExecutionProtocol.initHistory_state, serviceControlRun, FinDist.map_bind,
    FinDist.map_comp]
  rw [runtime.servicedEventGame_eq_evalServiceControl inputs roster reactionRounds behaviorWire
    order, FinDist.map_bind]
  apply FinDist.bind_congr
  intro input _
  have controlLaw := runtime.runServiceControlSteps_map_execution roster reactionRounds
    (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
      players focal replacement) behaviorWire order runtime.serviceEpochs []
    (MessageApplication.PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application (State.initial input)))
  rw [← controlLaw, FinDist.map_comp]
  rfl

private theorem service_runPure_execution (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (modelWire : runtime.application.WirePolicy) (focal : Player)
    (pureProfile : (i : Unit) →
      (runtime.serviceInformation inputs roster reactionRounds players modelWire focal).Policy i) :
    let fuel := runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []
    let E := runtime.serviceProtocol inputs roster reactionRounds players modelWire focal
    let M := runtime.serviceInformation inputs roster reactionRounds players modelWire focal
    let response := runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players
      modelWire focal (pureProfile ())
    (M.runFrom pureProfile (fuel + 1) E.initHistory).map
        (fun result => serviceExecution? runtime result.state) =
      ((runtime.servicedEventGame inputs roster reactionRounds response.wirePure
        response.orderPure).play
          (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
            players focal response.playerPure)).map some := by
  dsimp only
  rw [← InformationModel.runBehavioralFrom_toBehavioral]
  have policiesEq :
      (fun i => (pureProfile i).toBehavioral) =
        (fun _ => runtime.serviceBehavioral inputs roster reactionRounds players modelWire
          (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players modelWire
            focal (pureProfile ())).wirePure
          (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players modelWire
            focal (pureProfile ())).orderPure
          focal
          (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players modelWire
            focal (pureProfile ())).playerPure) := by
    funext i
    cases i
    exact (runtime.serviceBehavioral_pureServiceResponsesOfPolicy inputs roster reactionRounds
      players modelWire focal (pureProfile ())).symm
  rw [policiesEq]
  exact runtime.service_runBehavioral_execution inputs roster reactionRounds players modelWire
    (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players modelWire focal
      (pureProfile ())).wirePure
    (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players modelWire focal
      (pureProfile ())).orderPure focal
    (runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players modelWire focal
      (pureProfile ())).playerPure

/-- The focal player, wire, and adaptive order can be predrawn jointly before
private setup.  The resulting finite law is over total deterministic response
functions, while every opponent policy and every native transition kernel is
left unchanged. -/
theorem exists_pureServiceResponses_mixture (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (PureServiceResponses runtime),
      (runtime.servicedEventGame inputs roster reactionRounds wire order).play
          (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
            players focal replacement) =
        mixture.bind fun response =>
          (runtime.servicedEventGame inputs roster reactionRounds response.wirePure
            response.orderPure).play
              (Profile.update
                (sig := MessageApplication.policySignature Player runtime.application)
                players focal response.playerPure) := by
  let E := runtime.serviceProtocol inputs roster reactionRounds players wire focal
  let M := runtime.serviceInformation inputs roster reactionRounds players wire focal
  let fuel := runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []
  let history := E.initHistory
  let behavioral : (i : Unit) → M.BehavioralPolicy i := fun _ =>
    runtime.serviceBehavioral inputs roster reactionRounds players wire wire order focal
      replacement
  obtain ⟨mixed, mixedLaw⟩ :=
    InformationModel.exists_mixed_runMixedFrom_eq_runBehavioralFrom
      (M := M) (runtime.service_actsOnceWhereItMatters inputs roster reactionRounds players wire
        focal) behavioral (fuel + 1) history
  let response (pureProfile : (i : Unit) → M.Policy i) : PureServiceResponses runtime :=
    runtime.pureServiceResponsesOfPolicy inputs roster reactionRounds players wire focal
      (pureProfile ())
  let mixture : FinDist (PureServiceResponses runtime) := (FinDist.pi mixed).map response
  refine ⟨mixture, ?_⟩
  apply FinDist.map_injective (Option.some_injective runtime.application.PolicyExecution)
  rw [FinDist.map_bind]
  have behavioralExecution := runtime.service_runBehavioral_execution inputs roster
    reactionRounds players wire wire order focal replacement
  change _ = mixture.bind (fun response =>
    ((runtime.servicedEventGame inputs roster reactionRounds response.wirePure
      response.orderPure).play
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          players focal response.playerPure)).map some)
  rw [← behavioralExecution]
  change (M.runBehavioralFrom behavioral (fuel + 1) history).map
      (fun result => serviceExecution? runtime result.state) = _
  rw [← mixedLaw]
  simp only [mixture, FinDist.bind_map]
  change (M.runMixedFrom mixed (fuel + 1) history).map
      (fun result => serviceExecution? runtime result.state) =
    (FinDist.pi mixed).bind fun pureProfile =>
      ((runtime.servicedEventGame inputs roster reactionRounds
        (response pureProfile).wirePure (response pureProfile).orderPure).play
          (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
            players focal (response pureProfile).playerPure)).map some
  rw [InformationModel.runMixedFrom, FinDist.map_bind]
  apply FinDist.bind_congr
  intro pureProfile _
  exact runtime.service_runPure_execution inputs roster reactionRounds players wire focal
    pureProfile
end Vegas.EventGraphRuntime
