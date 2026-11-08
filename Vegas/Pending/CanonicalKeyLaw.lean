/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionPolicyLaw
import Vegas.EventGraph.SchedulerErasure

/-! # Canonical key law under native automatic completion

For a ready-independent reference profile the canonical law of the final store
and completion records can step any ready event first. Automatic completion of a
defaulted owner's ready event executes that owner's forced failure, which is the
profile's own action law there, so draining preserves the canonical key law on
every graph, without a sequential ordering premise.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A step of an owned ready event with the action the profile prescribes there
deterministically preserves the canonical key law of a ready-independent
profile. -/
theorem canonicalLaw_of_mem_step_of_actionLaw {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (config next : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (owner : Player)
    (acting : graph.actor? event = some owner) (action : graph.Action event)
    (prescribed : actionLaw profile config event = PMF.pure action)
    (member : next ∈ (config.step event ready action).support) :
    canonicalLaw profile next = canonicalLaw profile config := by
  obtain ⟨result, law⟩ := config.step_eq_pure_of_actor event ready action owner acting
  rw [law, PMF.mem_support_pure_iff] at member
  subst next
  have stepLaw : eventStep profile config event ready = PMF.pure result := by
    unfold eventStep
    rw [prescribed, PMF.pure_bind, law]
  rw [← independent.eventStep_bind_canonicalLaw _ config rfl event ready, stepLaw, PMF.pure_bind]

/-- A step of a defaulted owner's ready event preserves the canonical key law of
a ready-independent profile, whatever action it is given. -/
theorem canonicalLaw_of_mem_step_defaulted {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (config next : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (owner : Player)
    (acting : graph.actor? event = some owner) (inactive : owner ∈ config.defaulted)
    (action : graph.Action event) (member : next ∈ (config.step event ready action).support) :
    canonicalLaw profile next = canonicalLaw profile config := by
  obtain ⟨result, law⟩ := config.step_eq_pure_of_actor event ready action owner acting
  rw [law, PMF.mem_support_pure_iff] at member
  subst next
  have stepLaw : eventStep profile config event ready = PMF.pure result := by
    unfold eventStep
    rw [actionLaw_of_actor profile config acting, dite_eq_left inactive, PMF.pure_bind,
      config.step_eq_of_defaulted event ready owner acting inactive _ action, law]
  rw [← independent.eventStep_bind_canonicalLaw _ config rfl event ready, stepLaw, PMF.pure_bind]

/-- One automatic completion preserves the canonical key law of a
ready-independent profile. -/
theorem completeAutomatic_canonicalLaw {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    canonicalLaw profile (state.completeAutomatic event eligible).config =
      canonicalLaw profile state.config := by
  obtain ⟨owner, acting, inactive⟩ := eligible.owned
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  exact canonicalLaw_of_mem_step_defaulted independent _ _ event eligible.1 owner acting inactive
    action supported

/-- Bounded automatic draining preserves the canonical key law of a
ready-independent profile. -/
theorem drain_canonicalLaw {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (state : State graph) :
    canonicalLaw profile state.drain.config = canonicalLaw profile state.config :=
  drainFuel_induction (fun current => canonicalLaw profile current.config =
      canonicalLaw profile state.config)
    (fun before event eligible previous =>
      (completeAutomatic_canonicalLaw independent before event eligible).trans previous)
    state.config.remaining state rfl

/-- A probabilistic native transition may drain its automatic completions
before the canonical key law is taken. -/
theorem drain_bind_canonicalLaw {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (law : PMF (State graph)) :
    (law.map State.drain).bind (fun state => canonicalLaw profile state.config) =
      law.bind (fun state => canonicalLaw profile state.config) := by
  rw [PMF.bind_map]
  apply bind_congr_on_support _
  intro state _
  exact drain_canonicalLaw independent state

end Vegas.EventGraphRuntime.State

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A native environment command, with its automatic tail, preserves the
canonical key law of a ready-independent profile unless it expires the ready
event of an active owner. Clock advances keep the configuration, a sample
executes the chance kernel, and an expiry is either idle or completes a
defaulted owner's event. -/
theorem environmentStep_drain_bind_canonicalLaw {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (timeouts : EventTimeouts graph)
    (state : State graph) (command : EnvironmentCommand graph)
    (expiry : ∀ event, command = .expire event →
      (∀ next ∈ (environmentStep timeouts state (.expire event)).support,
        next.config = state.config) ∨
      ∃ owner, graph.actor? event = some owner ∧ owner ∈ state.config.defaulted) :
    ((environmentStep timeouts state command).map State.drain).bind
        (fun next => canonicalLaw profile next.config) =
      canonicalLaw profile state.config := by
  rw [State.drain_bind_canonicalLaw independent]
  have pointwise : (∀ next ∈ (environmentStep timeouts state command).support,
      canonicalLaw profile next.config = canonicalLaw profile state.config) →
      (environmentStep timeouts state command).bind (fun next => canonicalLaw profile next.config) =
        canonicalLaw profile state.config := by
    intro same
    rw [bind_congr_on_support _ same]
    exact PMF.bind_const _ _
  cases command with
  | advanceClock =>
      apply pointwise
      intro next member
      simp only [environmentStep, PMF.mem_support_pure_iff] at member
      subst next
      rfl
  | executeSample event =>
      by_cases ready : state.config.cut.Ready event
      · cases view : nodeView graph event with
        | sample payload law outputEq codeEq =>
            have ownerless := nodeView_sample_actor outputEq codeEq
            rw [environmentStep_executeSample_eq timeouts state event ready payload law outputEq
              codeEq view, PMF.bind_map]
            have stepLaw : eventStep profile state.config event ready =
                state.config.step event ready
                  (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) := by
              unfold eventStep
              rw [actionLaw_of_ownerless profile state.config ownerless, PMF.pure_bind,
                (graph.nodes event).action_eq_of_actor_none ownerless
                  (EventCode.actionOfActorNone (graph.nodes event) ownerless)
                  (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)]
            rw [← independent.eventStep_bind_canonicalLaw _ state.config rfl event ready, stepLaw]
            rfl
        | bind owner payload outputEq codeEq =>
            rw [environmentStep_executeSample_of_nonsample timeouts state event ready
              (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
              PMF.pure_bind]
        | resolve owner payload binding checks outputEq codeEq =>
            rw [environmentStep_executeSample_of_nonsample timeouts state event ready
              (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
              PMF.pure_bind]
      · rw [environmentStep_executeSample_of_not_ready timeouts state event ready, PMF.pure_bind]
  | expire event =>
      apply pointwise
      intro next member
      rcases expiry event rfl with idle | ⟨owner, acting, inactive⟩
      · rw [idle next member]
      · rcases environmentStep_expire_config_eq_or_mem_step timeouts state next event member with
          same | ⟨ready, action, stepped⟩
        · rw [same]
        · exact State.canonicalLaw_of_mem_step_defaulted independent _ _ event ready owner acting
            inactive action stepped

end Vegas.EventGraphRuntime
