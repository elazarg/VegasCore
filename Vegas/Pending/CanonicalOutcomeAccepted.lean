module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.CanonicalOutcomePublication
public import Vegas.Pending.EffectiveOpening

@[expose] public section

/-! # Publication rounds when only accepted openings are timely

Effective-opening clients open a publication only when the opening would be
accepted; at a rejected opening they stay silent and the publication may
expire. Expiry withholds, which publishes a failure and defaults the owner,
exactly as the rejected opening of an always-open reference does. So a ledger
round at a publication-only configuration preserves the outcome law of an
always-open reference when only accepted openings of active owners are required
to be within their deadlines.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- An expiry at a rejected opening of an active owner preserves the outcome
law of an opening reference. -/
theorem outcomeLaw_of_rejected_expiry {Outcome : Type*} {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (read : graph.Config → Outcome)
    (keyed : ∀ left right : graph.Config, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (config next : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    {owner : Player} {payload : L.Ty} {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (rejected : openingAccepted event config.store = false)
    (active : owner ∉ config.defaulted) (action : graph.Action event)
    (member : next ∈ (config.step event ready action).support) :
    outcomeLaw profile read next = outcomeLaw profile read config := by
  have owned : graph.actor? event = some owner := nodeView_resolve_actor outputEq codeEq
  have publication : (graph.outputLayout event).IsPublication := by
    rw [outputEq]
    trivial
  let opening := EventField.openAction _ publication
  rw [step_of_opening_rejected config event ready node rejected action,
    PMF.mem_support_pure_iff] at member
  subst next
  have openedMember : config.complete event ready opening
      (cast (congrArg EventField.Value outputEq.symm) .failure) ∈
        (config.step event ready opening).support := by
    rw [step_of_opening_rejected config event ready node rejected opening]
    exact PMF.mem_support_pure_iff _ _ |>.mpr rfl
  have prescribed : actionLaw profile config event = PMF.pure opening := by
    rw [actionLaw_of_actor profile config owned, dite_eq_right active]
    exact opens config event owner owned publication active
  rw [← outcomeLaw_eq_of_canonicalLaw_eq read keyed
    (State.canonicalLaw_of_mem_step_of_actionLaw independent _ _ event ready owner owned opening
      prescribed openedMember)]
  unfold outcomeLaw
  exact runPlan_map_of_erase_invariant profile graph.canonicalScheduler read invariant _
    (Config.erase_complete_of_defaulting config event ready owner owned active action opening _
      (defaultEvent_of_failed_publication event outputEq codeEq action)
      (defaultEvent_of_failed_publication event outputEq codeEq opening))

/-- A native environment command at a publication-only configuration preserves
the outcome law of an opening reference at every supported successor, when no
active owner's ready publication with an accepted opening is due. -/
theorem environmentStep_outcomeLaw_of_accepted {Outcome : Type*}
    {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (read : graph.Config → Outcome)
    (keyed : ∀ left right : graph.Config, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (timeouts : EventTimeouts graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (publications : ∀ event, state.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, state.config.cut.Ready event → graph.actor? event = some owner →
      owner ∉ state.config.defaulted → openingAccepted event state.config.store = true →
      state.WithinDeadline timeouts event)
    (moved : next ∈ (environmentStep timeouts state command).support) :
    outcomeLaw profile read next.config = outcomeLaw profile read state.config := by
  cases command with
  | expire event =>
      rcases environmentStep_expire_config_eq_or_mem_step timeouts state next event moved with
        same | ⟨ready, action, stepped⟩
      · rw [same]
      · obtain ⟨owner', payload, binding, checks, outputEq, codeEq, node⟩ :=
          exists_resolve_of_publication (publications event ready)
        have owned := nodeView_resolve_actor outputEq codeEq
        by_cases inactive : owner' ∈ state.config.defaulted
        · exact outcomeLaw_eq_of_canonicalLaw_eq read keyed
            (State.canonicalLaw_of_mem_step_defaulted independent _ _ event ready owner' owned
              inactive action stepped)
        cases accepted : openingAccepted event state.config.store
        · exact outcomeLaw_of_rejected_expiry independent opens read keyed invariant _ _ event
            ready node accepted inactive action stepped
        · have within := timely event owner' ready owned inactive accepted
          unfold State.WithinDeadline at within
          cases activated : state.activatedAt event with
          | none =>
              rw [activated] at within
              exact within.elim
          | some entered =>
              rw [activated] at within
              rw [environmentStep_expire_of_not_due timeouts state event ready entered activated
                (by omega), PMF.mem_support_pure_iff] at moved
              subst next
              rfl
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at moved
      subst next
      rfl
  | executeSample event =>
      by_cases ready : state.config.cut.Ready event
      · cases view : nodeView graph event with
        | sample payload law outputEq codeEq =>
            have publication := publications event ready
            rw [outputEq] at publication
            exact publication.elim
        | bind owner payload outputEq codeEq =>
            rw [environmentStep_executeSample_of_nonsample timeouts state event ready
              (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
              PMF.mem_support_pure_iff] at moved
            subst next
            rfl
        | resolve owner payload binding checks outputEq codeEq =>
            rw [environmentStep_executeSample_of_nonsample timeouts state event ready
              (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
              PMF.mem_support_pure_iff] at moved
            subst next
            rfl
      · rw [environmentStep_executeSample_of_not_ready timeouts state event ready,
          PMF.mem_support_pure_iff] at moved
        subst next
        rfl

/-- A ledger environment step at a publication-only configuration preserves
the outcome law of an opening reference at every supported successor, when no
active owner's ready publication with an accepted opening is due. -/
theorem reactive_environmentStep_outcomeLaw_of_accepted {Outcome : Type*}
    {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (read : graph.Config → Outcome)
    (keyed : ∀ left right : graph.Config, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ∉ execution.application.config.defaulted →
      openingAccepted event execution.application.config.store = true →
      execution.application.WithinDeadline timeouts event)
    (moved : next ∈
      (execution.environmentStep ((reactiveApplication timeouts) leaks) command).support) :
    outcomeLaw profile read next.application.config =
      outcomeLaw profile read execution.application.config := by
  have viaKey {config : graph.Config}
      (same : canonicalLaw profile config = canonicalLaw profile execution.application.config) :
      outcomeLaw profile read config = outcomeLaw profile read execution.application.config :=
    outcomeLaw_eq_of_canonicalLaw_eq read keyed same
  unfold ReactiveApplication.Execution.environmentStep at moved
  rw [PMF.support_map] at moved
  obtain ⟨updated, supported, rfl⟩ := moved
  cases command with
  | activate who =>
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      cases found : execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
      | some message =>
          cases result : ((reactiveApplication timeouts) leaks).handle execution.application
              message with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, result, Option.getD_none]
          | some after =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, result, Option.getD_some]
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call result
              apply viaKey
              rw [← drained, State.drain_canonicalLaw independent]
              exact handle_canonicalLaw_of_publications independent opens timeouts _ _ _
                publications handled
  | application operation =>
      rw [PMF.support_map] at supported
      obtain ⟨state, changed, rfl⟩ := supported
      change state ∈ ((environmentStep timeouts execution.application operation).map
        State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      exact (outcomeLaw_eq_of_canonicalLaw_eq read keyed
        (State.drain_canonicalLaw independent native)).trans
        (environmentStep_outcomeLaw_of_accepted independent opens read keyed invariant
          timeouts _ _ operation publications timely nativeMoved)

/-- **Publication rounds preserve the outcome law when only accepted openings
are timely.** -/
theorem reactive_round_outcomeLaw_of_accepted {Outcome : Type*}
    {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (read : graph.Config → Outcome)
    (keyed : ∀ left right : graph.Config, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ∉ execution.application.config.defaulted →
      openingAccepted event execution.application.config.store = true →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈
      (((reactiveApplication timeouts) leaks).round scheduler players execution).support) :
    outcomeLaw profile read next.application.config =
      outcomeLaw profile read execution.application.config := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have middleLaw := reactive_environmentStep_outcomeLaw_of_accepted independent opens read
    keyed invariant timeouts leaks execution middle command publications timely moved
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  cases actor : command.actor? app with
  | none =>
      rw [actor] at resumed
      simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      subst next
      exact middleLaw
  | some who =>
      rw [actor] at resumed
      change next ∈ (app.invoke players who middle).support at resumed
      rw [ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, _, rfl⟩ := resumed
      rw [(reactive_respond_application timeouts leaks middle who response).1]
      exact middleLaw

end Vegas.EventGraphRuntime
