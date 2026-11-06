/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.CanonicalKeyLaw
import Vegas.Pending.ReactiveGraphSteps
import Vegas.EventGraph.PublicationDecision

/-! # Canonical key law across publication rounds

While every ready event is a publication, a ledger round changes the
configuration only by an accepted opening, which executes the `true` action, or
by native service: clock advances, idle expiries, and automatic completion of
defaulted owners. For a ready-independent reference that opens every active
publication, each of these preserves the canonical key law at every supported
successor, provided no active owner's ready publication has passed its
deadline.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- A publication has an owner. -/
theorem actor_of_publication {event : graph.EventId}
    (publication : (graph.outputLayout event).IsPublication) :
    ∃ owner, graph.actor? event = some owner := by
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      rw [outputEq] at publication
      exact publication.elim
  | sample payload law outputEq codeEq =>
      rw [outputEq] at publication
      exact publication.elim
  | resolve owner payload binding checks outputEq codeEq =>
      exact ⟨owner, nodeView_resolve_actor outputEq codeEq⟩

omit [DecidableEq Player] in
private theorem openAction_eq_cast_true {event : graph.EventId} {payload : L.Ty}
    (outputEq : graph.outputLayout event = .publication payload)
    (publication : (graph.outputLayout event).IsPublication) :
    EventField.openAction _ publication = cast (congrArg EventField.Action outputEq.symm) true := by
  generalize graph.outputLayout event = field at outputEq publication ⊢
  subst outputEq
  rfl

/-- A profile opens every publication of an active owner as a point mass. -/
def OpensPublications (profile : graph.BehavioralProfile) : Prop :=
  ∀ (config : graph.Config) (event : graph.EventId) (who : Player)
    (actor : graph.actor? event = some who)
    (publication : (graph.outputLayout event).IsPublication)
    (active : who ∉ config.defaulted),
    profile who event actor (graph.playerObserve who config) active =
      PMF.pure (EventField.openAction _ publication)

/-- An accepted call at a publication-only configuration preserves the
canonical key law of a ready-independent opening profile. -/
theorem handle_canonicalLaw_of_publications {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (publications : ∀ event, state.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (accepted : handle runtime state message = some next) :
    canonicalLaw profile next.config = canonicalLaw profile state.config := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      obtain ⟨_, ready, _, owner, payload, outputEq, _⟩ :=
        (handle_commitment_iff runtime state next id event candidate).mp accepted
      have publication := publications event ready
      rw [outputEq] at publication
      exact publication.elim
  | opening event candidate raw =>
      obtain ⟨ready, action, stepped, _, _, owner, payload, binding, checks, outputEq, codeEq, _,
        actionEq⟩ := handle_opening_config_step runtime state next id event candidate raw accepted
      have acting := nodeView_resolve_actor outputEq codeEq
      by_cases inactive : owner ∈ state.config.defaulted
      · exact State.canonicalLaw_of_mem_step_defaulted independent _ _ event ready owner acting
          inactive action stepped
      · apply State.canonicalLaw_of_mem_step_of_actionLaw independent _ _ event ready owner acting
          action _ stepped
        rw [actionLaw_of_actor profile state.config acting, dite_eq_right inactive,
          opens state.config event owner acting (publications event ready) inactive, actionEq,
          openAction_eq_cast_true outputEq]

/-- A native environment command at a publication-only configuration preserves
the canonical key law of a ready-independent profile at every supported
successor, when no active owner's ready publication is due. -/
theorem environmentStep_canonicalLaw_of_publications {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (publications : ∀ event, state.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, state.config.cut.Ready event → graph.actor? event = some owner →
      owner ∉ state.config.defaulted → state.WithinDeadline runtime event)
    (moved : next ∈ (environmentStep runtime state command).support) :
    canonicalLaw profile next.config = canonicalLaw profile state.config := by
  cases command with
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
            rw [environmentStep_executeSample_of_nonsample runtime state event ready
              (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
              PMF.mem_support_pure_iff] at moved
            subst next
            rfl
        | resolve owner payload binding checks outputEq codeEq =>
            rw [environmentStep_executeSample_of_nonsample runtime state event ready
              (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
              PMF.mem_support_pure_iff] at moved
            subst next
            rfl
      · rw [environmentStep_executeSample_of_not_ready runtime state event ready,
          PMF.mem_support_pure_iff] at moved
        subst next
        rfl
  | expire event =>
      rcases environmentStep_expire_config_eq_or_mem_step runtime state next event moved with
        same | ⟨ready, action, stepped⟩
      · rw [same]
      · obtain ⟨owner, acting⟩ := actor_of_publication (publications event ready)
        by_cases inactive : owner ∈ state.config.defaulted
        · exact State.canonicalLaw_of_mem_step_defaulted independent _ _ event ready owner acting
            inactive action stepped
        · have within := timely event owner ready acting inactive
          unfold State.WithinDeadline at within
          cases activated : state.activatedAt event with
          | none =>
              rw [activated] at within
              exact within.elim
          | some entered =>
              rw [activated] at within
              rw [environmentStep_expire_of_not_due runtime state event ready entered activated
                (by omega), PMF.mem_support_pure_iff] at moved
              subst next
              rfl

/-- A ledger environment step at a publication-only configuration preserves the
canonical key law of a ready-independent opening profile at every supported
successor, when no active owner's ready publication is due. -/
theorem reactive_environmentStep_canonicalLaw_of_publications
    {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ∉ execution.application.config.defaulted →
      execution.application.WithinDeadline runtime event)
    (moved : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) command).support) :
    canonicalLaw profile next.application.config =
      canonicalLaw profile execution.application.config := by
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
          cases result : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, result, Option.getD_none]
          | some after =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, result, Option.getD_some]
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call result
              rw [← drained, State.drain_canonicalLaw independent]
              exact handle_canonicalLaw_of_publications independent opens runtime _ _ _
                publications handled
  | application operation =>
      rw [PMF.support_map] at supported
      obtain ⟨state, changed, rfl⟩ := supported
      change state ∈ ((environmentStep runtime execution.application operation).map
        State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      exact (State.drain_canonicalLaw independent native).trans
        (environmentStep_canonicalLaw_of_publications independent runtime _ _ operation
          publications timely nativeMoved)

/-- **Publication rounds preserve the canonical key law.** A ledger round at a
publication-only configuration preserves the canonical key law of a
ready-independent opening profile at every supported successor, whatever the
scheduler and player policies, when no active owner's ready publication is
due. -/
theorem reactive_round_canonicalLaw_of_publications {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ∉ execution.application.config.defaulted →
      execution.application.WithinDeadline runtime event)
    (reached : next ∈
      ((runtime.reactiveApplication leaks).round scheduler players execution).support) :
    canonicalLaw profile next.application.config =
      canonicalLaw profile execution.application.config := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have middleLaw := reactive_environmentStep_canonicalLaw_of_publications independent opens
    runtime leaks execution middle command publications timely moved
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
      rw [(reactive_respond_application runtime leaks middle who response).1]
      exact middleLaw

end Vegas.EventGraphRuntime
