module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.CanonicalKeyDistribution
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.EventGraph.PublicationDecision

@[expose] public section

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
/-- The opening action of a publication is the cast `true` action. -/
theorem openAction_eq_cast_true {event : graph.EventId} {payload : L.Ty}
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
theorem handle_canonicalDistribution_of_publications {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (timeouts : EventTimeouts graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (publications : ∀ event, state.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (accepted : handle timeouts state message = some next) :
    canonicalDistribution profile next.config = canonicalDistribution profile state.config := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      obtain ⟨_, ready, _, owner, payload, outputEq, _⟩ :=
        (handle_commitment_iff timeouts state next id event candidate).mp accepted
      have publication := publications event ready
      rw [outputEq] at publication
      exact publication.elim
  | opening event candidate raw =>
      obtain ⟨ready, action, stepped, _, _, owner, payload, binding, checks, outputEq, codeEq, _,
        actionEq⟩ := handle_opening_config_step timeouts state next id event candidate raw accepted
      have acting := nodeView_resolve_actor outputEq codeEq
      by_cases inactive : owner ∈ state.config.defaulted
      · exact State.canonicalDistribution_of_mem_step_defaulted independent _ _ event ready
          owner acting inactive action stepped
      · apply State.canonicalDistribution_of_mem_step_of_actionDistribution independent _ _ event
          ready owner acting action _ stepped
        rw [actionDistribution_of_actor profile state.config acting, dite_eq_right inactive,
          opens state.config event owner acting (publications event ready) inactive, actionEq,
          openAction_eq_cast_true outputEq]

/-- A native environment command at a publication-only configuration preserves
the canonical key law of a ready-independent profile at every supported
successor, when no active owner's ready publication is due. -/
theorem environmentStep_canonicalDistribution_of_publications {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (timeouts : EventTimeouts graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (publications : ∀ event, state.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, state.config.cut.Ready event → graph.actor? event = some owner →
      owner ∉ state.config.defaulted → state.WithinDeadline timeouts event)
    (moved : next ∈ (environmentStep timeouts state command).support) :
    canonicalDistribution profile next.config = canonicalDistribution profile state.config := by
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
  | expire event =>
      rcases environmentStep_expire_config_eq_or_mem_step timeouts state next event moved with
        same | ⟨ready, action, stepped⟩
      · rw [same]
      · obtain ⟨owner, acting⟩ := actor_of_publication (publications event ready)
        by_cases inactive : owner ∈ state.config.defaulted
        · exact State.canonicalDistribution_of_mem_step_defaulted independent _ _ event ready
            owner acting inactive action stepped
        · have within := timely event owner ready acting inactive
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

/-- A ledger environment step at a publication-only configuration preserves the
canonical key law of a ready-independent opening profile at every supported
successor, when no active owner's ready publication is due. -/
theorem reactive_environmentStep_canonicalDistribution_of_publications
    {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ∉ execution.application.config.defaulted →
      execution.application.WithinDeadline timeouts event)
    (moved : next ∈
      (execution.environmentStep ((reactiveApplication timeouts) leaks) command).support) :
    canonicalDistribution profile next.application.config =
      canonicalDistribution profile execution.application.config := by
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
              rw [← drained, State.drain_canonicalDistribution independent]
              exact handle_canonicalDistribution_of_publications independent opens timeouts _ _ _
                publications handled
  | application operation =>
      rw [PMF.support_map] at supported
      obtain ⟨state, changed, rfl⟩ := supported
      change state ∈ ((environmentStep timeouts execution.application operation).map
        State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      exact (State.drain_canonicalDistribution independent native).trans
        (environmentStep_canonicalDistribution_of_publications independent timeouts _ _ operation
          publications timely nativeMoved)

/-- **Publication rounds preserve the canonical key law.** A ledger round at a
publication-only configuration preserves the canonical key law of a
ready-independent opening profile at every supported successor, whatever the
scheduler and player policies, when no active owner's ready publication is
due. -/
theorem reactive_round_canonicalDistribution_of_publications {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ∉ execution.application.config.defaulted →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈
      (((reactiveApplication timeouts) leaks).round scheduler players execution).support) :
    canonicalDistribution profile next.application.config =
      canonicalDistribution profile execution.application.config := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have middleLaw := reactive_environmentStep_canonicalDistribution_of_publications independent opens
    timeouts leaks execution middle command publications timely moved
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

/-- The existing canonical runner is deterministic throughout a public-only
source interval; its endpoint is a genuine rank prefix with the same full
continuation potential. No flatness or payload-finiteness premise is needed. -/
theorem exists_publication_prefix
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    (opens : OpensPublications profile) :
    ∀ count start (origin : graph.Config), origin.cut.IsPrefix start →
      start + count ≤ graph.order.eventCount →
      (∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
        (graph.outputLayout event).IsPublication) →
      ∃ donor, graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count origin =
          PMF.pure donor ∧ donor.cut.IsPrefix (start + count) ∧
        Relation.ReflTransGen Config.Step origin donor ∧
        canonicalDistribution profile donor = canonicalDistribution profile origin := by
  intro count
  induction count with
  | zero =>
    intro start origin ordered _ _
    exact ⟨origin, rfl, by simpa only [Nat.add_zero] using ordered, .refl, rfl⟩
  | succ count ih =>
    intro start origin ordered bounded publications
    have inside : start < graph.order.eventCount := by omega
    let event : graph.EventId := ⟨start, inside⟩
    have ready : origin.cut.Ready event := ordered.ready inside
    have least (other : graph.EventId) (pending : origin.cut.Ready other) : event ≤ other := by
      apply Fin.le_iff_val_le_val.mpr
      change start ≤ other.val
      by_contra earlier
      exact pending.1 ((ordered.2 other).mpr (by omega))
    have publication := publications event le_rfl (by dsimp only [event]; omega)
    obtain ⟨owner, owned⟩ := actor_of_publication publication
    obtain ⟨action, acting⟩ : ∃ action, actionDistribution profile origin event =
      PMF.pure action := by
      by_cases inactive : owner ∈ origin.defaulted
      · exact ⟨(graph.nodes event).failureAction owner owned, by
          rw [actionDistribution_of_actor profile origin owned, dite_eq_left inactive]⟩
      · exact ⟨EventField.openAction _ publication, by
          rw [actionDistribution_of_actor profile origin owned, dite_eq_right inactive]
          exact opens origin event owner owned publication inactive⟩
    obtain ⟨next, stepLaw⟩ := origin.step_eq_pure_of_actor event ready action owner owned
    have moved : next ∈ (origin.step event ready action).support := by
      rw [stepLaw]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    have first : eventStep profile origin event ready = PMF.pure next := by
      rw [eventStep, acting, PMF.pure_bind, stepLaw]
    have nextOrdered : next.cut.IsPrefix (start + 1) := by
      rw [origin.step_cut event ready action next moved]
      exact ordered.complete inside
    obtain ⟨donor, law, donorOrdered, path, potential⟩ := ih (start + 1) next nextOrdered (by omega)
      (fun other lower upper => publications other (by omega) (by omega))
    have firstPotential := State.canonicalDistribution_of_mem_step_of_actionDistribution
      independent origin next
      event ready owner owned action acting moved
    refine ⟨donor, ?_, ?_, (Relation.ReflTransGen.single ⟨event, ready, action, moved⟩).trans
      path, potential.trans firstPotential⟩
    · rw [runPlan_canonical_succ profile count origin ready.not_terminal event ready least,
        first, PMF.pure_bind]
      exact law
    · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using donorOrdered

end Vegas.EventGraphRuntime

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A publication step that keeps all owners active executes the unique opening
prescribed by an ordinary opening profile, even when the actor is arbitrary. -/
theorem canonicalDistribution_eq_of_clear_publication_step
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    (opens : EventGraphRuntime.OpensPublications profile)
    (before after : graph.Config) (event : graph.EventId) (ready : before.cut.Ready event)
    (publication : (graph.outputLayout event).IsPublication) (action : graph.Action event)
    (moved : after ∈ (before.step event ready action).support)
    (clear : after.defaulted = ∅) :
    canonicalDistribution profile after = canonicalDistribution profile before := by
  obtain ⟨owner, owned⟩ := EventGraphRuntime.actor_of_publication publication
  have active : owner ∉ before.defaulted := by
    intro inactive
    have persists := before.defaulted_step event ready action after moved inactive
    rw [clear] at persists
    simp at persists
  obtain ⟨opened, prescribed, defaults⟩ :=
    opensDecisively_of_opens owner (profile owner)
      (fun config selected actor kind live => opens config selected owner actor kind live)
      before event ready owned publication active
  have actionEq : action = opened := by
    by_contra different
    have inactive := defaults action different after moved
    rw [clear] at inactive
    simp at inactive
  apply EventGraphRuntime.State.canonicalDistribution_of_mem_step_of_actionDistribution independent
    before after event ready owner owned action _ moved
  rw [actionDistribution_of_actor profile before owned, dite_eq_right active, actionEq]
  exact prescribed

/-- On a clear public-only graph path, ordinary-opening continuation law is
unchanged by every actual action along the path. -/
theorem canonicalDistribution_eq_of_clear_publication_path
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    (opens : EventGraphRuntime.OpensPublications profile)
    {before after : graph.Config} (path : Relation.ReflTransGen Config.Step before after)
    (clear : after.defaulted = ∅)
    (publications : ∀ event : graph.EventId, event ∉ before.cut.completed →
      event ∈ after.cut.completed → (graph.outputLayout event).IsPublication) :
    canonicalDistribution profile after = canonicalDistribution profile before := by
  revert clear publications
  induction path with
  | refl => intro _ _; rfl
  | @tail current next walked moved ih =>
    intro clear publications
    obtain ⟨event, ready, action, member⟩ := moved
    have currentClear : current.defaulted = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro owner inactive
      have persists := current.defaulted_step event ready action next member inactive
      rw [clear] at persists
      simp at persists
    have publication := publications event
      (fun old => ready.1 (Config.Step.path_completed_mono walked old))
      (by rw [current.step_cut event ready action next member];
          simp only [EventOrder.Cut.mem_complete]; exact Or.inl trivial)
    have stepLaw := canonicalDistribution_eq_of_clear_publication_step independent opens current
      next
      event ready publication action member clear
    apply stepLaw.trans (ih currentClear _)
    intro prior fresh done
    exact publications prior fresh
      (Config.Step.completed_mono ⟨event, ready, action, member⟩ done)


end Vegas.EventGraph
