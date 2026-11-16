module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.CanonicalKeyPublication
public import Vegas.EventGraph.DecisionTwin
public import Vegas.Pending.EffectiveOpening

@[expose] public section

/-! # Canonical outcome law across publication rounds

Read the canonical run of a ready-independent reference through a readout that
depends only on the final key and ignores the decisions of defaulted players.
A publication round preserves this outcome law even when an active owner's
publication expires, provided its binding failed: the expiry then publishes the
same failure as the reference's opening and defaults the owner in the same way.
So only publications whose binding holds a value must be inside their deadline.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The canonical run law of a profile from a configuration, read through `read`. -/
def outcomeLaw {Outcome : Type*} (profile : graph.BehavioralProfile)
    (read : graph.Config → Outcome) (config : graph.Config) : PMF Outcome :=
  (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) config.remaining config).map
    read

/-- A publication's binding holds a value. -/
def BindingHolds (config : graph.Config) (event : graph.EventId) : Prop :=
  match nodeView graph event with
  | .resolve _ _ binding _ _ _ => ∃ value, binding.get? config.store = some (.success value)
  | _ => True

/-- A publication's binding holds a failure. -/
def BindingFails (config : graph.Config) (event : graph.EventId) : Prop :=
  match nodeView graph event with
  | .resolve _ _ binding _ _ _ => binding.get? config.store = some .failure
  | _ => False

omit [DecidableEq Player] in
/-- A ready publication's binding holds a value or a failure. -/
theorem bindingHolds_or_fails (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (publication : (graph.outputLayout event).IsPublication) :
    BindingHolds config event ∨ BindingFails config event := by
  unfold BindingHolds BindingFails
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      have impossible := publication
      rw [outputEq] at impossible
      exact impossible.elim
  | sample payload law outputEq codeEq =>
      have impossible := publication
      rw [outputEq] at impossible
      exact impossible.elim
  | resolve owner payload binding checks outputEq codeEq =>
      have footprint := EventCode.readFields_cast outputEq (graph.nodes event)
      rw [codeEq] at footprint
      have present := binding.get?_isSome config.store
        (config.read_available ready (by
          rw [← footprint]
          exact Finset.mem_insert_self _ _))
      cases stored : binding.get? config.store with
      | none =>
          rw [stored] at present
          cases present
      | some result =>
          cases result with
          | failure => exact Or.inr stored
          | success value => exact Or.inl ⟨value, stored⟩

omit [DecidableEq Player] in
theorem BindingHolds.not_fails {config : graph.Config} {event : graph.EventId}
    (holds : BindingHolds config event) : ¬ BindingFails config event := by
  intro failed
  unfold BindingHolds at holds
  unfold BindingFails at failed
  cases view : nodeView graph event with
  | resolve owner payload binding checks outputEq codeEq =>
      rw [view] at holds failed
      obtain ⟨value, stored⟩ := holds
      change binding.get? config.store = some .failure at failed
      rw [stored] at failed
      cases failed
  | bind owner payload outputEq codeEq =>
      rw [view] at failed
      exact failed
  | sample payload law outputEq codeEq =>
      rw [view] at failed
      exact failed

omit [DecidableEq Player] in
/-- A failed binding stays failed while stored fields are kept. -/
theorem BindingFails.keep {before after : graph.Config} {event : graph.EventId}
    (kept : ∀ field value, before.store field = some value → after.store field = some value)
    (failed : BindingFails before event) : BindingFails after event := by
  unfold BindingFails at failed ⊢
  split at failed
  · exact FieldRef.get?_preserved _ _ _ kept _ failed
  · exact failed.elim

/-- A key-determined readout has the same law wherever the canonical key law is
the same. -/
theorem outcomeLaw_eq_of_canonicalLaw_eq {Outcome : Type*} {profile : graph.BehavioralProfile}
    (read : graph.Config → Outcome)
    (keyed : ∀ left right : graph.Config, runKey left = runKey right → read left = read right)
    {left right : graph.Config} (same : canonicalLaw profile left = canonicalLaw profile right) :
    outcomeLaw profile read left = outcomeLaw profile read right := by
  classical
  let key : _ → Outcome := fun value =>
    if found : ∃ config : graph.Config, runKey config = value then read (Classical.choose found)
    else read left
  have factor : read = key ∘ runKey := by
    funext config
    have found : ∃ other : graph.Config, runKey other = runKey config := ⟨config, rfl⟩
    simp only [Function.comp_apply, key, dite_eq_left found]
    exact (keyed _ _ (Classical.choose_spec found)).symm
  unfold outcomeLaw
  rw [factor, ← PMF.map_comp, ← PMF.map_comp]
  exact congrArg (PMF.map key) same

/-- An expiry at a failed binding of an active owner preserves the outcome law
of an opening reference. -/
theorem outcomeLaw_of_failed_expiry {Outcome : Type*} {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (read : graph.Config → Outcome)
    (keyed : ∀ left right : graph.Config, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (config next : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    {owner : Player} {payload : L.Ty} {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (failed : binding.get? config.store = some .failure)
    (active : owner ∉ config.defaulted) (action : graph.Action event)
    (member : next ∈ (config.step event ready action).support) :
    outcomeLaw profile read next = outcomeLaw profile read config := by
  have owned : graph.actor? event = some owner := nodeView_resolve_actor outputEq codeEq
  have publication : (graph.outputLayout event).IsPublication := by
    rw [outputEq]
    trivial
  let opening := EventField.openAction _ publication
  rw [config.step_of_binding_failed event ready outputEq codeEq failed action,
    PMF.mem_support_pure_iff] at member
  subst next
  have openedMember : config.complete event ready opening
      (cast (congrArg EventField.Value outputEq.symm) .failure) ∈
        (config.step event ready opening).support := by
    rw [config.step_of_binding_failed event ready outputEq codeEq failed opening]
    exact PMF.mem_support_pure_iff _ _ |>.mpr rfl
  have prescribed : actionLaw profile config event = PMF.pure opening := by
    rw [actionLaw_of_actor profile config owned, dite_eq_right active]
    exact opens config event owner owned publication active
  rw [← outcomeLaw_eq_of_canonicalLaw_eq read keyed
    (State.canonicalLaw_of_mem_step_of_actionLaw independent _ _ event ready owner owned opening
      prescribed openedMember)]
  exact runPlan_map_of_binding_failed profile graph.canonicalScheduler read invariant _ config
    event ready outputEq codeEq active action opening

/-- A native environment command at a publication-only configuration preserves
the outcome law of an opening reference at every supported successor, when no
active owner's ready publication with a holding binding is due. -/
theorem environmentStep_outcomeLaw_of_publications {Outcome : Type*}
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
      owner ∉ state.config.defaulted → BindingHolds state.config event →
      state.WithinDeadline timeouts event)
    (moved : next ∈ (environmentStep timeouts state command).support) :
    outcomeLaw profile read next.config = outcomeLaw profile read state.config := by
  have viaKey (same : canonicalLaw profile next.config = canonicalLaw profile state.config) :
      outcomeLaw profile read next.config = outcomeLaw profile read state.config :=
    outcomeLaw_eq_of_canonicalLaw_eq read keyed same
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
      · cases view : nodeView graph event with
        | bind owner payload outputEq codeEq =>
            have impossible := publications event ready
            rw [outputEq] at impossible
            exact impossible.elim
        | sample payload law outputEq codeEq =>
            have impossible := publications event ready
            rw [outputEq] at impossible
            exact impossible.elim
        | resolve owner payload binding checks outputEq codeEq =>
            have owned := nodeView_resolve_actor outputEq codeEq
            by_cases inactive : owner ∈ state.config.defaulted
            · exact viaKey (State.canonicalLaw_of_mem_step_defaulted independent _ _ event ready
                owner owned inactive action stepped)
            by_cases holds : ∃ value, binding.get? state.config.store = some (.success value)
            · have within := timely event owner ready owned inactive (by
                unfold BindingHolds
                rw [view]
                exact holds)
              unfold State.WithinDeadline at within
              cases activated : state.activatedAt event with
              | none =>
                  rw [activated] at within
                  exact within.elim
              | some entered =>
                  rw [activated] at within
                  rw [environmentStep_expire_of_not_due timeouts state event ready entered
                    activated (by omega), PMF.mem_support_pure_iff] at moved
                  subst next
                  rfl
            · have footprint := EventCode.readFields_cast outputEq (graph.nodes event)
              rw [codeEq] at footprint
              have present := binding.get?_isSome state.config.store
                (state.config.read_available ready (by
                  rw [← footprint]
                  exact Finset.mem_insert_self _ _))
              have failed : binding.get? state.config.store = some .failure := by
                cases stored : binding.get? state.config.store with
                | none => rw [stored] at present; cases present
                | some result =>
                    cases result with
                    | failure => rfl
                    | success value => exact (holds ⟨value, stored⟩).elim
              exact outcomeLaw_of_failed_expiry independent opens read keyed invariant _ _ event
                ready outputEq codeEq failed inactive action stepped

/-- A ledger environment step at a publication-only configuration preserves
the outcome law of an opening reference at every supported successor, when no
active owner's ready publication with a holding binding is due. -/
theorem reactive_environmentStep_outcomeLaw_of_publications {Outcome : Type*}
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
      BindingHolds execution.application.config event →
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
        (environmentStep_outcomeLaw_of_publications independent opens read keyed invariant
          timeouts _ _ operation publications timely nativeMoved)

/-- **Publication rounds preserve the outcome law.** A ledger round at a
publication-only configuration preserves the outcome law of a ready-independent
opening reference at every supported successor, whatever the scheduler and
player policies, when no active owner's ready publication with a holding
binding is due. -/
theorem reactive_round_outcomeLaw_of_publications {Outcome : Type*}
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
      BindingHolds execution.application.config event →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈
      (((reactiveApplication timeouts) leaks).round scheduler players execution).support) :
    outcomeLaw profile read next.application.config =
      outcomeLaw profile read execution.application.config := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have middleLaw := reactive_environmentStep_outcomeLaw_of_publications independent opens read
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

/-- An initial segment of the canonical executor preserves its terminal continuation law. -/
theorem runPlan_bind_outcomeLaw {Outcome : Type*} (profile : graph.BehavioralProfile)
    (read : graph.Config → Outcome) :
    ∀ count config,
      (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count config).bind
        (outcomeLaw profile read) = outcomeLaw profile read config := by
  let plan := graph.policyPlan profile graph.canonicalScheduler
  have head (config : graph.Config) (pending : ¬ config.cut.Terminal) :
      (plan config pending).bind (fun choice =>
        (config.step choice.1.1 choice.1.2 choice.2).bind (outcomeLaw profile read)) =
          outcomeLaw profile read config := by
    obtain ⟨remaining, fuel⟩ : ∃ remaining, config.remaining = remaining + 1 := by
      have nonzero : config.remaining ≠ 0 := by
        intro zero
        exact pending (config.terminal_iff_remaining_zero.mpr zero)
      exact Nat.exists_eq_succ_of_ne_zero nonzero
    unfold outcomeLaw
    conv_rhs => rw [fuel, EventGraph.runPlan, dite_eq_right pending, PMF.map_bind]
    apply bind_congr_on_support _
    intro choice _
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro next reached
    have progress := config.remaining_step choice.1.1 choice.1.2 choice.2 next reached
    rw [show next.remaining = remaining by omega]
  intro count
  induction count with
  | zero => intro config; exact PMF.pure_bind _ _
  | succ count ih =>
      intro config
      by_cases terminal : config.cut.Terminal
      · rw [EventGraph.runPlan, dite_eq_left terminal, PMF.pure_bind]
      · rw [EventGraph.runPlan, dite_eq_right terminal, PMF.bind_bind]
        calc
          _ = (plan config terminal).bind (fun choice =>
              (config.step choice.1.1 choice.1.2 choice.2).bind (outcomeLaw profile read)) := by
            apply bind_congr_on_support _
            intro choice _
            rw [PMF.bind_bind]
            exact bind_congr_on_support _ (fun next _ => ih next)
          _ = _ := head config terminal

/-- A continuation supported on empty public defaults has no current default.
This uses only the absorbing graph semantics. -/
theorem defaulted_eq_empty_of_outcomeLaw
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (clean : outcomeLaw profile Config.defaulted config = PMF.pure ∅) :
    config.defaulted = ∅ := by
  obtain ⟨final, selected⟩ := (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
    config.remaining config).support_nonempty
  have observed : final.defaulted ∈ (outcomeLaw profile Config.defaulted config).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, selected, rfl⟩
  rw [clean, PMF.mem_support_pure_iff] at observed
  have growing := Config.Step.path_defaulted_mono
    (runPlan_graph_steps (graph.policyPlan profile graph.canonicalScheduler)
      config.remaining config final selected)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro who member
  have later := growing member
  simp only [observed, Finset.notMem_empty] at later

private theorem defaultLaw_eq_of_canonicalLaw_eq {profile : graph.BehavioralProfile}
    {left right : graph.Config}
    (same : canonicalLaw profile left = canonicalLaw profile right) :
    outcomeLaw profile Config.defaulted left = outcomeLaw profile Config.defaulted right :=
  outcomeLaw_eq_of_canonicalLaw_eq Config.defaulted
    (fun _ _ equal => defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) equal)) same

/-- If an ordinary-opening continuation never defaults, every ready publication
has an accepted opening. This is a property of the semantic continuation law. -/
theorem openingAccepted_of_defaultLaw
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    (opens : OpensPublications profile) (config : graph.Config)
    (law : outcomeLaw profile Config.defaulted config = PMF.pure ∅)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (publication : (graph.outputLayout event).IsPublication) :
    openingAccepted event config.store = true := by
  have clear := defaulted_eq_empty_of_outcomeLaw profile config law
  obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
    exists_resolve_of_publication publication
  have owned := nodeView_resolve_actor outputEq codeEq
  have active : owner ∉ config.defaulted := by rw [clear]; simp
  by_contra different
  have rejected : openingAccepted event config.store = false := Bool.eq_false_iff.mpr different
  let action := cast (congrArg EventField.Action outputEq.symm) true
  let failed := config.complete event ready action
    (cast (congrArg EventField.Value outputEq.symm) .failure)
  have member : failed ∈ (config.step event ready action).support := by
    rw [step_of_opening_rejected config event ready node rejected action]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have prescribed : actionLaw profile config event = PMF.pure action := by
    rw [actionLaw_of_actor profile config owned, dite_eq_right active,
      opens config event owner owned publication active,
      openAction_eq_cast_true outputEq publication]
  have same := State.canonicalLaw_of_mem_step_of_actionLaw independent config failed event ready
    owner owned action prescribed member
  have failedClear := defaulted_eq_empty_of_outcomeLaw profile failed
    ((defaultLaw_eq_of_canonicalLaw_eq same).trans law)
  have inactive : owner ∈ failed.defaulted := by
    change owner ∈ (config.complete event ready action _).defaults.defaulted
    rw [EventGraph.Config.complete_defaults, config.completion_resolve_defaultEvent event owner
      payload binding checks outputEq codeEq true .failure, ite_eq_right active]
    simp only [PublicationResult.isFailure, ite_true, DefaultHistory.defaulted_record_some,
      Finset.mem_insert, true_or]
  rw [failedClear] at inactive
  simp at inactive

/-- With only publications ready, an environment operation either defaults the
focal owner or retains a clear ordinary-opening continuation potential. Only
foreign accepted publications require deadline protection. -/
theorem environment_publication_clear_or_focal_default
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    (opens : OpensPublications profile) (timeouts : EventTimeouts graph)
    (state next : State graph) (command : EnvironmentCommand graph) (focal : Player)
    (law : outcomeLaw profile Config.defaulted state.config = PMF.pure ∅)
    (publications : ∀ event, state.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (deadlines : ∀ event owner, state.config.cut.Ready event → graph.actor? event = some owner →
      owner ≠ focal → state.WithinDeadline timeouts event)
    (moved : next ∈ (environmentStep timeouts state command).support) :
    focal ∈ next.config.defaulted ∨
      (next.config.defaulted = ∅ ∧ canonicalLaw profile next.config =
        canonicalLaw profile state.config) := by
  classical
  by_cases failed : focal ∈ next.config.defaulted
  · exact Or.inl failed
  right
  have clear := defaulted_eq_empty_of_outcomeLaw profile state.config law
  have same : canonicalLaw profile next.config = canonicalLaw profile state.config := by
    cases command with
    | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp moved
      rfl
    | executeSample event =>
      by_cases ready : state.config.cut.Ready event
      · cases view : nodeView graph event with
        | sample payload chance outputEq codeEq =>
          have kind := publications event ready
          rw [outputEq] at kind
          exact kind.elim
        | bind owner payload outputEq codeEq =>
          rw [environmentStep_executeSample_of_nonsample timeouts state event ready
            (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
            PMF.mem_support_pure_iff] at moved
          cases moved
          rfl
        | resolve owner payload binding checks outputEq codeEq =>
          rw [environmentStep_executeSample_of_nonsample timeouts state event ready
            (fun _ _ _ _ impossible => by rw [view] at impossible; cases impossible),
            PMF.mem_support_pure_iff] at moved
          cases moved
          rfl
      · rw [environmentStep_executeSample_of_not_ready timeouts state event ready,
          PMF.mem_support_pure_iff] at moved
        cases moved
        rfl
    | expire event =>
      rcases environmentStep_expire_config_eq_or_mem_step timeouts state next event moved with
        unchanged | ⟨ready, action, stepped⟩
      · rw [unchanged]
      obtain ⟨owner, owned⟩ := actor_of_publication (publications event ready)
      by_cases sameOwner : owner = focal
      · have nextClear : next.config.defaulted = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro other inactive
          have otherActive : other ∉ state.config.defaulted := by rw [clear]; simp
          have otherOwned := state.config.step_new_default_actor next.config event ready action
            stepped other otherActive inactive
          have equal : other = owner := Option.some.inj (otherOwned.symm.trans owned)
          exact failed (sameOwner ▸ equal ▸ inactive)
        exact canonicalLaw_eq_of_clear_publication_step independent opens state.config next.config
          event ready (publications event ready) action stepped nextClear
      · have within := deadlines event owner ready owned sameOwner
        unfold State.WithinDeadline at within
        cases activated : state.activatedAt event with
        | none => rw [activated] at within; exact within.elim
        | some entered =>
          rw [activated] at within
          rw [environmentStep_expire_of_not_due timeouts state event ready entered activated
            (by omega), PMF.mem_support_pure_iff] at moved
          cases moved
          rfl
  exact ⟨defaulted_eq_empty_of_outcomeLaw profile next.config
    ((defaultLaw_eq_of_canonicalLaw_eq same).trans law), same⟩

/-- Before a focal default, a native public operation preserves the ordinary
opening potential and cannot default any honest owner with a protected deadline. -/
theorem reactive_environment_publication_clear_or_focal_default
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    (opens : OpensPublications profile) (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command) (focal : Player)
    (law : outcomeLaw profile Config.defaulted execution.application.config = PMF.pure ∅)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (deadlines : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ≠ focal →
      execution.application.WithinDeadline timeouts event)
    (moved : next ∈
      (execution.environmentStep ((reactiveApplication timeouts) leaks) command).support) :
    focal ∈ next.application.config.defaulted ∨
      (next.application.config.defaulted = ∅ ∧ canonicalLaw profile next.application.config =
        canonicalLaw profile execution.application.config) := by
  classical
  by_cases failed : focal ∈ next.application.config.defaulted
  · exact Or.inl failed
  right
  have same : canonicalLaw profile next.application.config =
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
            cases result : ((reactiveApplication timeouts) leaks).handle execution.application
                message with
            | none =>
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, result, Option.getD_none]
            | some after =>
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, result, Option.getD_some]
                obtain ⟨native, handled, drained⟩ := reactiveHandle_call result
                rw [← drained, State.drain_canonicalLaw independent]
                exact handle_canonicalLaw_of_publications independent opens timeouts _ _ _
                  publications handled
    | application operation =>
        rw [PMF.support_map] at supported
        obtain ⟨state, changed, rfl⟩ := supported
        change state ∈ ((environmentStep timeouts execution.application operation).map
          State.drain).support at changed
        obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
        rcases environment_publication_clear_or_focal_default independent opens timeouts
            execution.application native operation focal law publications deadlines nativeMoved with
          bad | ⟨_clear, same⟩
        · exfalso
          apply failed
          change focal ∈ native.drain.config.defaulted
          rw [native.drain_defaulted]
          exact bad
        · exact (State.drain_canonicalLaw independent native).trans same
  exact ⟨defaulted_eq_empty_of_outcomeLaw profile next.application.config
    ((defaultLaw_eq_of_canonicalLaw_eq same).trans law), same⟩

/-- A whole native public round either defaults the focal player or preserves
the clear ordinary-opening potential, with arbitrary client responses. -/
theorem reactive_round_publication_clear_or_focal_default
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    (opens : OpensPublications profile) (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (execution next : ((reactiveApplication timeouts) leaks).Execution) (focal : Player)
    (law : outcomeLaw profile Config.defaulted execution.application.config = PMF.pure ∅)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      (graph.outputLayout event).IsPublication)
    (deadlines : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ≠ focal →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈
      (((reactiveApplication timeouts) leaks).round scheduler players execution).support) :
    focal ∈ next.application.config.defaulted ∨
      (next.application.config.defaulted = ∅ ∧ canonicalLaw profile next.application.config =
        canonicalLaw profile execution.application.config) := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have middleLaw := reactive_environment_publication_clear_or_focal_default independent opens
    timeouts leaks execution middle command focal law publications deadlines moved
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
