module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealBlockTraffic
public import Vegas.Game.RevealServiceEffectiveTimely
public import Vegas.Pending.DrainOutputs
public import Vegas.Pending.ReactiveCompletion

@[expose] public section

/-! # Records of a block of concurrent reveals

During a block of concurrent reveals, an honest effective-opening client submits
a block reveal only when its opening is accepted, and acceptance persists while
the stored fields are kept. Hence every record the block run creates for an
honest reveal is an accepted opening, a withholding expiry of a rejected
opening, or an automatic completion.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- An accepted opening with a stored footprint stays accepted while stored
fields are kept. -/
theorem openingAccepted_keep {before after : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId}
    (kept : ∀ field value, before.store field = some value → after.store field = some value)
    (available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (before.store field).isSome)
    (accepted : openingAccepted event before.store = true) :
    (∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (after.store field).isSome) ∧ openingAccepted event after.store = true := by
  have agree : Store.AgreeOn after.store before.store
      ((serviceGraph setup mode).nodes event).readFields := by
    intro field read
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field read)
    rw [kept field value stored, stored]
  refine ⟨fun field read => ?_, by rw [openingAccepted_congr event agree, accepted]⟩
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field read)
  rw [kept field value stored]
  rfl

/-- Every submission of an honest owner for a block reveal names an accepted
opening with a stored footprint. -/
def HonestBlockSubmissions (who : Player) (start finish : Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution) : Prop :=
  ∀ owner, owner ≠ who → ∀ entry ∈ execution.logs owner,
    ∀ event : (serviceGraph setup mode).EventId,
    start ≤ event.val → event.val < finish →
    (submittedEvent? (serviceTimeouts setup mode duration)) leaks entry.action = some event →
    (∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (execution.application.config.store field).isSome) ∧
      openingAccepted event execution.application.config.store = true

/-- At the block start no response has submitted a block reveal, since none
was seen ready. -/
theorem honestBlockSubmissions_start (who : Player) (start finish : Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (atTurn : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks execution owner)
    (untouched : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → Untouched setup leaks event execution) :
    HonestBlockSubmissions who start finish execution := by
  intro owner different entry member event early late submitted
  exact (untouched event early late owner entry member
    (entry.beforeView.application.publicView.ownTurn?_spec owner event
      (atTurn owner different entry member event submitted)).1).elim

/-- **Honest block submissions persist.** A round inside an unfinished block
keeps every honest owner's block submissions accepted, when honest clients open
a reveal exactly when its opening is accepted. -/
theorem honestBlockSubmissions_round {horizon remaining : Nat}
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (deviation : (serviceApplication setup mode duration leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (current next : (serviceApplication setup mode duration leaks).Execution)
    (trace : ((serviceApplication setup mode duration leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩))
    (inside : InBlock start finish current.application.config)
    (running : ¬ BlockDone finish current.application.config)
    (valid : HonestBlockSubmissions who start finish current)
    (reached : next ∈ ((serviceApplication setup mode duration leaks).round scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation) current).support) :
    HonestBlockSubmissions who start finish next := by
  let app := serviceApplication setup mode duration leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall current middle command moved
  have keptMiddle := (keepsStore_step (serviceTimeouts setup mode duration) leaks).environmentStep
    current middle command moved
  have middleValid : HonestBlockSubmissions who start finish middle := by
    intro owner different entry member event early late submitted
    rw [recallEq] at member
    obtain ⟨available, accepted⟩ := valid owner different entry member event early late submitted
    exact openingAccepted_keep keptMiddle available accepted
  rcases cases with ⟨_, rfl⟩ | ⟨actor, active, response, chosen, rfl⟩
  · exact middleValid
  have kept := (keepsStore_step (serviceTimeouts setup mode duration) leaks).respond middle actor
    response
  intro owner different entry member event early late submitted
  by_cases same : owner = actor
  · subst actor
    obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle owner response
    rw [recalled] at member
    rcases List.mem_append.mp member with old | fresh
    · obtain ⟨available, accepted⟩ := middleValid owner different entry old event early late
        submitted
      exact openingAccepted_keep kept available accepted
    obtain rfl := List.mem_singleton.mp fresh
    have commandEq : command = .activate owner := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst commandEq
    have appEq := activation_application setup leaks current middle owner moved
    obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
      scheduler remaining current middle (.activate owner) trace selected moved
    rw [active] at middleTrace
    have facts := legalFacts setup leaks horizon scheduler _ middleTrace
    have follows : Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
        turns (firstTurnTiming setup turns mode) reference) who deviation owner =
        serviceReferenceTurnPolicy setup mode duration leaks bound turns
          (firstTurnTiming setup turns mode) reference owner := Function.update_of_ne different _ _
    rw [follows] at chosen
    have middlePublications : ∀ query, middle.application.config.cut.Ready query →
        ((serviceGraph setup mode).outputLayout query).IsPublication := by
      intro query ready
      rw [appEq] at ready
      have bounded := shaped _ inside running query ready
      exact publications query bounded.1 bounded.2
    obtain ⟨ready, _, accepted⟩ := honest_block_submits_accepted bound turns reference decides
      middle owner facts.quiescent middlePublications response chosen event submitted
    exact openingAccepted_keep kept (fun field read =>
      middle.application.config.read_available ready read) accepted
  · rw [app.respond_recall_other middle actor owner same response] at member
    obtain ⟨available, accepted⟩ := middleValid owner different entry member event early late
      submitted
    exact openingAccepted_keep kept available accepted

/-- An honest block reveal completed by its owner's accepted opening. -/
def HonestOpened (who : Player) (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) : Prop :=
  ∃ (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
    owner ≠ who ∧ nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq ∧
    (∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (config.store field).isSome) ∧
    openingAccepted event config.store = true ∧
    completionOf config event =
      some ⟨event, some (cast (congrArg EventField.Action outputEq.symm) true), none⟩ ∧
    config.outputs event = (EventCode.resolveOutput? binding checks true config.store).map
      (cast (congrArg EventField.Value outputEq.symm))

/-- An honest block reveal whose rejected opening expired. -/
def HonestExpired (who : Player) (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) : Prop :=
  ∃ (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
    owner ≠ who ∧ nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq ∧
    (∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (config.store field).isSome) ∧
    openingAccepted event config.store = false ∧
    completionOf config event =
      some ⟨event, some (cast (congrArg EventField.Action outputEq.symm) false), some owner⟩ ∧
    config.outputs event =
      some (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.failure))

/-- **The block's records.** Every event completed since `origin` was completed
automatically for a defaulted owner, or is a block reveal of the deviator, an
honest accepted opening, or an honest expired rejected opening. -/
def BlockRecordsSound (who : Player) (start finish : Nat)
    (origin current : (serviceGraph setup mode).Config) : Prop :=
  ∀ event : (serviceGraph setup mode).EventId, event ∉ origin.cut.completed →
    event ∈ current.cut.completed →
    (completionOf current event = some ⟨event, none, none⟩ ∧
      current.outputs event = failureOutput event ∧
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧
        owner ∈ current.defaulted) ∨
    (start ≤ event.val ∧ event.val < finish ∧
      ((serviceGraph setup mode).actor? event = some who ∨ HonestOpened who current event ∨
        HonestExpired who current event))

/-- A completed event keeps its output along a graph path. -/
theorem outputs_path {before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    {event : (serviceGraph setup mode).EventId} (done : event ∈ before.cut.completed) :
    after.outputs event = before.outputs event := by
  cases outputEq : before.outputs event with
  | none =>
      exact (Option.not_isSome_iff_eq_none.mpr outputEq
        ((before.output_available event).mpr done)).elim
  | some value => exact Config.Step.path_store_of_some path (.inr event) value outputEq

/-- A resolution's output keeps its value once its footprint is stored. -/
theorem resolveOutput_keep {before after : (serviceGraph setup mode).Config}
    (kept : ∀ field value, before.store field = some value → after.store field = some value)
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (before.store field).isSome) (disclose : Bool) :
    EventCode.resolveOutput? binding checks disclose after.store =
      EventCode.resolveOutput? binding checks disclose before.store := by
  have footprint := EventCode.readFields_cast outputEq ((serviceGraph setup mode).nodes event)
  rw [codeEq] at footprint
  apply EventCode.resolveOutput?_congr
  intro field member
  have read : field ∈ ((serviceGraph setup mode).nodes event).readFields := by
    rw [← footprint]
    exact member
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field read)
  rw [kept field value stored, stored]

/-- Block records persist along graph paths. -/
theorem BlockRecordsSound.path {who : Player} {start finish : Nat}
    {origin before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    (sound : BlockRecordsSound who start finish origin before) :
    ∀ event, event ∉ origin.cut.completed → event ∈ before.cut.completed →
      (completionOf after event = some ⟨event, none, none⟩ ∧
        after.outputs event = failureOutput event ∧
        ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧
          owner ∈ after.defaulted) ∨
      (start ≤ event.val ∧ event.val < finish ∧
        ((serviceGraph setup mode).actor? event = some who ∨ HonestOpened who after event ∨
          HonestExpired who after event)) := by
  intro event fresh done
  have kept : ∀ field value, before.store field = some value → after.store field = some value :=
    fun field value stored => Config.Step.path_store_of_some path field value stored
  rcases sound event fresh done with ⟨recorded, output, owner, acting, inactive⟩ |
    ⟨early, late, owned | opened | expired⟩
  · left
    refine ⟨Config.Step.path_completionOf_of_some path event _ recorded, ?_,
      owner, acting, Config.Step.path_defaulted_mono path inactive⟩
    have stored := kept (.inr event)
    cases outputEq : before.outputs event with
    | none =>
        exact (Option.not_isSome_iff_eq_none.mpr outputEq
          ((before.output_available event).mpr done)).elim
    | some value =>
        have later := stored value outputEq
        change after.outputs event = some value at later
        rw [later, ← outputEq, output]
  · exact Or.inr ⟨early, late, Or.inl owned⟩
  · obtain ⟨owner, payload, binding, checks, outputEq, codeEq, different, node, available,
      accepted, recorded, stored⟩ := opened
    obtain ⟨availableAfter, acceptedAfter⟩ := openingAccepted_keep kept available accepted
    exact Or.inr ⟨early, late, Or.inr (Or.inl ⟨owner, payload, binding, checks, outputEq, codeEq,
      different, node, availableAfter, acceptedAfter,
      Config.Step.path_completionOf_of_some path event _ recorded, by
        rw [outputs_path path done, stored,
          resolveOutput_keep kept (outputEq := outputEq) codeEq available]⟩)⟩
  · obtain ⟨owner, payload, binding, checks, outputEq, codeEq, different, node, available,
      rejected, recorded, stored⟩ := expired
    have rejectedAfter := (OpeningRejected.keep (setup := setup) kept ⟨available, rejected⟩)
    exact Or.inr ⟨early, late, Or.inr (Or.inr ⟨owner, payload, binding, checks, outputEq, codeEq,
      different, node, rejectedAfter.1, rejectedAfter.2,
      Config.Step.path_completionOf_of_some path event _ recorded, by
        rw [outputs_path path done, stored]⟩)⟩

/-- A record a drain appends is silent, for a newly completed event storing its
failure. -/
theorem drainRecord_of_not_mem (native : EventGraphRuntime.State (serviceGraph setup mode))
    (record : (serviceGraph setup mode).Completion) (primary : record ∉ native.config.history)
    (present : record ∈ native.drain.config.history) :
    record.decision = none ∧ record.defaultEvent = none ∧
      record.event ∉ native.config.cut.completed ∧
      native.drain.config.outputs record.event = failureOutput record.event ∧
      ∃ owner, (serviceGraph setup mode).actor? record.event = some owner ∧
        owner ∈ native.drain.config.defaulted := by
  obtain ⟨silent, quiet, owner, acting, inactive⟩ :=
    native.drain_new_completion record primary present
  have notDone : record.event ∉ native.config.cut.completed := by
    intro done
    obtain ⟨other, otherMember, otherEvent⟩ := List.mem_map.mp
      ((native.config.history_exact record.event).mpr done)
    obtain ⟨extra, extended⟩ :=
      Config.Step.path_history_prefix native.drain_graph_steps
    have otherDrained : other ∈ native.drain.config.history := by
      rw [← extended]
      exact List.mem_append_left _ otherMember
    have same := List.inj_on_of_nodup_map native.drain.config.history_nodup otherDrained
      present otherEvent
    exact primary (same ▸ otherMember)
  exact ⟨silent, quiet, notDone, native.drain_outputs record.event notDone (by
    rw [← native.drain.config.history_exact]
    exact List.mem_map.mpr ⟨record, present, rfl⟩),
    owner, acting, Config.Step.path_defaulted_mono native.drain_graph_steps inactive⟩

/-- A record new after one graph step and a drain is the step's completion, or
an automatic completion of a newly completed event storing its failure. -/
theorem newRecord_step_drain (config : (serviceGraph setup mode).Config)
    (native : EventGraphRuntime.State (serviceGraph setup mode))
    (event : (serviceGraph setup mode).EventId) (ready : config.cut.Ready event)
    (action : (serviceGraph setup mode).Action event)
    (member : native.config ∈ (config.step event ready action).support)
    (record : (serviceGraph setup mode).Completion) (fresh : record ∉ config.history)
    (present : record ∈ native.drain.config.history) :
    (record ∈ native.config.history ∧ ∃ value, record = EventGraph.completion
      (serviceGraph setup mode) event (config.actualDecision event action) value) ∨
    (record.decision = none ∧ record.defaultEvent = none ∧
      record.event ∉ native.config.cut.completed ∧
      native.drain.config.outputs record.event = failureOutput record.event ∧
      ∃ owner, (serviceGraph setup mode).actor? record.event = some owner ∧
        owner ∈ native.drain.config.defaulted) := by
  by_cases primary : record ∈ native.config.history
  · left
    refine ⟨primary, ?_⟩
    obtain ⟨value, _, history⟩ := config.step_completion event ready action native.config member
    rw [history] at primary
    exact ⟨value, List.mem_singleton.mp ((List.mem_append.mp primary).resolve_left fresh)⟩
  · exact Or.inr (drainRecord_of_not_mem native record primary present)

/-- An automatic record of an event is its silent record. -/
theorem completionOf_of_silent {config : (serviceGraph setup mode).Config}
    {record : (serviceGraph setup mode).Completion} (present : record ∈ config.history)
    (silent : record.decision = none) (quiet : record.defaultEvent = none) :
    completionOf config record.event = some ⟨record.event, none, none⟩ := by
  rw [(completionOf_eq_some_iff config record.event record).mpr ⟨present, rfl⟩]
  obtain ⟨event, decision, defaultEvent⟩ := record
  simp only at silent quiet
  subst silent quiet
  rfl

/-- An accepted opening's resolution publishes a value. -/
theorem resolveOutput_of_accepted {event : (serviceGraph setup mode).EventId} {owner : Player}
    {payload : L.Ty} {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    {store : EventGraph.Store (serviceGraph setup mode).layout}
    (accepted : openingAccepted event store = true) :
    ∃ value, EventCode.resolveOutput? binding checks true store = some (.success value) := by
  unfold openingAccepted at accepted
  rw [node] at accepted
  dsimp only at accepted
  cases result : EventCode.resolveOutput? binding checks true store with
  | none => rw [result] at accepted; cases accepted
  | some output =>
      cases output with
      | success value => exact ⟨value, rfl⟩
      | failure => rw [result] at accepted; cases accepted

/-- An active owner's resolution step completes with its deterministic output. -/
theorem resolve_step_eq {config : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} (ready : config.cut.Ready event) {owner : Player}
    {payload : L.Ty} {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (active : owner ∉ config.defaulted)
    (disclose : Bool) (output : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks disclose config.store = some output) :
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) disclose) =
      PMF.pure (config.complete event ready (cast (congrArg EventField.Action outputEq.symm)
        disclose) (cast (congrArg EventField.Value outputEq.symm) output)) := by
  have effective : (EventCode.resolve owner payload binding checks).effectiveAction
      config.defaulted disclose = disclose := by
    simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right active]
  rw [config.step_eq_map_of_code event ready outputEq (.resolve owner payload binding checks)
    codeEq disclose (PMF.pure output) (by rw [effective, EventCode.resolve_eval?, resolved]; rfl),
    PMF.pure_map]

/-- An active owner's resolution record carries its disclosure, and names the
owner as defaulting exactly when the output fails. -/
theorem completion_resolve_eq (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (active : owner ∉ config.defaulted) (disclose : Bool)
    (output : PublicationResult (L.Val payload)) :
    EventGraph.completion (serviceGraph setup mode) event
        (config.actualDecision event (cast (congrArg EventField.Action outputEq.symm) disclose))
        (cast (congrArg EventField.Value outputEq.symm) output) =
      ⟨event, some (cast (congrArg EventField.Action outputEq.symm) disclose),
        if output.isFailure then some owner else none⟩ := by
  have quiet := config.completion_resolve_defaultEvent event owner payload binding checks
    outputEq codeEq disclose output
  rw [ite_eq_right active] at quiet
  have decided := config.actualDecision_of_active event owner
    (nodeView_resolve_actor outputEq codeEq) active
    (cast (congrArg EventField.Action outputEq.symm) disclose)
  rw [← quiet]
  unfold EventGraph.completion
  rw [decided]

/-- **The block's records persist.** A round inside an unfinished block keeps
every record since `origin` classified, when honest clients open a reveal
exactly when its opening is accepted. -/
theorem blockRecordsSound_round {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (deviation : (serviceApplication setup mode duration leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (origin : (serviceGraph setup mode).Config)
    (current next : (serviceApplication setup mode duration leaks).Execution)
    (supported : current ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      current.environmentRecall.length).support)
    (bounded : current.environmentRecall.length ≤ horizon)
    (inside : InBlock start finish current.application.config)
    (running : ¬ BlockDone finish current.application.config)
    (submissions : HonestBlockSubmissions who start finish current)
    (sound : BlockRecordsSound who start finish origin current.application.config)
    (reached : next ∈ ((serviceApplication setup mode duration leaks).round scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation) current).support) :
    BlockRecordsSound who start finish origin next.application.config := by
  classical
  let app := serviceApplication setup mode duration leaks
  let timeouts := serviceTimeouts setup mode duration
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players current.environmentRecall.length bounded current supported
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have signed := signedCommitments_history timeouts leaks (serviceInitialLaw setup mode)
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have nextConfig : next.application.config = middle.application.config := by
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · rfl
    · exact (reactive_respond_application timeouts leaks middle actor response).1
  rw [nextConfig]
  have path : Relation.ReflTransGen Config.Step current.application.config
      middle.application.config :=
    ((reactiveApplication_graphSteps timeouts) leaks).environmentStep current middle command moved
  have keptMiddle : ∀ field value, current.application.config.store field = some value →
      middle.application.config.store field = some value :=
    fun field value stored => Config.Step.path_store_of_some path field value stored
  intro event fresh done
  by_cases old : event ∈ current.application.config.cut.completed
  · exact BlockRecordsSound.path path sound event fresh old
  obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp
    ((completionOf_isSome_iff middle.application.config event).mpr done)
  obtain ⟨present, recordEvent⟩ :=
    (completionOf_eq_some_iff middle.application.config event record).mp recorded
  have newRecord : record ∉ current.application.config.history := fun inside =>
    old ((current.application.config.history_exact event).mp
      (List.mem_map.mpr ⟨record, inside, recordEvent⟩))
  -- an automatic completion of the drain
  have silentCase (native : EventGraphRuntime.State (serviceGraph setup mode))
      (drained : native.drain.config = middle.application.config)
      (silent : record.decision = none) (quiet : record.defaultEvent = none)
      (notDone : record.event ∉ native.config.cut.completed)
      (output : native.drain.config.outputs record.event = failureOutput record.event)
      (drainOwner : ∃ owner, (serviceGraph setup mode).actor? record.event = some owner ∧
        owner ∈ native.drain.config.defaulted) :
      (completionOf middle.application.config event = some ⟨event, none, none⟩ ∧
        middle.application.config.outputs event = failureOutput event ∧
        ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧
          owner ∈ middle.application.config.defaulted) ∨
      (start ≤ event.val ∧ event.val < finish ∧
        ((serviceGraph setup mode).actor? event = some who ∨
          HonestOpened who middle.application.config event ∨
          HonestExpired who middle.application.config event)) := by
    left
    subst recordEvent
    refine ⟨completionOf_of_silent present silent quiet, ?_, ?_⟩
    · rw [← drained]
      exact output
    · rw [← drained]
      exact drainOwner
  -- the step's own completion of a ready block reveal
  have readyCase (ready : current.application.config.cut.Ready event) :
      start ≤ event.val ∧ event.val < finish := shaped _ inside running event ready
  have follows (owner : Player) (different : owner ≠ who) : players owner =
      serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference owner := Function.update_of_ne different _ _
  cases command with
  | activate actor =>
      have same := activation_application setup leaks current middle actor moved
      rw [same] at done
      exact (old done).elim
  | wait =>
      obtain ⟨updated, supported', rfl⟩ := PMF.support_map .. ▸ moved
      cases (PMF.mem_support_pure_iff _ _).mp supported'
      exact (old done).elim
  | «include» id =>
      obtain ⟨updated, supported', rfl⟩ := PMF.support_map .. ▸ moved
      cases (PMF.mem_support_pure_iff _ _).mp supported'
      cases found : current.network.lookup id with
      | none =>
          exact (old (by simpa only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found] using done)).elim
      | some message =>
          have pending := List.mem_of_find?_eq_some found
          cases accepted : app.handle current.application message with
          | none =>
              have unchanged : (current.includePending app id).application =
                  current.application := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none]
              exfalso
              apply old
              change event ∈ (current.includePending app id).application.config.cut.completed
                at done
              rw [unchanged] at done
              exact done
          | some after =>
              have applicationEq : (current.includePending app id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
              have middleDrain : native.drain.config =
                  ({ current.includePending app id with environmentRecall :=
                    current.environmentRecall ++ [⟨current.observeEnvironment app,
                      .include id⟩] } : app.Execution).application.config := by
                change native.drain.config = (current.includePending app id).application.config
                rw [applicationEq, drained]
              rw [← middleDrain] at present
              cases call : message.payload.call with
              | malformed raw =>
                  rw [call] at handled
                  simp [handle] at handled
              | commitment named candidate =>
                  rw [call] at handled
                  obtain ⟨_, readyNamed, _, owner, payload, outputEq, codeEq, _⟩ :=
                    (handle_commitment_iff timeouts current.application native message.id named
                      candidate).mp handled
                  have bounds := shaped _ inside running named readyNamed
                  have publication := publications named bounds.1 bounds.2
                  rw [outputEq] at publication
                  exact publication.elim
              | opening named candidate raw =>
                  rw [call] at handled
                  obtain ⟨readyNamed, action, member, _, _, owner, payload, binding, checks,
                    outputEq, codeEq, node, actionEq⟩ := handle_opening_config_step timeouts
                    current.application native message.id named candidate raw handled
                  rcases newRecord_step_drain current.application.config native named readyNamed
                      action member record newRecord present with
                    ⟨primary, value, recordEq⟩ | ⟨silent, quiet, notDone, output, drainOwner⟩
                  · have eventEq : event = named := by rw [← recordEvent, recordEq]; rfl
                    subst eventEq
                    have bounds := readyCase readyNamed
                    refine Or.inr ⟨bounds.1, bounds.2, ?_⟩
                    have owned := nodeView_resolve_actor outputEq codeEq
                    obtain ⟨other, otherNamed, senderActor⟩ :=
                      handle_event_actor timeouts current.application native _ handled
                    have otherEq : other = event := by
                      simpa [Payload.event?] using otherNamed.symm
                    subst otherEq
                    have senderOwner : message.sender = owner :=
                      Option.some.inj (senderActor.symm.trans owned)
                    by_cases isWho : owner = who
                    · exact Or.inl (isWho ▸ owned)
                    right
                    left
                    have active : owner ∉ current.application.config.defaulted :=
                      current.application.active_of_ready_owned facts.quiescent readyNamed owned
                    obtain ⟨entry, entryMember, material, _, emitted, _⟩ :=
                      facts.provenance.pending message pending
                    obtain ⟨_, material', transmitted, packet⟩ :=
                      signed.emissions message.sender entry entryMember message emitted
                    have submitted : (submittedEvent? timeouts) leaks entry.action = some other
                      := by
                      simp only [EventGraphRuntime.submittedEvent?, transmitted]
                      rw [← packet, call]
                      rfl
                    rw [senderOwner] at entryMember
                    obtain ⟨available, acceptedNow⟩ := submissions owner isWho entry entryMember
                      other bounds.1 bounds.2 submitted
                    obtain ⟨availableMiddle, acceptedMiddle⟩ :=
                      openingAccepted_keep keptMiddle available acceptedNow
                    obtain ⟨opened, resolved⟩ := resolveOutput_of_accepted node acceptedNow
                    rw [actionEq, resolve_step_eq readyNamed outputEq codeEq active true
                      (.success opened) resolved, PMF.mem_support_pure_iff] at member
                    rw [member, Config.complete_history] at primary
                    have recordExact :=
                      List.mem_singleton.mp ((List.mem_append.mp primary).resolve_left newRecord)
                    have nativeOutput : native.config.outputs other =
                        some (cast (congrArg EventField.Value outputEq.symm)
                          (PublicationResult.success opened)) := by
                      rw [member]
                      exact Config.complete_output_same _ _ _ _ _
                    have stored := Config.Step.path_store_of_some native.drain_graph_steps
                      (.inr other) _ nativeOutput
                    change native.drain.config.outputs other = _ at stored
                    rw [middleDrain] at stored
                    refine ⟨owner, payload, binding, checks, outputEq, codeEq, isWho, node,
                      availableMiddle, acceptedMiddle, ?_, ?_⟩
                    · rw [recorded]
                      exact congrArg some (recordExact.trans (completion_resolve_eq _ other
                        outputEq codeEq active true (.success opened)))
                    · rw [stored,
                        resolveOutput_keep keptMiddle (outputEq := outputEq) codeEq available,
                        resolved]
                      rfl
                  · exact silentCase native middleDrain silent quiet notDone output drainOwner
  | application operation =>
      obtain ⟨updated, supported', rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported'
      change state ∈ ((EventGraphRuntime.environmentStep timeouts current.application
        operation).map EventGraphRuntime.State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      rcases completionStep_environmentStep timeouts current.application native operation
          nativeMoved with ⟨same, _, _⟩ | ⟨stepped, readyStepped, action, member, _, _⟩
      · have fresh' : record ∉ native.config.history := by rw [same]; exact newRecord
        obtain ⟨silent, quiet, notDone, output, drainOwner⟩ :=
          drainRecord_of_not_mem native record fresh' present
        exact silentCase native rfl silent quiet notDone output drainOwner
      rcases newRecord_step_drain current.application.config native stepped readyStepped action
          member record newRecord present with
        ⟨primary, value, recordEq⟩ | ⟨silent, quiet, notDone, output, drainOwner⟩
      · subst recordEvent
        have steppedEq : stepped = record.event := by rw [recordEq]; rfl
        subst steppedEq
        have bounds := readyCase readyStepped
        refine Or.inr ⟨bounds.1, bounds.2, ?_⟩
        obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
          exists_resolve_of_publication (publications record.event bounds.1 bounds.2)
        have owned := nodeView_resolve_actor outputEq codeEq
        by_cases isWho : owner = who
        · exact Or.inl (isWho ▸ owned)
        rcases native_new_completion_cases timeouts current.application native operation
            nativeMoved record newRecord primary with
          ⟨_, entered, activated, due, expiredAction, expiredValue, expired, expiredEq⟩ |
            ownerless
        · have active : owner ∉ current.application.config.defaulted :=
            current.application.active_of_ready_owned facts.quiescent readyStepped owned
          cases acceptedEq : openingAccepted record.event current.application.config.store
          · right
            right
            have rejectedMiddle := OpeningRejected.keep (setup := setup) keptMiddle
              ⟨fun field read => current.application.config.read_available readyStepped read,
                acceptedEq⟩
            rw [step_of_opening_rejected current.application.config record.event readyStepped
              node acceptedEq action, PMF.mem_support_pure_iff] at member
            have primary' := primary
            rw [member, Config.complete_history] at primary'
            have recordExact :=
              List.mem_singleton.mp ((List.mem_append.mp primary').resolve_left newRecord)
            have both := recordExact.symm.trans expiredEq
            unfold EventGraph.completion at both
            rw [current.application.config.actualDecision_of_active record.event owner owned
                active action,
              current.application.config.actualDecision_of_active record.event owner owned
                active expiredAction,
              ExpiredAction.publication_eq expired payload outputEq] at both
            simp only [EventCompletion.mk.injEq, Option.some.injEq, heq_eq_eq, true_and] at both
            obtain ⟨actionFalse, -⟩ := both
            have nativeOutput : native.config.outputs record.event =
                some (cast (congrArg EventField.Value outputEq.symm)
                  (PublicationResult.failure)) := by
              rw [member]
              exact Config.complete_output_same _ _ _ _ _
            refine ⟨owner, payload, binding, checks, outputEq, codeEq, isWho, node,
              rejectedMiddle.1, rejectedMiddle.2, ?_,
              Config.Step.path_store_of_some native.drain_graph_steps (.inr record.event) _
                nativeOutput⟩
            rw [recorded]
            refine congrArg some (recordExact.trans ?_)
            rw [actionFalse]
            exact completion_resolve_eq _ _ outputEq codeEq active false .failure
          · exfalso
            have within := effectivePublication_withinDeadline contract timely players owner
              reference decides (follows owner isWho) current.environmentRecall.length bounded
              current supported record.event owned readyStepped
              (publications record.event bounds.1 bounds.2) acceptedEq
            unfold EventGraphRuntime.State.WithinDeadline at within
            rw [activated] at within
            exact absurd due (Nat.not_le.mpr within)
        · rw [owned] at ownerless
          cases ownerless
      · exact silentCase native rfl silent quiet notDone output drainOwner

end Vegas
