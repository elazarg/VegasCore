/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealClosureBoundary
import Vegas.Game.RevealPhaseBoundary

/-! # Points inside a run of reveals

A point of a run of reveals from `start` to `finish` with bar `bar`: the
execution is reached by complete rounds within the horizon, earlier events
have completed, it lies inside the run, honest submissions are accepted, the
deviator's reveals of the run before `bar` have completed, and from `bar` on its
reveals are pending while it is active and recorded silently. A phase boundary
at the start of a run is a point with bar `start`; the end of a step to the
deviator's next reveal `target` is a point with bar `target + 1`; and the end of
the last step is the phase boundary at `finish`.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A point of a run of reveals with bar `bar`. -/
structure RunPoint (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (players : Player → (serviceApplication setup mode duration leaks).Policy) (horizon : Nat)
    (who : Player) (start finish bar : Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution) : Prop where
  supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
    (serviceInitialLaw setup mode) scheduler players execution.environmentRecall.length).support
  bounded : execution.environmentRecall.length ≤ horizon
  earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
    event ∈ execution.application.config.cut.completed
  inside : ¬ BlockDone finish execution.application.config →
    InBlock start finish execution.application.config
  submissions : HonestBlockSubmissions who start finish execution
  owned : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val → event.val < bar →
    (serviceGraph setup mode).actor? event = some who →
      event ∈ execution.application.config.cut.completed
  pending : ∀ event : (serviceGraph setup mode).EventId, bar ≤ event.val →
    event.val < finish → (serviceGraph setup mode).actor? event = some who →
      who ∉ execution.application.config.defaulted →
        event ∉ execution.application.config.cut.completed
  silent : ∀ event : (serviceGraph setup mode).EventId, bar ≤ event.val →
    event.val < finish → (serviceGraph setup mode).actor? event = some who →
      ∀ record, completionOf execution.application.config event = some record →
        record.decision = none
  later : ∀ event : (serviceGraph setup mode).EventId, finish ≤ event.val →
    event ∈ execution.application.config.cut.completed →
      completionOf execution.application.config event = some ⟨event, none, none⟩ ∧
      execution.application.config.outputs event = failureOutput event ∧
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧
        owner ∈ execution.application.config.defaulted
  seen : SeenOnly (fun event : (serviceGraph setup mode).EventId => event.val < finish) execution
  owners : DefaultOwners execution.application.config

/-- A silent record of a later event stays silent along graph paths. -/
theorem later_silent_path {before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    {event : (serviceGraph setup mode).EventId}
    (done : event ∈ before.cut.completed)
    (silent : completionOf before event = some ⟨event, none, none⟩ ∧
      before.outputs event = failureOutput event ∧
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧ owner ∈ before.defaulted) :
    completionOf after event = some ⟨event, none, none⟩ ∧
      after.outputs event = failureOutput event ∧
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧ owner ∈ after.defaulted := by
  obtain ⟨recorded, output, owner, owned, inactive⟩ := silent
  exact ⟨Config.Step.path_completionOf_of_some path event _ recorded,
    (outputs_path path done).trans output, owner, owned,
    Config.Step.path_defaulted_mono path inactive⟩

/-- **A phase boundary at the start of a run is a point of the run.** -/
theorem PhaseBoundary.runPoint
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup mode duration leaks).Policy) {horizon : Nat}
    (relaxed : RelaxedOrder (serviceGraph setup mode)) {start finish : Nat}
    (run : RevealRun (serviceGraph setup mode) start finish)
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (boundary : PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode
      duration leaks bound turns (firstTurnTiming setup turns mode) reference) who deviation)
      horizon start execution) :
    RunPoint scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration leaks
      bound turns (firstTurnTiming setup turns mode) reference) who deviation) horizon who start
      finish start execution where
  supported := boundary.supported
  bounded := boundary.bounded
  earlier := boundary.earlier
  inside := fun running => ⟨boundary.earlier, fun event late done =>
    running (run.done_of_later relaxed late done)⟩
  submissions := honestBlockSubmissions_start who start finish execution
    (fun owner different => (canonicalSlots_roundsFrom_reference scheduler _ owner
      (firstTurnTiming setup turns mode) reference (Function.update_of_ne different _ _)
      execution.environmentRecall.length execution boundary.supported).1)
    (fun event early _ => boundary.seen.untouched (by omega))
  owned := fun event early late _ => by omega
  pending := fun event early _ owned active done => by
    obtain ⟨_, _, owner, ownedOwner, inactive⟩ := boundary.later event early done
    rw [owned] at ownedOwner
    cases ownedOwner
    exact active inactive
  silent := fun event early _ _ record found => by
    have done : event ∈ execution.application.config.cut.completed :=
      (completionOf_isSome_iff _ event).mp (by rw [found]; rfl)
    rw [(boundary.later event early done).1] at found
    cases found
    rfl
  later := fun event late done =>
    boundary.later event (le_trans run.nonempty.le late) done
  seen := boundary.seen.mono fun event smaller => by have := run.nonempty; omega
  owners := boundary.owners

/-- A new event of an active deviator recorded on a path records a decision. -/
theorem decided_of_active_path {who : Player} {before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    (active : who ∉ after.defaulted) {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some who)
    (fresh : event ∉ before.cut.completed) (done : event ∈ after.cut.completed) :
    ∃ record, completionOf after event = some record ∧ record.decision ≠ none := by
  obtain ⟨middle, next, ready, action, walked, member, rest⟩ := path_new_event path fresh done
  obtain ⟨value, _, recorded⟩ := step_record_path member rest
  have middleActive : who ∉ middle.defaulted := fun inactive => active
    (Config.Step.path_defaulted_mono
      (Relation.ReflTransGen.head ⟨event, ready, action, member⟩ rest) inactive)
  have ownedNode : ((serviceGraph setup mode).nodes event).actor = some who := owned
  refine ⟨_, recorded, ?_⟩
  change middle.actualDecision event action ≠ none
  unfold Config.actualDecision
  rw [(EventCode.effectiveAction_of_active _ _ who ownedNode middleActive action).2]
  exact Option.some_ne_none _

/-- **The end of a step to the deviator's next reveal is the next point of the
run.** -/
theorem RunPoint.target_endpoint {horizon : Nat}
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
    (relaxed : RelaxedOrder (serviceGraph setup mode)) {start finish bar : Nat}
    (run : RevealRun (serviceGraph setup mode) start finish)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetEarly : bar ≤ target.val) (targetLate : target.val < finish)
    (least : ∀ event : (serviceGraph setup mode).EventId, bar ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event ≠ some who)
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (point : RunPoint scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration
      leaks bound turns (firstTurnTiming setup turns mode) reference) who deviation) horizon who
      start finish bar execution)
    (final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      (fun current => target ∈ current.application.config.cut.completed) horizon
      execution).support) :
    RunPoint scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration leaks
      bound turns (firstTurnTiming setup turns mode) reference) who deviation) horizon who start
      finish (target.val + 1) final := by
  classical
  let G := serviceGraph setup mode
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  have before : ∀ event : G.EventId, start ≤ event.val → event.val < target.val →
      G.actor? event = some who → event ∈ execution.application.config.cut.completed := by
    intro event early smaller owned
    by_cases low : event.val < bar
    · exact point.owned event early low owned
    · exact (least event (by omega) smaller owned).elim
  obtain ⟨path, sound, decided, submissions, inside⟩ := runStep_facts bound turns contract
    timely reference decides who deviation start finish (run.shaped relaxed) run.publications
    (fun cut => target ∈ cut.completed) (fun cut done => done target targetLate) execution
    (· = target) (fun config path running event ready owned => ready_owned_eq_target who relaxed
      run point.earlier target targetOwned targetLate before path running ready owned)
    point.supported point.bounded point.inside point.submissions final reached
  have done : target ∈ final.application.config.cut.completed :=
    runUntilHorizon_stop contract players
      (fun current => target ∈ current.application.config.cut.completed)
      (fun current terminal => by rw [terminal]; exact Finset.mem_univ _)
      execution point.supported point.bounded final reached
  obtain ⟨finalSupported, finalBounded⟩ :=
    runUntilHorizon_bounded point.supported point.bounded reached
  have mono := Config.Step.path_completed_mono path
  refine ⟨finalSupported, finalBounded, fun event early => mono (point.earlier event early),
    inside, submissions, ?_, ?_, ?_, ?_, ?_, DefaultOwners.path path point.owners⟩
  · intro event early smaller owned
    by_cases low : event.val < target.val
    · exact mono (before event early low owned)
    · have same : event = target := Fin.ext (by omega)
      rw [same]
      exact done
  · intro event late _ owned active doneFinal
    by_cases old : event ∈ execution.application.config.cut.completed
    · exact point.pending event (by omega) (by omega) owned
        (fun inactive => active (Config.Step.path_defaulted_mono path inactive)) old
    · obtain ⟨record, found, decision⟩ := decided_of_active_path path active owned old doneFinal
      exact decision (decided event (fun same => by rw [same] at late; omega) old owned record
        found)
  · intro event late lateFinish owned record found
    by_cases old : event ∈ execution.application.config.cut.completed
    · obtain ⟨previous, previousFound⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff _ event).mpr old)
      rw [Config.Step.path_completionOf_of_some path event previous previousFound] at found
      cases found
      exact point.silent event (by omega) lateFinish owned _ previousFound
    · exact decided event (fun same => by rw [same] at late; omega) old owned record found
  · intro event late doneFinal
    by_cases old : event ∈ execution.application.config.cut.completed
    · exact later_silent_path path old (point.later event late old)
    · rcases sound event old doneFinal with silentRecord | ⟨_, smaller, _⟩
      · exact silentRecord
      · omega
  · apply runUntil_seenOnly scheduler players
      (fun current => target ∈ current.application.config.cut.completed)
      (fun current => Relation.ReflTransGen Config.Step execution.application.config
        current.application.config ∧
        (¬ BlockDone finish current.application.config →
          InBlock start finish current.application.config))
      (fun current valid running next moved =>
        ⟨valid.1.trans (round_config_path moved), fun unfinished =>
          (valid.2 (fun blockDone => running (blockDone target targetLate))).path
            (run.shaped relaxed) (round_config_path moved) unfinished⟩)
      (fun current valid running event ready =>
        ((run.shaped relaxed) _ (valid.2 (fun blockDone => running (blockDone target targetLate)))
          (fun blockDone => running (blockDone target targetLate)) event ready).2)
      (horizon - execution.environmentRecall.length) execution ⟨.refl, point.inside⟩
      point.seen final reached

/-- **The end of the last step of a run is the phase boundary at its end.** -/
theorem RunPoint.final_endpoint {horizon : Nat}
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
    (relaxed : RelaxedOrder (serviceGraph setup mode)) {start finish bar : Nat}
    (run : RevealRun (serviceGraph setup mode) start finish)
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (point : RunPoint scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration
      leaks bound turns (firstTurnTiming setup turns mode) reference) who deviation) horizon who
      start finish bar execution)
    (final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      (fun current => BlockDone finish current.application.config) horizon execution).support) :
    PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration leaks
      bound turns (firstTurnTiming setup turns mode) reference) who deviation) horizon finish
      final := by
  classical
  let G := serviceGraph setup mode
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  have shaped := run.shaped relaxed
  have done := runUntilHorizon_stop contract players
    (fun current => BlockDone finish current.application.config)
    (fun current terminal event _ => by rw [terminal]; exact Finset.mem_univ _)
    execution point.supported point.bounded final reached
  obtain ⟨path, sound, _, _, _⟩ := runStep_facts bound turns contract timely reference decides
    who deviation start finish shaped run.publications
    (fun cut => ∀ event : G.EventId, event.val < finish → event ∈ cut.completed)
    (fun _ blockDone => blockDone) execution (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) point.supported point.bounded point.inside point.submissions
    final (by convert reached using 3; rfl)
  obtain ⟨finalSupported, finalBounded⟩ :=
    runUntilHorizon_bounded point.supported point.bounded reached
  refine ⟨finalSupported, finalBounded, done, fun event late doneFinal => ?_, ?_,
    DefaultOwners.path path point.owners⟩
  · by_cases old : event ∈ execution.application.config.cut.completed
    · exact later_silent_path path old (point.later event late old)
    · rcases sound event old doneFinal with silentRecord | ⟨_, smaller, _⟩
      · exact silentRecord
      · omega
  · apply runUntil_seenOnly scheduler players
      (fun current => BlockDone finish current.application.config)
      (fun current => Relation.ReflTransGen Config.Step execution.application.config
        current.application.config ∧
        (¬ BlockDone finish current.application.config →
          InBlock start finish current.application.config))
      (fun current valid running next moved =>
        ⟨valid.1.trans (round_config_path moved), fun unfinished =>
          (valid.2 running).path shaped (round_config_path moved) unfinished⟩)
      (fun current valid running event ready => (shaped _ (valid.2 running) running event ready).2)
      (horizon - execution.environmentRecall.length) execution ⟨.refl, point.inside⟩
      point.seen final reached

end Vegas
