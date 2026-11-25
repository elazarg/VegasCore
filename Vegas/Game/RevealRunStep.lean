module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealRunRecords
public import Vegas.Game.RevealPhaseBoundary

@[expose] public section

/-! # A step of a run of reveals on the ledger

A step of a run of concurrent reveals runs from a point inside the run until a
condition on the cut, which holds once the run is done. Every execution it
reaches is reached by graph steps, has its new records classified as in a run,
keeps honest submissions accepted, and records a decision of the deviator only
at events the deviator may have ready before the step stops.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies} {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- The deviator records a decision since `origin` only at allowed events. -/
def DecidesOnly (who : Player) (origin : (serviceGraph setup deps).Config)
    (allowed : (serviceGraph setup deps).EventId → Prop)
    (config : (serviceGraph setup deps).Config) : Prop :=
  ∀ event : (serviceGraph setup deps).EventId, ¬ allowed event →
    event ∉ origin.cut.completed → (serviceGraph setup deps).actor? event = some who →
      ∀ record, completionOf config event = some record → record.decision = none

/-- The invariant of a step of a run from `origin`, with `n` rounds left. -/
def RunStepHolds (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy) (horizon : Nat)
    (start finish : Nat) (allowed : (serviceGraph setup deps).EventId → Prop)
    (origin : (serviceGraph setup deps).Config) (n : Nat)
    (current : (serviceApplication setup deps duration leaks).Execution) : Prop :=
    current ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) who deviation)
      current.environmentRecall.length).support ∧
    current.environmentRecall.length + n ≤ horizon ∧
    (¬ BlockDone finish current.application.config →
      InBlock start finish current.application.config) ∧
    HonestBlockSubmissions who start finish current ∧
    Relation.ReflTransGen Config.Step origin current.application.config ∧
    BlockRecordsSound who start finish origin
      current.application.config ∧
    DecidesOnly who origin allowed current.application.config

/-- **A round of a step of a run** keeps the step's invariant while the step
has not stopped. -/
theorem runStep_round
    (serial : (serviceGraph setup deps).ActorSerial) {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay : (serviceGraph setup deps).EventId → Nat}
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup deps).Config)
      (event : (serviceGraph setup deps).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
      (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup deps) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup deps).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup deps).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup deps).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (publications : ∀ event : (serviceGraph setup deps).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup deps).outputLayout event).IsPublication)
    (stop : (serviceGraph setup deps).order.Cut → Prop)
    (stopDone : ∀ cut : (serviceGraph setup deps).order.Cut,
      (∀ event : (serviceGraph setup deps).EventId, event.val < finish →
        event ∈ cut.completed) → stop cut)
    (origin : (serviceGraph setup deps).Config)
    (allowed : (serviceGraph setup deps).EventId → Prop)
    (readyAllowed : ∀ config : (serviceGraph setup deps).Config,
      Relation.ReflTransGen Config.Step origin config →
      ¬ stop config.cut → ∀ event, config.cut.Ready event →
        (serviceGraph setup deps).actor? event = some who → allowed event)
:
    ∀ (n : Nat) (current : (serviceApplication setup deps duration leaks).Execution),
      RunStepHolds scheduler bound turns reference who deviation horizon start finish allowed
        origin (n + 1) current →
      ¬ stop current.application.config.cut →
      ∀ next ∈ ((serviceApplication setup deps duration leaks).round scheduler
        (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
          (firstTurnTiming setup turns deps) reference) who deviation) current).support,
        RunStepHolds scheduler bound turns reference who deviation horizon start finish allowed
          origin n next := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound
    turns (firstTurnTiming setup turns deps) reference) who deviation
  have notDone (cut : (serviceGraph setup deps).order.Cut) (running : ¬ stop cut) :
      ¬ ∀ event : (serviceGraph setup deps).EventId, event.val < finish →
        event ∈ cut.completed := fun done => running (stopDone cut done)
  intro n current valid running next moved
  obtain ⟨currentSupported, currentBounded, currentInside, currentSubmissions, walked, sound,
    decided⟩ := valid
  have unfinished : ¬ BlockDone finish current.application.config := notDone _ running
  have lengths := app.round_environmentRecall_length scheduler players current next moved
  have path := reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
    players current next moved
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialDistribution setup deps) horizon
    scheduler
    players current.environmentRecall.length (by omega) current currentSupported
  have remaining : horizon - current.environmentRecall.length =
      (horizon - current.environmentRecall.length - 1) + 1 := by omega
  rw [remaining] at trace
  have within (event : (serviceGraph setup deps).EventId)
      (ready : current.application.config.cut.Ready event) :
      start ≤ event.val ∧ event.val < finish :=
    shaped _ (currentInside unfinished) unfinished event ready
  refine ⟨?_, by omega, fun later => (currentInside unfinished).path shaped path later,
    honestBlockSubmissions_round scheduler bound turns reference decides who deviation start
      finish shaped publications current next trace (currentInside unfinished) unfinished
      currentSubmissions moved, walked.trans path,
    blockRecordsSound_round serial bound turns contract timely reference decides who deviation start
      finish shaped publications origin current next currentSupported
      (by omega) (currentInside unfinished) unfinished currentSubmissions sound moved, ?_⟩
  · apply app.roundsFrom_runUntil scheduler players (serviceInitialDistribution setup deps)
      (fun current => stop current.application.config.cut) 1 current next currentSupported
    change next ∈ (if stop current.application.config.cut then PMF.pure current
      else (app.round scheduler players current).bind (app.runUntil scheduler players
        (fun current => stop current.application.config.cut) 0)).support
    rw [ite_eq_right running, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨next, moved, by simp [ReactiveApplication.runUntil]⟩
  · intro event notAllowed fresh owned record found
    by_cases old : event ∈ current.application.config.cut.completed
    · obtain ⟨previous, previousFound⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff current.application.config event).mpr old)
      have kept := Config.Step.path_completionOf_of_some path event previous previousFound
      rw [kept] at found
      have same := Option.some.inj found
      subst same
      exact decided event notAllowed fresh owned _ previousFound
    have doneNext : event ∈ next.application.config.cut.completed := by
      obtain ⟨present, _⟩ := (completionOf_eq_some_iff _ event record).mp found
      rw [← next.application.config.history_exact event]
      exact List.mem_map.mpr ⟨record, present, by
        obtain ⟨_, same⟩ := (completionOf_eq_some_iff _ event record).mp found
        exact same⟩
    rcases round_new_record_ready current next
        (fun query ready => publications query (within query ready).1 (within query ready).2)
        moved event old doneNext with silent | ready
    · exact silent record found
    · exact (notAllowed (readyAllowed _ walked running event ready owned)).elim

/-- **A step of a run.** Every execution a supported step of a run of
concurrent reveals reaches before its stopping condition was reached from the
start by graph steps, has its new records classified, keeps honest submissions
accepted, stays inside the run, and records a decision of the deviator only at
events allowed whenever they are ready, when honest clients open a reveal
exactly when its opening is accepted. -/
theorem runStep_facts
    (serial : (serviceGraph setup deps).ActorSerial) {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay : (serviceGraph setup deps).EventId → Nat}
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup deps).Config)
      (event : (serviceGraph setup deps).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
      (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup deps) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup deps).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup deps).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup deps).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (publications : ∀ event : (serviceGraph setup deps).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup deps).outputLayout event).IsPublication)
    (stop : (serviceGraph setup deps).order.Cut → Prop) [DecidablePred stop]
    (stopDone : ∀ cut : (serviceGraph setup deps).order.Cut,
      (∀ event : (serviceGraph setup deps).EventId, event.val < finish →
        event ∈ cut.completed) → stop cut)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (allowed : (serviceGraph setup deps).EventId → Prop)
    (readyAllowed : ∀ config : (serviceGraph setup deps).Config,
      Relation.ReflTransGen Config.Step execution.application.config config →
      ¬ stop config.cut → ∀ event, config.cut.Ready event →
        (serviceGraph setup deps).actor? event = some who → allowed event)
    (supported : execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) who deviation)
      execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (inside : ¬ BlockDone finish execution.application.config →
      InBlock start finish execution.application.config)
    (submissions : HonestBlockSubmissions who start finish execution)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) who deviation)
      (fun current => stop current.application.config.cut) horizon execution).support) :
    Relation.ReflTransGen Config.Step execution.application.config final.application.config ∧
      BlockRecordsSound who start finish execution.application.config
        final.application.config ∧
      DecidesOnly who execution.application.config allowed final.application.config ∧
      HonestBlockSubmissions who start finish final ∧
      (¬ BlockDone finish final.application.config →
        InBlock start finish final.application.config) := by
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound
    turns (firstTurnTiming setup turns deps) reference) who deviation
  have notDone (cut : (serviceGraph setup deps).order.Cut) (running : ¬ stop cut) :
      ¬ ∀ event : (serviceGraph setup deps).EventId, event.val < finish →
        event ∈ cut.completed := fun done => running (stopDone cut done)
  have preserved := runStep_round serial bound turns contract timely reference decides who deviation
    start finish shaped publications stop stopDone execution.application.config allowed
    readyAllowed
  obtain ⟨n, _, _, finalInside, finalSubmissions, walked, sound, decided⟩ :=
    app.runUntil_support_holds scheduler players
      (fun current => stop current.application.config.cut)
      (RunStepHolds scheduler bound turns reference who deviation horizon start finish allowed
        execution.application.config) preserved
      (horizon - execution.environmentRecall.length) execution
      ⟨supported, by omega, inside, submissions, .refl, fun event fresh done => (fresh done).elim,
        fun event _ fresh _ record found => (fresh ((completionOf_isSome_iff _ event).mp
          (by rw [found]; rfl))).elim⟩ final reached
  exact ⟨walked, sound, decided, finalSubmissions, finalInside⟩

end Vegas
