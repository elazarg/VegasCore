/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunRecords
import Vegas.Game.RevealPhaseBoundary

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
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The deviator records a decision since `origin` only at allowed events. -/
def DecidesOnly (who : Player) (origin : (serviceGraph setup mode).Config)
    (allowed : (serviceGraph setup mode).EventId → Prop)
    (config : (serviceGraph setup mode).Config) : Prop :=
  ∀ event : (serviceGraph setup mode).EventId, ¬ allowed event →
    event ∉ origin.cut.completed → (serviceGraph setup mode).actor? event = some who →
      ∀ record, completionOf config event = some record → record.decision = none

/-- **A step of a run.** Every execution a supported step of a run of
concurrent reveals reaches before its stopping condition was reached from the
start by graph steps, has its new records classified, keeps honest submissions
accepted, stays inside the run, and records a decision of the deviator only at
events allowed whenever they are ready, when honest clients open a reveal
exactly when its opening is accepted. -/
theorem runStep_facts {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
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
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (stop : (serviceGraph setup mode).order.Cut → Prop) [DecidablePred stop]
    (stopDone : ∀ cut : (serviceGraph setup mode).order.Cut,
      (∀ event : (serviceGraph setup mode).EventId, event.val < finish →
        event ∈ cut.completed) → stop cut)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (allowed : (serviceGraph setup mode).EventId → Prop)
    (readyAllowed : ∀ config : (serviceGraph setup mode).Config,
      Relation.ReflTransGen Config.Step execution.application.config config →
      ¬ stop config.cut → ∀ event, config.cut.Ready event →
        (serviceGraph setup mode).actor? event = some who → allowed event)
    (supported : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (inside : ¬ BlockDone finish execution.application.config →
      InBlock start finish execution.application.config)
    (submissions : HonestBlockSubmissions who start finish execution)
    (final : (serviceApplication setup mode deadline leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      (fun current => stop current.application.config.cut) horizon execution).support) :
    Relation.ReflTransGen Config.Step execution.application.config final.application.config ∧
      BlockRecordsSound who start finish execution.application.config
        final.application.config ∧
      DecidesOnly who execution.application.config allowed final.application.config ∧
      HonestBlockSubmissions who start finish final ∧
      (¬ BlockDone finish final.application.config →
        InBlock start finish final.application.config) := by
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  have notDone (cut : (serviceGraph setup mode).order.Cut) (running : ¬ stop cut) :
      ¬ ∀ event : (serviceGraph setup mode).EventId, event.val < finish →
        event ∈ cut.completed := fun done => running (stopDone cut done)
  let holds := fun (n : Nat) (current : app.Execution) =>
    current ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler players
      current.environmentRecall.length).support ∧
    current.environmentRecall.length + n ≤ horizon ∧
    (¬ BlockDone finish current.application.config →
      InBlock start finish current.application.config) ∧
    HonestBlockSubmissions who start finish current ∧
    Relation.ReflTransGen Config.Step execution.application.config current.application.config ∧
    BlockRecordsSound who start finish execution.application.config
      current.application.config ∧
    DecidesOnly who execution.application.config allowed current.application.config
  have preserved : ∀ n current, holds (n + 1) current →
      ¬ stop current.application.config.cut →
      ∀ next ∈ (app.round scheduler players current).support, holds n next := by
    intro n current valid running next moved
    obtain ⟨currentSupported, currentBounded, currentInside, currentSubmissions, walked, sound,
      decided⟩ := valid
    have unfinished : ¬ BlockDone finish current.application.config := notDone _ running
    have lengths := app.round_environmentRecall_length scheduler players current next moved
    have path := reactive_round_graph_steps (serviceRuntime setup mode deadline) leaks scheduler
      players current next moved
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
      players current.environmentRecall.length (by omega) current currentSupported
    have remaining : horizon - current.environmentRecall.length =
        (horizon - current.environmentRecall.length - 1) + 1 := by omega
    rw [remaining] at trace
    have within (event : (serviceGraph setup mode).EventId)
        (ready : current.application.config.cut.Ready event) :
        start ≤ event.val ∧ event.val < finish :=
      shaped _ (currentInside unfinished) unfinished event ready
    refine ⟨?_, by omega, fun later => (currentInside unfinished).path shaped path later,
      honestBlockSubmissions_round scheduler bound turns reference decides who deviation start
        finish shaped publications current next trace (currentInside unfinished) unfinished
        currentSubmissions moved, walked.trans path,
      blockRecordsSound_round bound turns contract timely reference decides who deviation start
        finish shaped publications execution.application.config current next currentSupported
        (by omega) (currentInside unfinished) unfinished currentSubmissions sound moved, ?_⟩
    · apply app.roundsFrom_runUntil scheduler players (serviceInitialLaw setup mode)
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
  obtain ⟨n, _, _, finalInside, finalSubmissions, walked, sound, decided⟩ :=
    app.runUntil_support_holds scheduler players
      (fun current => stop current.application.config.cut) holds preserved
      (horizon - execution.environmentRecall.length) execution
      ⟨supported, by omega, inside, submissions, .refl, fun event fresh done => (fresh done).elim,
        fun event _ fresh _ record found => (fresh ((completionOf_isSome_iff _ event).mp
          (by rw [found]; rfl))).elim⟩ final reached
  exact ⟨walked, sound, decided, finalSubmissions, finalInside⟩

end Vegas
