/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockReflection

/-! # Runs of a block of concurrent reveals

Along every supported run of a block of concurrent reveals, run until the block
is done, the configuration moves by graph steps, every honest submission stays
accepted, and every new record stays classified. Defaults keep naming the
owners of their events along graph steps.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

section Generic

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- A count-indexed invariant preserved by every round that is taken holds at
every execution a stopped run reaches. -/
theorem _root_.Interaction.ReactiveApplication.runUntil_support_holds (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (holds : Nat → app.Execution → Prop)
    (preserved : ∀ n execution, holds (n + 1) execution → ¬ stop execution →
      ∀ next ∈ (app.round scheduler players execution).support, holds n next) :
    ∀ (count : Nat) (execution : app.Execution), holds count execution →
      ∀ final ∈ (app.runUntil scheduler players stop count execution).support,
        ∃ n, holds n final := by
  intro count
  induction count with
  | zero =>
      intro execution valid final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨0, valid⟩
  | succ count ih =>
      intro execution valid final reached
      by_cases stopped : stop execution
      · rw [app.runUntil_of_stop scheduler players stop _ execution stopped,
          PMF.mem_support_pure_iff] at reached
        subst reached
        exact ⟨count + 1, valid⟩
      · simp only [ReactiveApplication.runUntil, stopped, ↓reduceIte] at reached
        obtain ⟨next, nextReached, finalReached⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        exact ih next (preserved count execution valid stopped next nextReached) final
          finalReached

end Generic

section Owners

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every recorded default names the owner of its event. -/
def DefaultOwners (config : graph.Config) : Prop :=
  ∀ completion ∈ config.history, ∀ player, completion.defaultEvent = some player →
    graph.actor? completion.event = some player

/-- Defaults keep naming their owners along graph paths. -/
theorem DefaultOwners.path {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) (owners : DefaultOwners before) :
    DefaultOwners after := by
  induction path with
  | refl => exact owners
  | @tail middle next _ moved ih =>
      obtain ⟨event, ready, action, supported⟩ := moved
      obtain ⟨value, _, history⟩ := middle.step_completion event ready action next supported
      intro completion member player defaulted
      rw [history] at member
      rcases List.mem_append.mp member with old | new
      · exact ih completion old player defaulted
      · have same := List.mem_singleton.mp new
        subst same
        exact completion_defaultEvent_actor middle event action value player defaulted

end Owners

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **A block run.** Every execution a supported block run reaches until the
block is done was reached from the start by graph steps and has its new
records classified, when honest clients open a reveal exactly when its opening
is accepted. -/
theorem blockRun_facts {horizon : Nat}
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
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (inside : ¬ BlockDone finish execution.application.config →
      InBlock start finish execution.application.config)
    (untouched : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → Untouched setup leaks event execution)
    (final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      (fun current => BlockDone finish current.application.config) horizon execution).support) :
    Relation.ReflTransGen Config.Step execution.application.config final.application.config ∧
      BlockRecordsSound who start finish execution.application.config
        final.application.config := by
  let app := serviceApplication setup mode duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  let holds := fun (n : Nat) (current : app.Execution) =>
    current ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler players
      current.environmentRecall.length).support ∧
    current.environmentRecall.length + n ≤ horizon ∧
    (¬ BlockDone finish current.application.config →
      InBlock start finish current.application.config) ∧
    HonestBlockSubmissions who start finish current ∧
    Relation.ReflTransGen Config.Step execution.application.config current.application.config ∧
    BlockRecordsSound who start finish execution.application.config current.application.config
  have preserved : ∀ n current, holds (n + 1) current →
      ¬ BlockDone finish current.application.config →
      ∀ next ∈ (app.round scheduler players current).support, holds n next := by
    intro n current valid running next moved
    obtain ⟨currentSupported, currentBounded, currentInside, submissions, walked, sound⟩ := valid
    have lengths := app.round_environmentRecall_length scheduler players current next moved
    have path := reactive_round_graph_steps (serviceTimeouts setup mode duration) leaks scheduler
      players current next moved
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
      players current.environmentRecall.length (by omega) current currentSupported
    have remaining : horizon - current.environmentRecall.length =
        (horizon - current.environmentRecall.length - 1) + 1 := by omega
    rw [remaining] at trace
    refine ⟨?_, by omega, fun unfinished => (currentInside running).path shaped path unfinished,
      honestBlockSubmissions_round scheduler bound turns reference decides who deviation start
        finish shaped publications current next trace (currentInside running) running
        submissions moved, walked.trans path,
      blockRecordsSound_round bound turns contract timely reference decides who deviation start
        finish shaped publications execution.application.config current next currentSupported
        (by omega) (currentInside running) running submissions sound moved⟩
    apply app.roundsFrom_runUntil scheduler players (serviceInitialLaw setup mode)
      (fun current => BlockDone finish current.application.config) 1 current next
      currentSupported
    change next ∈ (if BlockDone finish current.application.config then PMF.pure current
      else (app.round scheduler players current).bind (app.runUntil scheduler players
        (fun current => BlockDone finish current.application.config) 0)).support
    rw [ite_eq_right running, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨next, moved, by simp [ReactiveApplication.runUntil]⟩
  have atTurn : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks execution owner :=
    fun owner different => (canonicalSlots_roundsFrom_reference scheduler players owner
      (firstTurnTiming setup turns mode) reference (Function.update_of_ne different _ _)
      execution.environmentRecall.length execution supported).1
  obtain ⟨n, _, _, _, _, walked, sound⟩ := app.runUntil_support_holds scheduler players
    (fun current => BlockDone finish current.application.config) holds preserved
    (horizon - execution.environmentRecall.length) execution
    ⟨supported, by omega, inside, honestBlockSubmissions_start who start finish execution
      atTurn untouched, .refl, fun event fresh done => (fresh done).elim⟩ final reached
  exact ⟨walked, sound⟩

end Vegas
