/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingClearExecutionCoupling
import Vegas.Pending.PhaseBindingMemoryIncludeTrace
import Vegas.Pending.PhaseBindingMemoryActivation

/-! # All original scheduler commands during an opaque commitment block -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L} {Obs : Type}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every selected original scheduler command couples the actual clear
execution laws, deriving updated memory on inclusion and retaining both recalls.
Only first public exclusion is collapsed; phase exit is still an actual state. -/
theorem environment_command_memory_coupling (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (left right : (app).Execution)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, right⟩))
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (observe : (app).PlayerView → Obs)
    (past : (left.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)) =
      (right.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)))
    (clear : right.application.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment)
    (command : (app).Command)
    (selected : command ∈ (scheduler left.environmentRecall
      (left.observeEnvironment app)).support) :
    ∃ paired : PMF (Option (app).Execution × Option (app).Execution),
      paired.map Prod.fst = ((left.environmentStep app command).map fun next =>
        if next.application.current.excluded = ∅ then some next else none) ∧
      paired.map Prod.snd = ((right.environmentStep app command).map fun next =>
        if next.application.current.excluded = ∅ then some next else none) ∧
      ∀ pair ∈ paired.support, match pair with
        | (none, none) => True
        | (some first, some second) => ∃ nextMemory : BindingShadow graph,
            nextMemory.OwnBindings owner ∧
            (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
            first.application = nextMemory.phased owner second.application ∧
            first.network = second.network ∧ first.receipts = second.receipts ∧
            first.environmentRecall = second.environmentRecall ∧
            (∀ who, who ≠ owner → first.recall who = second.recall who) ∧
            (first.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)) =
              (second.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted))
        | _ => False := by
  classical
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application, phased_publicView owned]
    rfl
  have firstClear : left.application.current.excluded = ∅ := by rw [application]; exact clear
  cases command with
  | application command =>
      obtain ⟨paired, firstLaw, secondLaw, related⟩ := environment_clear_execution_coupling
        runtime leaks memory owner owned left right application network receipts service recalled
          clear opaquePhase command
      refine ⟨paired, firstLaw, secondLaw, ?_⟩
      intro pair supported
      have actual := related pair supported
      rcases pair with ⟨first, second⟩
      cases first with
      | none => cases second <;> exact actual
      | some first =>
          cases second with
          | none => exact actual
          | some second =>
              rcases actual with ⟨state, net, receipt, log, recallEq, firstPast, secondPast⟩
              exact ⟨memory, owned, valid, state, net, receipt, log, recallEq, by
                rw [firstPast, secondPast]; exact past⟩
  | activate actor =>
      obtain ⟨paired, firstLaw, secondLaw, related⟩ := activation_memory_coupling runtime leaks
        memory owner owned left right application network receipts service actor
      refine ⟨paired.map (fun pair => (some pair.1, some pair.2)), ?_, ?_, ?_⟩
      · rw [PMF.map_comp]
        change paired.map (some ∘ Prod.fst) = _
        rw [← PMF.map_comp, firstLaw]
        apply map_congr_on_support
        intro next supported
        obtain ⟨selected, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        obtain ⟨ids, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp _drawn
        simp only [firstClear, ite_true]
      · rw [PMF.map_comp]
        change paired.map (some ∘ Prod.snd) = _
        rw [← PMF.map_comp, secondLaw]
        apply map_congr_on_support
        intro next supported
        obtain ⟨selected, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        obtain ⟨ids, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp _drawn
        simp only [clear, ite_true]
      · intro pair supported
        obtain ⟨actual, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        obtain ⟨state, net, receipt, log, firstPast, secondPast⟩ := related actual drawn
        refine ⟨memory, owned, valid, state, net, receipt, log, ?_, ?_⟩
        · rw [firstPast, secondPast]
          exact recalled
        · rw [firstPast, secondPast]
          exact past
  | «include» id =>
      obtain ⟨_, _, nextMemory, nextOwned, nextValid, state, net, receipt, log, recallEq, word⟩ :=
        phase_binding_memory_include_trace runtime leaks bounds plan inputs horizon scheduler
          remaining left right leftTrace rightTrace memory owner owned valid application network
            receipts service recalled observe past clear opaquePhase id selected
      let first : (app).Execution := {left.includePending app id with environmentRecall :=
        left.environmentRecall ++ [⟨left.observeEnvironment app, .include id⟩]}
      let second : (app).Execution := {right.includePending app id with environmentRecall :=
        right.environmentRecall ++ [⟨right.observeEnvironment app, .include id⟩]}
      have secondClear : second.application.current.excluded = ∅ :=
        include_commitmentPhase_clear runtime leaks right clear opaquePhase id
      have leftOpaque : ∀ phase ∈ left.application.phases.head?, phase.kind = .commitment := by
        rw [application]
        exact opaquePhase
      have nextFirstClear : first.application.current.excluded = ∅ :=
        include_commitmentPhase_clear runtime leaks left firstClear leftOpaque id
      refine ⟨PMF.pure (some first, some second), ?_, ?_, ?_⟩
      · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        change _ = PMF.pure (if first.application.current.excluded = ∅ then some first else none)
        simp only [nextFirstClear, ite_true]
      · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        change _ = PMF.pure (if second.application.current.excluded = ∅ then some second else none)
        simp only [secondClear, ite_true]
      · intro pair supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        exact ⟨nextMemory, nextOwned, nextValid, state, net, receipt, log, recallEq, word⟩
  | wait =>
      let first : (app).Execution := {left with environmentRecall :=
        left.environmentRecall ++ [⟨left.observeEnvironment app, .wait⟩]}
      let second : (app).Execution := {right with environmentRecall :=
        right.environmentRecall ++ [⟨right.observeEnvironment app, .wait⟩]}
      refine ⟨PMF.pure (some first, some second), ?_, ?_, ?_⟩
      · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        change _ = PMF.pure (if left.application.current.excluded = ∅ then some first else none)
        simp only [firstClear, ite_true]
      · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        change _ = PMF.pure (if right.application.current.excluded = ∅ then some second else none)
        simp only [clear, ite_true]
      · intro pair supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        refine ⟨memory, owned, valid, application, network, receipts, ?_, recalled, past⟩
        change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
        rw [service, before]

end Vegas.EventGraphRuntime.BindingShadow
