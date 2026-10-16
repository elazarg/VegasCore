/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingEnvironmentCoupling
import GameTheory.Math.Probability.ConditionalObservation

/-! # Full original command marginals coupled until first exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L} {Obs : Type}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Existing fiber disintegration restores both original full command laws from
the clear projection. Excluded endpoints need no hypothetical restored shadow. -/
theorem environment_command_stopped_coupling (bounds : MessageBounds graph)
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
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst = left.environmentStep app command ∧
      paired.map Prod.snd = right.environmentStep app command ∧
      ∀ pair ∈ paired.support,
        (pair.1.application.current.excluded ≠ ∅ ∧ pair.2.application.current.excluded ≠ ∅) ∨
        ∃ nextMemory : BindingShadow graph,
          nextMemory.OwnBindings owner ∧
          (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
          pair.1.application = nextMemory.phased owner pair.2.application ∧
          pair.1.network = pair.2.network ∧ pair.1.receipts = pair.2.receipts ∧
          pair.1.environmentRecall = pair.2.environmentRecall ∧
          (∀ who, who ≠ owner → pair.1.recall who = pair.2.recall who) ∧
          (pair.1.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)) =
            (pair.2.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)) := by
  classical
  let firstLaw := left.environmentStep app command
  let secondLaw := right.environmentStep app command
  let cut (physical : (app).Execution) :=
    if physical.application.current.excluded = ∅ then some physical else none
  obtain ⟨optional, firstMarginal, secondMarginal, related⟩ :=
    environment_command_memory_coupling runtime leaks bounds plan inputs horizon scheduler
      remaining left right leftTrace rightTrace memory owner owned valid application network
        receipts service recalled observe past clear opaquePhase command selected
  let paired := optional.bind fun pair => bindPairLaw
    (fiberPosterior firstLaw cut pair.1) (fun _ => fiberPosterior secondLaw cut pair.2)
  refine ⟨paired, ?_, ?_, ?_⟩
  · simp only [paired, PMF.map_bind, bindPairLaw_map_fst]
    change optional.bind ((fiberPosterior firstLaw cut) ∘ Prod.fst) = firstLaw
    rw [← PMF.bind_map, firstMarginal]
    exact fiberPosterior_reconstruct firstLaw cut
  · simp only [paired, PMF.map_bind, bindPairLaw_map_snd, PMF.bind_const]
    change optional.bind ((fiberPosterior secondLaw cut) ∘ Prod.snd) = secondLaw
    rw [← PMF.bind_map, secondMarginal]
    exact fiberPosterior_reconstruct secondLaw cut
  · intro pair supported
    obtain ⟨observed, observationSupport, conditional⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨first, firstSupport, mappedSupport⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ conditional)
    obtain ⟨second, actualSecondSupport, same⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp mappedSupport
    cases same
    have firstPresent : observed.1 ∈ (firstLaw.map cut).support := by
      rw [← firstMarginal]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨observed, observationSupport, rfl⟩
    have secondPresent : observed.2 ∈ (secondLaw.map cut).support := by
      rw [← secondMarginal]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨observed, observationSupport, rfl⟩
    have firstCut := (mem_support_fiberPosterior firstPresent firstSupport).1
    have secondCut := (mem_support_fiberPosterior secondPresent actualSecondSupport).1
    have actual := related observed observationSupport
    rcases observed with ⟨firstObserved, secondObserved⟩
    cases firstObserved with
    | none =>
        cases secondObserved with
        | some secondObserved => exact actual.elim
        | none =>
            left
            constructor
            · change (if first.application.current.excluded = ∅ then some first else none) =
                none at firstCut
              split at firstCut
              · cases firstCut
              · assumption
            · change (if second.application.current.excluded = ∅ then some second else none) =
                none at secondCut
              split at secondCut
              · cases secondCut
              · assumption
    | some firstObserved =>
        cases secondObserved with
        | none => exact actual.elim
        | some secondObserved =>
            have firstEq : first = firstObserved := by
              by_cases firstClear : first.application.current.excluded = ∅
              · simpa only [cut, firstClear, ite_true, Option.some.injEq] using firstCut
              · simp only [cut, firstClear, ite_false] at firstCut
                cases firstCut
            have secondEq : second = secondObserved := by
              by_cases secondClear : second.application.current.excluded = ∅
              · simpa only [cut, secondClear, ite_true, Option.some.injEq] using secondCut
              · simp only [cut, secondClear, ite_false] at secondCut
                cases secondCut
            subst firstObserved
            subst secondObserved
            exact Or.inr actual

end Vegas.EventGraphRuntime.BindingShadow
