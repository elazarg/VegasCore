/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRoster

/-! # Actual private response counts in a finite service roster

Response-count offsets are consequences of supported native execution. Players
retain every response and passive observation; no scheduler cursor is supplied
to their policies. The count theorem includes arbitrary raw responses.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_instruction_actor (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks)
    (past : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView)
    (instruction : ServiceInstruction (graph setup)) (fixed : instruction ≠ .wire)
    (command : (application setup leaks).Command)
    (supported : command ∈ ((runtime setup).interactionInstruction leaks network
      past view instruction).support) :
    command.actor? (application setup leaks) = instructionActor instruction := by
  cases instruction with
  | player who | grant event | sample event | tick | expire event =>
      simp only [interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      rfl
  | includeLatest event owner =>
      simp only [interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      unfold reactiveLatest
      split <;> rfl
  | wire => exact False.elim (fixed rfl)

theorem fixed_plan_response_counts (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (plan : List (ServiceInstruction (graph setup))) (fixed : ServiceInstruction.wire ∉ plan)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network plan
      initial).support) (who : Player) :
    (final.recall who).length = (initial.recall who).length +
      (plan.filterMap instructionActor).count who := by
  induction plan generalizing initial with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      simp only [List.filterMap_nil, List.count_nil, Nat.add_zero]
  | cons instruction rest ih =>
      obtain ⟨middle, moved, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      have restFixed : ServiceInstruction.wire ∉ rest := fun member =>
        fixed (List.mem_cons_of_mem _ member)
      rw [ih restFixed middle reached]
      obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
      have actor := roster_instruction_actor setup leaks network initial.environmentRecall
        (initial.observeEnvironment (application setup leaks)) instruction
          (fun equal => fixed (List.mem_cons.mpr (Or.inl equal.symm))) command selected
      rw [(application setup leaks).dispatch_recall_length players command initial middle
        dispatched who, actor]
      cases selectedActor : instructionActor instruction with
      | none => simp only [List.filterMap_cons, selectedActor, reduceCtorEq, ↓reduceIte,
          Nat.add_zero]
      | some owner =>
          simp only [List.filterMap_cons, selectedActor, Option.some.injEq]
          by_cases same : owner = who
          · simp [same]
            omega
          · simp [same]

theorem roster_prefix_response_counts (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterPlanPrefix setup rosters event.val) initial).support) (who : Player) :
    (final.recall who).length = (initial.recall who).length +
      rosterOffset setup rosters who event := by
  rw [fixed_plan_response_counts setup leaks network players _
    (rosterPlanPrefix_no_wire setup rosters event.val) initial final reached who,
      rosterPlanPrefix_actors]
  rfl

end Vegas.SourceProgram.RevealService
