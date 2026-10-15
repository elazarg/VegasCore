/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedEmissionPersistence
import Vegas.Pending.PhaseSeedInclusion
import Vegas.Pending.PhaseCountUniqueness
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveRoundTrace

/-! # A physical coordinate has one immutable timed envelope in clean histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem ownerWord_messages_sublist (coordinate : CommitAttemptEvent graph)
    (owner : Player) (past : List (app).PlayerEntry) :
    List.Sublist ((ownerWord runtime leaks coordinate owner past).flatMap Prod.snd)
      ((app).outputs past) := by
  classical
  induction past with
  | nil => simp [ownerWord, ReactiveApplication.outputs]
  | cons entry rest ih =>
      by_cases requested : PhaseRuntimeState.requests entry.beforeView.application.2
          owner coordinate
      · cases emitted : entry.emitted with
        | none => simpa [ownerWord, requested, ReactiveApplication.outputs, emitted] using ih
        | some message =>
            by_cases selected : ownPacket coordinate owner message = true
            · simpa [ownerWord, requested, ReactiveApplication.outputs, emitted, selected]
                using ih.cons_cons message
            · simpa [ownerWord, requested, ReactiveApplication.outputs, emitted, selected]
                using ih.cons message
      · cases emitted : entry.emitted with
        | none => simpa [ownerWord, requested, ReactiveApplication.outputs, emitted] using ih
        | some message =>
            simpa [ownerWord, requested, ReactiveApplication.outputs, emitted]
              using ih.cons message

omit [Fintype Player] in
/-- The timed word contains each authored envelope at most once, including its raw payload. -/
theorem localInput_emissions_nodup (execution : (app).Execution)
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (words : WordRecall runtime leaks execution)
    (recalled : PhaseCount.CountRecall runtime leaks execution) :
    ((localInput runtime leaks coordinate owner execution.environmentRecall
      (execution.observeEnvironment app)).emissions.map Prod.snd).Nodup := by
  have serials := recalled.2.2 owner
  have outputSerials : ((app).outputs (execution.recall owner)).map
      (fun message => message.id.2) = List.range (execution.network.nextSerial owner) := by
    rw [← recalled.1 owner]
    exact serials
  have outputs : ((app).outputs (execution.recall owner)).Nodup :=
    List.Nodup.of_map (fun message => message.id.2) (outputSerials ▸ List.nodup_range)
  rw [localInput_word, words owner coordinate]
  simpa only [List.map_flatMap, List.map_map, Function.comp_def, List.map_id'] using
    outputs.sublist (ownerWord_messages_sublist runtime leaks coordinate owner
      (execution.recall owner))

omit [Fintype Player] in
/-- Count permission identifies all emissions of a physical coordinate, while
permanent serial order rules out a repeated occurrence at a different clock. -/
theorem localInput_emissions_eq_singleton (execution : (app).Execution)
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (words : WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (identified : ∀ first ∈ execution.network.inputs, ∀ second ∈ execution.network.inputs,
      first.id = second.id → first = second)
    (tick : Nat) (message : Message Player (CommitAttemptPacket graph))
    (recorded : (tick, message) ∈ (localInput runtime leaks coordinate owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    (localInput runtime leaks coordinate owner execution.environmentRecall
      (execution.observeEnvironment app)).emissions = [(tick, message)] := by
  classical
  let emissions := (localInput runtime leaks coordinate owner execution.environmentRecall
    (execution.observeEnvironment app)).emissions
  have only (entry) (member : entry ∈ emissions) : entry.2 = message := by
    have first := localInput_emission_authentic runtime leaks execution coordinate owner
      words clean.1.1 entry.1 entry.2 member
    have second := localInput_emission_authentic runtime leaks execution coordinate owner
      words clean.1.1 tick message recorded
    apply PhaseCount.Permits.eq_of_same_event
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 entry.2 first.1))
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message second.1))
      first.1 second.1 identified (first.2.1.trans second.2.1.symm)
    simp only [PhaseCount.event?, first.2.2.2, second.2.2.2, Option.map_some,
      first.2.2.1, second.2.2.1]
  have unique := localInput_emissions_nodup runtime leaks execution coordinate owner words clean.1
  change (emissions.map Prod.snd).Nodup at unique
  have length : emissions.length ≤ 1 := by
    have mapped : emissions.map Prod.snd = List.replicate emissions.length message :=
      List.map_eq_replicate_iff.mpr only
    rw [mapped] at unique
    exact List.nodup_replicate.mp unique
  change (tick, message) ∈ emissions at recorded
  have nonzero : emissions.length ≠ 0 := by
    intro zero
    have empty := List.eq_nil_of_length_eq_zero zero
    rw [empty] at recorded
    cases recorded
  have lengthOne : emissions.length = 1 := by omega
  obtain ⟨first, same⟩ := List.length_eq_one_iff.mp lengthOne
  change emissions = [(tick, message)]
  rw [same] at recorded ⊢
  exact congrArg (fun entry => [entry]) (List.mem_singleton.mp recorded).symm

/-- An actual supported continuation retains exactly the same timed envelope;
future private choices cannot add another envelope for this physical address. -/
theorem runRounds_emissions_eq_singleton (bounds : MessageBounds graph)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    (remaining count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some ⟨remaining + count, none, execution⟩))
    (words : WordRecall runtime leaks execution)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support)
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (tick : Nat) (message : Message Player (CommitAttemptPacket graph))
    (recorded : (tick, message) ∈ (localInput runtime leaks coordinate owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    (localInput runtime leaks coordinate owner next.environmentRecall
      (next.observeEnvironment app)).emissions = [(tick, message)] := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  obtain ⟨nextTrace⟩ := menu.trace_runRounds initial horizon scheduler players covered
    remaining count execution next trace reached
  have raw := menu.toRawTrace initial horizon scheduler nextTrace
  have nextClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) nextTrace
  have nextWords := runRounds_wordRecall runtime leaks scheduler players count execution next
    words reached
  have retainedWord := runRounds_emissions_prefix runtime leaks scheduler players count
    execution next words reached owner coordinate
  exact localInput_emissions_eq_singleton runtime leaks next coordinate owner nextWords nextClean
    (fun first firstInput second secondInput same =>
      (app).input_identifier_injective_history initial horizon scheduler
        ⟨remaining, none, next⟩ raw first second firstInput secondInput same)
    tick message (retainedWord.subset recorded)

end Vegas.EventGraphRuntime.PhaseSeedScheduler
