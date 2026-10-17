/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInformation
import Interaction.ReactiveRawRoundTrace

/-! # Actual clock-zero raw packets in the immutable early snapshot -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private def SnapshotRecorded (execution : app.Execution) : Prop :=
  ∀ owner entry, entry ∈ execution.recall owner → ∀ message, entry.emitted = some message →
    entry.beforeView.application.2.attempt = originalAttempt →
    entry.beforeView.application.1.publicView.clock = 0 →
    execution.environmentRecall.length ≤ 2 ∨
      ∃ snapshot, execution.environmentRecall[2]? = some snapshot ∧
        message ∈ snapshot.beforeView.network.inputs

private theorem snapshot_recorded_history (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => SnapshotRecorded current.execution) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ reached
          intro owner entry member
          exact (List.not_mem_nil member).elim
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              generalize actionEq : (joint actor).getD (⟨none⟩ : app.Action) = action
              intro owner entry member message emitted original zero
              by_cases old : entry ∈ execution.recall owner
              · rw [app.respond_environmentRecall]
                exact ih owner entry old message emitted original zero
              · have sameOwner : owner = actor := by
                  by_contra different
                  rw [app.respond_recall_other execution actor owner different action] at member
                  exact old member
                subst owner
                rcases action with ⟨transmission⟩
                cases transmission with
                | none =>
                    simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
                      List.mem_singleton] at member
                    rcases member with before | rfl
                    · exact (old before).elim
                    · cases emitted
                | some submission =>
                    simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
                      ↓reduceIte, List.mem_append, List.mem_singleton] at member
                    rcases member with before | rfl
                    · exact (old before).elim
                    · left
                      rw [app.respond_environmentRecall]
                      exact original_zero_clock_index seeds ⟨remaining, some actor, execution⟩
                        prior original zero
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, _selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro owner entry member message emitted original zero
                  rw [app.environmentStep_recall execution next command supported] at member
                  have entries := app.environmentStep_environmentRecall execution next command
                    supported
                  rcases ih owner entry member message emitted original zero with early | recorded
                  · change execution.environmentRecall.length ≤ 2 at early
                    by_cases stillEarly : next.environmentRecall.length ≤ 2
                    · exact Or.inl stillEarly
                    · right
                      have length : execution.environmentRecall.length = 2 := by
                        rw [entries, List.length_append, List.length_singleton] at stillEarly
                        omega
                      refine ⟨⟨execution.observeEnvironment app, command⟩, ?_, ?_⟩
                      · rw [entries, List.getElem?_append_right (by omega :
                          execution.environmentRecall.length ≤ 2), length, Nat.sub_self]
                        rfl
                      · have inputs := app.history_inputRecall initial horizon (family seeds) prior
                        have own : message ∈ app.outputs (execution.recall owner) :=
                          List.mem_filterMap.mpr ⟨entry, member, emitted⟩
                        rw [← inputs owner] at own
                        exact (List.mem_filter.mp own).1
                  · right
                    obtain ⟨snapshot, selected, input⟩ := recorded
                    have inside : 2 < execution.environmentRecall.length := by
                      by_contra outside
                      have absent : execution.environmentRecall[2]? = none :=
                        List.getElem?_eq_none (by omega)
                      rw [absent] at selected
                      cases selected
                    exact ⟨snapshot, by
                      rw [entries, List.getElem?_append_left inside]
                      exact selected, input⟩

/-- Every actual original clock-zero output belongs to the third command's
immutable input snapshot, once that command has been reached. -/
theorem raw_clock_zero_packet_in_snapshot (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ current.execution.recall owner)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (zero : entry.beforeView.application.1.publicView.clock = 0)
    (past : 3 ≤ current.execution.environmentRecall.length) :
    ∃ snapshot, current.execution.environmentRecall[2]? = some snapshot ∧
      message ∈ snapshot.beforeView.network.inputs := by
  rcases snapshot_recorded_history seeds trace owner entry member message emitted original zero
    with early | recorded
  · omega
  · exact recorded

def afterFirstTwo (aliceResponse bobResponse : app.Action) : app.Execution :=
  (bobFirst aliceResponse).respond app bob bobResponse

/-- The actual first two rounds retain both arbitrary raw responses. -/
theorem first_two_rounds (players : Player → app.Policy) (seeds : Seeds) :
    app.runRounds (family seeds) players 2 initialExecution =
      (players alice [] (aliceFirst.observe app alice)).bind fun aliceResponse =>
        (players bob [] ((bobFirst aliceResponse).observe app bob)).map
          (afterFirstTwo aliceResponse) := by
  have second (response : app.Action) :
      app.round (family seeds) players (aliceResponded response) =
        (players bob [] ((bobFirst response).observe app bob)).map (afterFirstTwo response) := by
    rw [ReactiveApplication.round, family_after_alice, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    change (players bob ((bobFirst response).recall bob)
      ((bobFirst response).observe app bob)).map ((bobFirst response).respond app bob) = _
    rw [bobFirst_recall]
    rfl
  rw [ReactiveApplication.runRounds, first_round, PMF.bind_map]
  congr 1
  funext response
  change (app.round (family seeds) players (aliceResponded response)).bind
    (app.runRounds (family seeds) players 0) = _
  rw [second]
  exact PMF.bind_pure _

private theorem response_inputs (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    ∃ emitted : Option (Message Player app.Payload),
      (execution.respond app owner response).network.inputs =
        execution.network.inputs ++ emitted.toList ∧
      ∀ message ∈ emitted.toList, message.sender = owner := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      refine ⟨none, ?_, ?_⟩
      · exact (List.append_nil _).symm
      · intro message impossible
        cases impossible
  | some submission =>
      refine ⟨some ⟨(owner, execution.network.nextSerial owner),
        app.packet (app.submit execution.application owner submission) owner
          (execution.network.known owner) submission⟩, rfl, ?_⟩
      intro message member
      cases (List.mem_singleton.mp member).symm
      rfl

private theorem option_input_unique
    (emitted : Option (Message Player app.Payload))
    (left right : Message Player app.Payload)
    (leftInput : left ∈ emitted.toList) (rightInput : right ∈ emitted.toList) : left = right := by
  cases emitted with
  | none => cases leftInput
  | some message =>
      exact (List.mem_singleton.mp leftInput).trans (List.mem_singleton.mp rightInput).symm

private theorem afterFirstTwo_unique_owner (first second : app.Action) (owner : Player)
    (left right : Message Player app.Payload)
    (leftInput : left ∈ (afterFirstTwo first second).network.inputs)
    (rightInput : right ∈ (afterFirstTwo first second).network.inputs)
    (leftOwner : left.sender = owner) (rightOwner : right.sender = owner) : left = right := by
  obtain ⟨firstOutput, firstInputs, firstSender⟩ := response_inputs aliceFirst alice first
  obtain ⟨secondOutput, secondInputs, secondSender⟩ := response_inputs (bobFirst first) bob second
  have bobInputs : (bobFirst first).network.inputs =
      (aliceResponded first).network.inputs := rfl
  have initialInputs : aliceFirst.network.inputs = [] := by rw [aliceFirst_network]; rfl
  change (aliceResponded first).network.inputs = aliceFirst.network.inputs ++ firstOutput.toList
    at firstInputs
  change (afterFirstTwo first second).network.inputs =
    (bobFirst first).network.inputs ++ secondOutput.toList at secondInputs
  rw [secondInputs, bobInputs, firstInputs, initialInputs, List.nil_append]
    at leftInput rightInput
  rcases List.mem_append.mp leftInput with leftFirst | leftSecond
  · rcases List.mem_append.mp rightInput with rightFirst | rightSecond
    · exact option_input_unique firstOutput left right leftFirst rightFirst
    · have same : alice = bob := (firstSender left leftFirst).symm.trans
        (leftOwner.trans (rightOwner.symm.trans (secondSender right rightSecond)))
      exact ((by decide : alice ≠ bob) same).elim
  · rcases List.mem_append.mp rightInput with rightFirst | rightSecond
    · have same : bob = alice := (secondSender left leftSecond).symm.trans
        (leftOwner.trans (rightOwner.symm.trans (firstSender right rightFirst)))
      exact ((by decide : alice ≠ bob) same.symm).elim
    · exact option_input_unique secondOutput left right leftSecond rightSecond

/-- The original snapshot contains at most one envelope from each owner,
even when both initial responses use arbitrary malformed raw submissions. -/
theorem first_snapshot_unique_owner (players : Player → app.Policy) (seeds : Seeds)
    (extra : Nat) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seeds) players (3 + extra)
      initialExecution).support)
    (snapshot : app.EnvironmentEntry) (selected : execution.environmentRecall[2]? = some snapshot)
    (owner : Player) (left right : Message Player (CommitAttemptPacket graph))
    (leftInput : left ∈ snapshot.beforeView.network.inputs)
    (rightInput : right ∈ snapshot.beforeView.network.inputs)
    (leftOwner : left.sender = owner) (rightOwner : right.sender = owner) : left = right := by
  rw [show 3 + extra = 2 + (extra + 1) by omega, app.runRounds_add,
    first_two_rounds, PMF.bind_bind] at reached
  obtain ⟨first, _firstSupport, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [PMF.bind_map] at afterFirst
  obtain ⟨second, _secondSupport, remaining⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  change execution ∈ (app.runRounds (family seeds) players (extra + 1)
    (afterFirstTwo first second)).support at remaining
  rw [ReactiveApplication.runRounds.eq_def] at remaining
  obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ remaining)
  obtain ⟨command, _chosen, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  obtain ⟨later, recalled, _length⟩ :=
    app.runRounds_environmentRecall_append (family seeds) players extra middle execution tail
  have complete : execution.environmentRecall = (afterFirstTwo first second).environmentRecall ++
      [⟨(afterFirstTwo first second).observeEnvironment app, command⟩] ++ later := by
    rw [recalled, app.dispatch_environmentRecall players command _ middle dispatched]
  have snapshotEq : snapshot = ⟨(afterFirstTwo first second).observeEnvironment app, command⟩ := by
    apply Option.some.inj
    rw [← selected, complete, afterFirstTwo, app.respond_environmentRecall,
      bobFirst_environmentRecall]
    rfl
  subst snapshot
  exact afterFirstTwo_unique_owner first second owner left right leftInput rightInput leftOwner
    rightOwner

end Vegas.Examples.CommitSeedSignalling
