/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveTrafficContinuation
import Interaction.ReactiveSubmissionSerial

/-! # Earlier signed inputs along reactive continuations

Every author's serials follow emission order at every legal prefix, under
arbitrary responses and adaptive scheduling. Once an input is retained, its
earlier same-author inputs cannot change along a continuation. The statement
is independent of packet contents, verdicts, and the application state.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Each principal's network inputs carry the serials `0, 1, …` in emission
order. -/
def Execution.InputSerialsInOrder (execution : app.Execution) : Prop :=
  ∀ who, (execution.network.inputs.filter fun input => input.sender = who).map
    (fun input => input.id.2) = List.range (execution.network.nextSerial who)

theorem inputSerialsInOrderInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.InputSerialsInOrder app) where
  respond execution who action valid := by
    intro observer
    have earlier := valid observer
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => simpa only [Execution.respond] using earlier
    | some submission =>
        by_cases same : observer = who
        · subst observer
          simp only [Message.sender] at earlier
          simp [Execution.respond, MessageNetwork.submit, List.filter_append, Message.sender,
            earlier, List.range_succ]
        · simp only [Message.sender] at earlier
          simp [Execution.respond, MessageNetwork.submit, List.filter_append, Message.sender,
            same, Ne.symm same, earlier]
  environment execution next command valid _ reached := by
    intro observer
    rw [app.environmentStep_inputs execution next command reached,
      app.environmentStep_nextSerial execution next command reached]
    exact valid observer

theorem inputSerialsInOrder_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.InputSerialsInOrder app) state :=
  (app.inputSerialsInOrderInvariant scheduler).history initial horizon
    (fun _ _ _ => rfl) trace

variable {app}

/-- The author's actual outputs suffice for every earlier-input test, even for
a packet not yet submitted. Serial-order and next-serial assumptions are unnecessary. -/
theorem Execution.InputRecall.earlier_inputs_iff_outputs {execution : app.Execution}
    (recalled : execution.InputRecall app) (message other : Message Principal app.Payload) :
    (other ∈ execution.network.inputs ∧ other.sender = message.sender ∧
      other.id.2 < message.id.2) ↔
    (other ∈ app.outputs (execution.recall message.sender) ∧ other.sender = message.sender ∧
      other.id.2 < message.id.2) := by
  rw [← recalled message.sender]
  constructor
  · rintro ⟨member, owner, lower⟩
    exact ⟨List.mem_filter.mpr ⟨member, by simp [owner]⟩, owner, lower⟩
  · rintro ⟨member, owner, lower⟩
    exact ⟨(List.mem_filter.mp member).1, owner, lower⟩

/-- Every input's serial is below its sender's next serial. -/
theorem Execution.InputSerialsInOrder.serial_lt {execution : app.Execution}
    (valid : execution.InputSerialsInOrder app) {input : Message Principal app.Payload}
    (member : input ∈ execution.network.inputs) :
    input.id.2 < execution.network.nextSerial input.sender := by
  have mapped : input.id.2 ∈ (execution.network.inputs.filter fun other =>
      other.sender = input.sender).map (fun other => other.id.2) :=
    List.mem_map.mpr ⟨input, List.mem_filter.mpr ⟨member, by simp⟩, rfl⟩
  rw [valid input.sender] at mapped
  exact List.mem_range.mp mapped

/-- Inputs appended after `before` carry serials at least the sender's next
serial at `before`. So an input of a later execution with a lower serial was
already an input of `before`. -/
theorem Execution.InputSerialsInOrder.mem_of_prefix {before after : app.Execution}
    (beforeValid : before.InputSerialsInOrder app) (afterValid : after.InputSerialsInOrder app)
    (prefixOf : before.network.inputs <+: after.network.inputs)
    {input : Message Principal app.Payload} (member : input ∈ after.network.inputs)
    (lower : input.id.2 < before.network.nextSerial input.sender) :
    input ∈ before.network.inputs := by
  obtain ⟨rest, split⟩ := prefixOf
  rw [← split] at member
  rcases List.mem_append.mp member with old | new
  · exact old
  · exfalso
    have whole := afterValid input.sender
    rw [← split, List.filter_append, List.map_append, beforeValid input.sender] at whole
    have nodup := whole ▸ List.nodup_range
    have inRest : input.id.2 ∈ (rest.filter fun other => other.sender = input.sender).map
        (fun other => other.id.2) :=
      List.mem_map.mpr ⟨input, List.mem_filter.mpr ⟨new, by simp⟩, rfl⟩
    exact List.disjoint_of_nodup_append nodup (List.mem_range.mpr lower) inRest

variable (app)

/-- Every continuation retains an input and exactly its earlier same-author
inputs. This includes arbitrary raw responses, rejection and passive sampling. -/
theorem earlier_inputs_reaches {initial : PMF app.State} {horizon : Nat}
    {scheduler : app.Scheduler} {first last : (app.protocol initial horizon scheduler).History}
    {fuel : Nat} (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (before after : app.Control) (firstEq : first.state = some before)
    (lastEq : last.state = some after) (message : Message Principal app.Payload)
    (present : message ∈ before.execution.network.inputs) :
    message ∈ after.execution.network.inputs ∧ ∀ other,
      (other ∈ after.execution.network.inputs ∧ other.sender = message.sender ∧
        other.id.2 < message.id.2) ↔
      (other ∈ before.execution.network.inputs ∧ other.sender = message.sender ∧
        other.id.2 < message.id.2) := by
  have traffic := app.stateTraffic_reaches initial horizon scheduler path
  have firstInputs := app.stateTraffic_inputs initial horizon scheduler first.trace
  have lastInputs := app.stateTraffic_inputs initial horizon scheduler last.trace
  have firstOrder := app.inputSerialsInOrder_history scheduler initial horizon first.trace
  have lastOrder := app.inputSerialsInOrder_history scheduler initial horizon last.trace
  rw [firstEq] at firstInputs firstOrder traffic
  rw [lastEq] at lastInputs lastOrder traffic
  have prefixOf : before.execution.network.inputs <+: after.execution.network.inputs := by
    have mapped := traffic.map TrafficRecord.envelope
    rw [firstInputs, lastInputs] at mapped
    exact mapped
  refine ⟨prefixOf.subset present, fun other => ⟨?_, ?_⟩⟩
  · rintro ⟨member, owner, lower⟩
    refine ⟨firstOrder.mem_of_prefix lastOrder prefixOf member ?_, owner, lower⟩
    rw [owner]
    exact lower.trans (firstOrder.serial_lt present)
  · rintro ⟨member, owner, lower⟩
    exact ⟨prefixOf.subset member, owner, lower⟩

/-- A verdict using earlier same-author inputs is locally testable from actual recall. -/
theorem own_verdict_iff_outputs
    (verdict : List (Message Principal app.Payload) → Message Principal app.Payload → Bool)
    (congruent : ∀ left right message,
      (∀ other, (other ∈ left ∧ other.sender = message.sender ∧ other.id.2 < message.id.2) ↔
        (other ∈ right ∧ other.sender = message.sender ∧ other.id.2 < message.id.2)) →
      verdict left message = verdict right message)
    (execution : app.Execution) (recalled : execution.InputRecall app) (who : Principal) :
    (∀ message ∈ execution.network.inputs, message.sender = who →
      verdict execution.network.inputs message = true) ↔
      ∀ message ∈ app.outputs (execution.recall who),
        verdict (app.outputs (execution.recall who)) message = true := by
  classical
  have localVerdict (message : Message Principal app.Payload) (owner : message.sender = who) :
      verdict execution.network.inputs message =
        verdict (app.outputs (execution.recall who)) message := by
    apply congruent
    intro other
    simpa only [owner] using recalled.earlier_inputs_iff_outputs message other
  constructor
  · intro clean message present
    rw [← recalled who] at present
    obtain ⟨member, owner⟩ := List.mem_filter.mp present
    have owned : message.sender = who := by simpa using owner
    rw [← localVerdict message owned]
    exact clean message member owned
  · intro clean message member owner
    rw [localVerdict message owner]
    apply clean
    rw [← recalled who]
    exact List.mem_filter.mpr ⟨member, by simpa using owner⟩

end Interaction.ReactiveApplication
