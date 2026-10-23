/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComponentSteps

/-! # Fresh prepared slots are public

A prepared slot of a player stops being fresh only when that player submits a
commitment naming it: registration and freezing touch only the sender's own
handle, inclusion freezes only a handle whose commitment was already submitted,
and no other step changes the catalogue. So at every legal history of the
default runtime, under arbitrary responses and every scheduler, a player's
prepared slot is fresh exactly when none of its submitted packets commits to
it (`Vegas.preparedFresh_history`). Submitted packets are public inputs, so the
canonical slot a player's decisions use is a function of the public view and
the inputs (`Vegas.canonicalFreshSlot_eq_publicFreshSlot`): the slot of a
canonical commitment reveals nothing private beyond what the operational state
records.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Generic

variable {graph : EventGraph Player L}

/-- A packet of `who` among `inputs` commits to its prepared slot `serial`. -/
def SlotCommitted (inputs : List (Message Player (WitnessedPacket graph))) (who : Player)
    (serial : Nat) : Prop :=
  ∃ message ∈ inputs, message.sender = who ∧
    ∃ event, message.payload.call = .commitment event (who, .prepared serial)

open Classical in
/-- The canonical slot read from public data: the slot numbered by the player's
completed bindings when no packet of the player commits to it, and otherwise
the least such slot. -/
def publicFreshSlot (inputs : List (Message Player (WitnessedPacket graph))) (who : Player)
    (count : Nat) : Option Nat :=
  if ¬ SlotCommitted inputs who count then some count
  else if uncommitted : ∃ serial, ¬ SlotCommitted inputs who serial then
    some (Nat.find uncommitted)
  else none

/-- Every prepared slot is fresh exactly when no submitted packet of its owner
commits to it. -/
def PreparedFresh (state : EventGraphRuntime.State graph)
    (inputs : List (Message Player (WitnessedPacket graph))) : Prop :=
  ∀ who serial, state.candidates.lookup (who, .prepared serial) = .fresh ↔
    ¬ SlotCommitted inputs who serial

open Classical in
/-- **The canonical slot is public.** Where prepared freshness holds, the
canonical slot of a player's view is read from its public view and the
inputs. -/
theorem canonicalFreshSlot_eq_publicFreshSlot {state : EventGraphRuntime.State graph}
    {inputs : List (Message Player (WitnessedPacket graph))}
    (fresh : PreparedFresh state inputs) (who : Player) :
    canonicalFreshSlot who (state.playerView who) =
      publicFreshSlot inputs who ((state.playerView who).publicView.bindingCount who) := by
  have same : ∀ serial, (state.playerView who).candidates (.prepared serial) = .fresh ↔
      ¬ SlotCommitted inputs who serial := fresh who
  unfold canonicalFreshSlot publicFreshSlot reactiveFreshSlot
  by_cases current : SlotCommitted inputs who ((state.playerView who).publicView.bindingCount who)
  · have notFresh : ¬ (state.playerView who).candidates
        (.prepared ((state.playerView who).publicView.bindingCount who)) = .fresh :=
      fun isFresh => (same _).mp isFresh current
    simp only [notFresh, current, not_true_eq_false, ↓reduceIte]
    by_cases exists_ : ∃ serial, ¬ SlotCommitted inputs who serial
    · have freshExists : ∃ serial, (state.playerView who).candidates (.prepared serial) = .fresh :=
        let ⟨serial, uncommitted⟩ := exists_
        ⟨serial, (same serial).mpr uncommitted⟩
      simp only [freshExists, exists_, ↓reduceDIte]
      congr 1
      apply le_antisymm
      · exact Nat.find_min' freshExists ((same _).mpr (Nat.find_spec exists_))
      · exact Nat.find_min' exists_ ((same _).mp (Nat.find_spec freshExists))
    · have noFresh : ¬ ∃ serial, (state.playerView who).candidates (.prepared serial) = .fresh :=
        fun ⟨serial, isFresh⟩ => exists_ ⟨serial, (same serial).mp isFresh⟩
      simp only [noFresh, exists_, ↓reduceDIte]
  · have isFresh := (same _).mpr current
    simp only [isFresh, current, not_false_eq_true, ↓reduceIte]

omit [DecidableEq Player] in
/-- Appending a packet commits a slot of `who` exactly when an earlier packet
did, or the new packet is `who`'s commitment to it. -/
theorem slotCommitted_append (inputs : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph)) (who : Player) (serial : Nat) :
    SlotCommitted (inputs ++ [message]) who serial ↔ SlotCommitted inputs who serial ∨
      (message.sender = who ∧ ∃ event, message.payload.call = .commitment event
        (who, .prepared serial)) := by
  unfold SlotCommitted
  constructor
  · rintro ⟨other, member, owner, committed⟩
    rcases List.mem_append.mp member with old | new
    · exact Or.inl ⟨other, old, owner, committed⟩
    · rw [List.mem_singleton.mp new] at owner committed
      exact Or.inr ⟨owner, committed⟩
  · rintro (⟨other, member, owner, committed⟩ | ⟨owner, committed⟩)
    · exact ⟨other, List.mem_append_left _ member, owner, committed⟩
    · exact ⟨message, List.mem_append_right _ (List.mem_singleton.mpr rfl), owner, committed⟩

end Generic

section Default

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A submission keeps freshness of prepared slots in step with the inputs. -/
theorem preparedFresh_submit (state : EventGraphRuntime.State (graph setup))
    (inputs : List (Message Player (WitnessedPacket (graph setup)))) (who : Player)
    (material : (application setup leaks).Submission)
    (message : Message Player (WitnessedPacket (graph setup)))
    (sender : message.sender = who) (call : message.payload.call = material.call.packet)
    (fresh : PreparedFresh state inputs) :
    PreparedFresh ((application setup leaks).submit state who material) (inputs ++ [message]) := by
  intro owner serial
  rw [slotCommitted_append]
  by_cases same : owner = who
  · subst same
    change (submitStep (material.call.register state owner) owner
      material.call.packet).candidates.lookup (owner, .prepared serial) = .fresh ↔ _
    rw [Submission.candidateAfter_eq]
    unfold Submission.candidateAfter
    have old := fresh owner serial
    cases packet : material.call.packet with
    | commitment event handle =>
        rcases handle with ⟨handleOwner, slot⟩
        by_cases target : handleOwner = owner ∧ (Slot.prepared serial :
            CandidateSlot (graph setup)) = slot
        · obtain ⟨rfl, rfl⟩ := target
          have newCommitted : message.sender = handleOwner ∧ ∃ event',
              message.payload.call = .commitment event' (handleOwner, .prepared serial) :=
            ⟨sender, event, call.trans packet⟩
          refine ⟨fun isFresh => ?_, fun uncommitted => (uncommitted (Or.inr newCommitted)).elim⟩
          exfalso
          simp only [true_and, ↓reduceIte] at isFresh
          cases meaning : state.candidates.lookup (handleOwner, Slot.prepared serial) <;>
            rw [meaning] at isFresh
          · cases opening : material.call.opening <;> simp [opening] at isFresh
          · cases isFresh
          · cases isFresh
        · simp only [target, ↓reduceIte, old]
          constructor
          · intro uncommitted committed
            rcases committed with committed | ⟨_, otherEvent, otherCall⟩
            · exact uncommitted committed
            · rw [call, packet] at otherCall
              cases otherCall
              exact target ⟨rfl, rfl⟩
          · intro uncommitted committed
            exact uncommitted (Or.inl committed)
    | opening event handle raw =>
        simp only [old]
        constructor
        · intro uncommitted committed
          rcases committed with committed | ⟨_, otherEvent, otherCall⟩
          · exact uncommitted committed
          · rw [call, packet] at otherCall
            cases otherCall
        · intro uncommitted committed
          exact uncommitted (Or.inl committed)
    | malformed raw =>
        simp only [old]
        constructor
        · intro uncommitted committed
          rcases committed with committed | ⟨_, otherEvent, otherCall⟩
          · exact uncommitted committed
          · rw [call, packet] at otherCall
            cases otherCall
        · intro uncommitted committed
          exact uncommitted (Or.inl committed)
  · have unchanged : ((application setup leaks).submit state who material).candidates.lookup
        (owner, .prepared serial) = state.candidates.lookup (owner, .prepared serial) := by
      change (submitStep (material.call.register state who) who
        material.call.packet).candidates.lookup (owner, .prepared serial) = _
      rw [submitStep_lookup_other _ who owner same]
      rw [Submission.register_eq]
      split
      · rfl
      · rename_i command _
        have view := privateStep_playerView_other state who owner same command
        exact congrFun (congrArg EventGraphRuntime.PlayerView.candidates view) _
    rw [unchanged, fresh owner serial]
    constructor
    · intro uncommitted committed
      rcases committed with committed | ⟨otherSender, _⟩
      · exact uncommitted committed
      · exact same (otherSender.symm.trans sender)
    · intro uncommitted committed
      exact uncommitted (Or.inl committed)

/-- A scheduler command keeps every prepared slot's meaning: inclusion freezes
only the handle of a commitment already submitted, which is no longer fresh. -/
theorem environment_lookup_prepared (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (facts : SettledFacts setup leaks execution)
    (fresh : PreparedFresh execution.application execution.network.inputs)
    (owner : Player) (serial : Nat) :
    next.application.candidates.lookup (owner, .prepared serial) =
      execution.application.candidates.lookup (owner, .prepared serial) := by
  cases command with
  | activate who =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
  | wait =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | application command =>
      obtain ⟨changed, _⟩ := applicationStep_facts execution next command reached
      rw [(environmentStep_tables (runtime setup) _ _ command changed).2]
  | «include» id =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (execution.includePending (application setup leaks)
        id).application.candidates.lookup _ = _
      cases found : execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
      | some message =>
          obtain ⟨identified, present, _⟩ := includePending_found execution.network id message found
          cases accepted : (application setup leaks).handle execution.application message with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, accepted, Option.getD_none]
          | some after =>
              have applicationEq :
                  (execution.includePending (application setup leaks) id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              rw [applicationEq]
              have call := reactiveHandle_call accepted
              cases packet : message.payload.call with
              | malformed raw =>
                  rw [packet] at call
                  simp [handle] at call
              | opening event handle raw =>
                  rw [packet] at call
                  rw [(handle_resolution_tables (runtime setup) _ _ _
                    (fun _ _ same => by cases same) call).2]
              | commitment event handle =>
                  rw [packet] at call
                  obtain ⟨frozen, _, handleOwner⟩ :=
                    handle_commitment_tables (runtime setup) _ _ _ event handle call
                  rw [frozen]
                  by_cases same : (owner, (Slot.prepared serial : CandidateSlot (graph setup))) =
                    handle
                  · subst same
                    apply CommitmentCandidates.lookup_freeze_eq_of_not_fresh
                    intro isFresh
                    apply (fresh owner serial).mp isFresh
                    exact ⟨message, facts.carried.pending message present, handleOwner.symm,
                      event, packet⟩
                  · exact CommitmentCandidates.lookup_freeze_other _ _ _ same

/-- Prepared freshness, with the settled facts it rests on. -/
def FreshFacts (execution : (application setup leaks).Execution) : Prop :=
  SettledFacts setup leaks execution ∧
    PreparedFresh execution.application execution.network.inputs

theorem freshFacts_serviceInvariant (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler FreshFacts where
  respond execution who action valid := by
    refine ⟨settledFacts_respond execution valid.1 who action, ?_⟩
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid.2
    | some material =>
        exact preparedFresh_submit execution.application execution.network.inputs who material _
          rfl rfl valid.2
  environment execution next command valid _ reached := by
    refine ⟨settledFacts_environment execution next command valid.1 reached, ?_⟩
    intro owner serial
    rw [environment_lookup_prepared execution next command reached valid.1 valid.2 owner serial,
      (environmentStep_shape setup leaks execution next command reached).1]
    exact valid.2 owner serial

/-- **Prepared freshness at every history.** At every legal history of the
default runtime from its initial law, under arbitrary responses and every
scheduler, a prepared slot is fresh exactly when no submitted packet of its
owner commits to it. -/
theorem preparedFresh_history (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    PreparedFresh control.execution.application control.execution.network.inputs :=
  ((freshFacts_serviceInvariant scheduler).history (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨settledFacts_initial _, fun owner serial => ?_⟩
      change (EventGraphRuntime.State.initial (graph := graph setup) _).candidates.lookup
        (owner, .prepared serial) = .fresh ↔ ¬ SlotCommitted [] owner serial
      rw [EventGraphRuntime.State.initial_candidate]
      simp [SlotCommitted])
    trace).2

end Default

end Vegas
