/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapFiberSum
import Vegas.Game.OnePacketOwnerSwap

/-! # The owner swap keeps the message bounds

Along every history of the one-packet game, every openable candidate in the
contract's catalogue is within the message bounds, when the bounds cover every
value of every initial binding input (`Vegas.candidate_mem_values_of_trace`).
Initially an openable candidate is the typed value of an initial binding input
of its owner. Afterwards a value becomes openable only when a submission of the
menu prepares it, and the menu admits only bounded opening data; freezing only
makes fresh candidates unopenable, and inclusion and environment service only
freeze.

Hence the owner swap between two views of one player at two histories of the
one-packet game keeps the message bounds (`Vegas.ownerSwap_bounded`): each pair
it transposes consists of two openable candidates of the views.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- Every openable candidate of the catalogue is within the message bounds. -/
def CandidatesWithin (bounds : MessageBounds (graph setup))
    (state : EventGraphRuntime.State (graph setup)) : Prop :=
  ∀ handle raw, state.candidates.lookup handle = .openable raw → raw ∈ bounds.values

/-- An openable candidate after a preparation is the prepared value or was
openable before. -/
private theorem openable_of_prepare
    (candidates : CommitmentCandidates Player (CandidateSlot (graph setup)) (Raw L))
    (owner : Player) (slot : CandidateSlot (graph setup)) (value : Raw L)
    (handle : Handle (graph setup)) (raw : Raw L)
    (found : (candidates.prepare owner slot value).lookup handle = .openable raw) :
    raw = value ∨ candidates.lookup handle = .openable raw := by
  by_cases same : handle = (owner, slot)
  · subst same
    rw [CommitmentCandidates.lookup_prepare_self] at found
    cases before : candidates.lookup (owner, slot) <;> rw [before] at found <;> cases found
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [candidates.lookup_prepare_other owner slot value handle same] at found
    exact Or.inr found

/-- Freezing creates no openable candidate. -/
private theorem openable_of_freeze
    (candidates : CommitmentCandidates Player (CandidateSlot (graph setup)) (Raw L))
    (frozen handle : Handle (graph setup)) (raw : Raw L)
    (found : (candidates.freeze frozen).lookup handle = .openable raw) :
    candidates.lookup handle = .openable raw := by
  by_cases same : handle = frozen
  · subst same
    rw [CommitmentCandidates.lookup_freeze_self] at found
    cases before : candidates.lookup handle <;> rw [before] at found <;> cases found
    rfl
  · rwa [candidates.lookup_freeze_other frozen handle same] at found

/-- Submitting an envelope creates no openable candidate. -/
private theorem openable_of_submitStep (state : EventGraphRuntime.State (graph setup))
    (who : Player) (packet : Payload (graph setup)) (handle : Handle (graph setup))
    (raw : Raw L) (found : (submitStep state who packet).candidates.lookup handle = .openable raw) :
    state.candidates.lookup handle = .openable raw := by
  cases packet with
  | commitment event candidate =>
      simp only [submitStep] at found
      split_ifs at found
      · exact openable_of_freeze _ _ _ _ found
      · exact found
  | opening | malformed => exact found

/-- Registering a submission makes openable only its own opening data. -/
private theorem openable_of_register (submission : Submission (graph setup))
    (state : EventGraphRuntime.State (graph setup)) (who : Player)
    (handle : Handle (graph setup)) (raw : Raw L)
    (found : (submission.register state who).candidates.lookup handle = .openable raw) :
    submission.opening = some raw ∨ state.candidates.lookup handle = .openable raw := by
  rcases submission with ⟨packet, opening⟩
  cases opening with
  | none =>
      right
      cases packet with
      | commitment event candidate =>
          rcases candidate with ⟨owner, input | serial⟩ <;> exact found
      | opening | malformed => exact found
  | some value =>
      cases packet with
      | commitment event candidate =>
          rcases candidate with ⟨owner, input | serial⟩
          · exact Or.inr found
          · simp only [Submission.register] at found
            split_ifs at found
            · rcases openable_of_prepare _ _ _ _ _ _ found with same | old
              · subst same
                exact Or.inl rfl
              · exact Or.inr old
            · exact Or.inr found
      | opening | malformed => exact Or.inr found

omit [IExpr.ResultTypes L] in
/-- A typed initial value makes openable only a value of a binding field. -/
private theorem openable_of_candidateOfValue (owner : Player)
    (kind : EventGraph.EventField Player L) (value : kind.Value) (raw : Raw L)
    (found : State.candidateOfValue owner kind value = .openable raw) :
    ∃ (inputOwner : Player) (payload : L.Ty) (typed : L.Val payload),
      kind = .binding inputOwner payload ∧ raw = ⟨payload, typed⟩ := by
  cases kind with
  | publicData | publication | privateInput => cases found
  | binding inputOwner payload =>
      simp only [State.candidateOfValue] at found
      split_ifs at found
      cases value with
      | failure => cases found
      | success typed => cases found; exact ⟨inputOwner, payload, typed, rfl, rfl⟩

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Inclusion and environment service create no openable candidate. -/
private theorem openable_of_environmentStep
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (handle : Handle (graph setup)) (raw : Raw L)
    (found : next.application.candidates.lookup handle = .openable raw) :
    execution.application.candidates.lookup handle = .openable raw := by
  let app := application setup leaks
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact found
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact found
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      revert found
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases lookedUp : execution.network.lookup id with
      | none => exact fun held => held
      | some message =>
          change ((app.handle execution.application message).getD
            execution.application).candidates.lookup handle = .openable raw → _
          cases accepted : app.handle execution.application message with
          | none => exact fun held => held
          | some next =>
              intro found
              have call := reactiveHandle_call accepted
              cases packet : message.payload.call with
              | malformed value =>
                  rw [packet] at call
                  simp [EventGraphRuntime.handle] at call
              | opening named other value =>
                  rw [packet] at call
                  have tables := handle_resolution_tables (runtime setup)
                    execution.application next _ (fun _ _ same => by cases same) call
                  change next.candidates.lookup handle = .openable raw at found
                  rwa [tables.2] at found
              | commitment named other =>
                  rw [packet] at call
                  have tables := handle_commitment_tables (runtime setup)
                    execution.application next _ named other call
                  change next.candidates.lookup handle = .openable raw at found
                  rw [tables.1] at found
                  exact openable_of_freeze _ _ _ _ found
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state.candidates.lookup handle = .openable raw at found
      rwa [(environmentStep_tables (runtime setup) execution.application state command
        changed).2] at found

variable {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Every initial state of the default runtime has its openable candidates
within the bounds when the bounds cover the initial binding inputs. -/
private theorem candidatesWithin_initial (covers : bounds.CoversInputValues)
    (state : EventGraphRuntime.State (graph setup)) (member : state ∈ (initialLaw setup).support) :
    CandidatesWithin bounds state := by
  rw [initialLaw, serviceInitialLaw, PMF.support_map] at member
  obtain ⟨initial, _, rfl⟩ := member
  rintro ⟨owner, slot⟩ raw found
  rw [EventGraphRuntime.State.initial_candidate] at found
  cases slot with
  | prepared serial => cases found
  | initial input =>
      obtain ⟨inputOwner, payload, typed, layoutEq, rfl⟩ :=
        openable_of_candidateOfValue owner _ _ raw found
      exact covers input inputOwner payload layoutEq typed

/-- A transposition of two values within the bounds keeps the bounds. -/
private theorem pairSwap_mem_values {pair : Option (Raw L × Raw L)}
    (within : ∀ left right, pair = some (left, right) →
      left ∈ bounds.values ∧ right ∈ bounds.values)
    {raw : Raw L} (member : raw ∈ bounds.values) :
    EventGraph.pairSwap pair raw ∈ bounds.values := by
  cases pair with
  | none => exact member
  | some pair =>
      rcases pair with ⟨left, right⟩
      obtain ⟨leftWithin, rightWithin⟩ := within left right rfl
      simp only [EventGraph.pairSwap]
      by_cases isLeft : raw = left
      · subst isLeft
        rw [@Equiv.swap_apply_left _ (fun a b => Classical.propDecidable (a = b))]
        exact rightWithin
      · by_cases isRight : raw = right
        · subst isRight
          rw [@Equiv.swap_apply_right _ (fun a b => Classical.propDecidable (a = b))]
          exact leftWithin
        · rw [@Equiv.swap_apply_of_ne_of_ne _ (fun a b => Classical.propDecidable (a = b)) _ _ _
            isLeft isRight]
          exact member

/-- **The owner swap keeps the bounds** when the openable candidates of both
views are within the bounds. -/
theorem ownerSwap_bounded_of_candidates (who : Player)
    (first second : EventGraphRuntime.PlayerView (graph setup))
    (firstWithin : ∀ slot raw, first.candidates slot = .openable raw → raw ∈ bounds.values)
    (secondWithin : ∀ slot raw, second.candidates slot = .openable raw → raw ∈ bounds.values) :
    ∀ handle raw, raw ∈ bounds.values →
      (ownerSwap who first second).raw handle raw ∈ bounds.values := by
  intro handle raw member
  change EventGraph.pairSwap (ownerHandlePairs who first second handle) raw ∈ _
  refine pairSwap_mem_values (fun left right paired => ?_) member
  unfold ownerHandlePairs at paired
  split_ifs at paired
  split at paired
  · rename_i firstLeft secondRight firstFound secondFound
    split_ifs at paired
    cases paired
    exact ⟨firstWithin _ _ firstFound, secondWithin _ _ secondFound⟩
  · cases paired

variable [Fintype Player]

variable (leaks bounds) in
/-- Openable candidates stay within the bounds along every one-packet response
and every environment step. -/
private theorem candidatesWithin_serviceInvariant :
    (bounds.onePacketMenu (runtime setup) leaks).ServiceInvariant scheduler
      (fun execution => CandidatesWithin bounds execution.application) where
  respond execution who action valid member := by
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid
    | some material =>
        have allowed := ((bounds.menu_mem (runtime setup) leaks who _ _ _).mp
          ((bounds.mem_onePacketActions (runtime setup) leaks who _ _ _).mp member).1).1.1.2
        intro handle raw found
        change (submitStep (material.call.register execution.application who) who
          material.call.packet).candidates.lookup handle = .openable raw at found
        rcases openable_of_register material.call execution.application who handle raw
          (openable_of_submitStep _ who _ handle raw found) with opened | old
        · change bounds.AllowsOpening material.call.opening at allowed
          rw [opened] at allowed
          exact allowed
        · exact valid handle raw old
  environment execution next command valid _ reached handle raw found :=
    valid handle raw (openable_of_environmentStep execution next command reached handle raw found)

/-- **Openable candidates are within the bounds.** Along every history of the
one-packet game, every openable candidate of the catalogue is within the message
bounds, when the bounds cover every value of every initial binding input. -/
theorem candidate_mem_values_of_trace (covers : bounds.CoversInputValues)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {handle : Handle (graph setup)} {raw : Raw L}
    (found : control.execution.application.candidates.lookup handle = .openable raw) :
    raw ∈ bounds.values :=
  (candidatesWithin_serviceInvariant leaks bounds).history (initialLaw setup) horizon
    (fun state member => candidatesWithin_initial covers state member) trace handle raw found

/-- **The owner swap between two views of one-packet histories keeps the
bounds.** For two histories of the one-packet game, the owner swap between the
views of `who` at their end states moves values within the message bounds, when
the bounds cover every value of every initial binding input. -/
theorem ownerSwap_bounded (covers : bounds.CoversInputValues) (who : Player)
    {firstControl secondControl : (application setup leaks).Control}
    (firstTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some firstControl))
    (secondTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some secondControl)) :
    ∀ handle raw, raw ∈ bounds.values →
      (ownerSwap who (firstControl.execution.observe (application setup leaks) who).application
        (secondControl.execution.observe (application setup leaks) who).application).raw
          handle raw ∈ bounds.values :=
  ownerSwap_bounded_of_candidates who _ _
    (fun _ _ found => candidate_mem_values_of_trace covers firstTrace found)
    (fun _ _ found => candidate_mem_values_of_trace covers secondTrace found)

end Vegas
