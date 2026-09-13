/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionPolicy
import Interaction.SealedResolutionBinding
import Interaction.SealedKnowledge

/-! # Partial disclosure with public clocks and nullable resolution

The relation retains the untimed kernel's occupancy, known-value, and packet
conditions, and also equates the complete public resolution state. The latter
includes readiness timestamps, the clock, and default events. Equal native
observations therefore include pending traffic and timeout metadata.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {runtime : SealedResolution Principal Value}

structure KnowledgeRelated (runtime : SealedResolution Principal Value)
    (known : CommitmentHandle Principal Nat → Prop)
    (left right : runtime.messageApplication.State) : Prop where
  sealed : SealedProgram.KnowledgeRelated runtime.program known
    (runtime.eventState left) (runtime.eventState right)
  publicState : left.application.visible = right.application.visible

variable {known : CommitmentHandle Principal Nat → Prop}
variable {left right : runtime.messageApplication.State}

theorem KnowledgeRelated.initial : KnowledgeRelated runtime known
    (MessageApplication.State.initial runtime.messageApplication runtime.initial)
    (MessageApplication.State.initial runtime.messageApplication runtime.initial) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, MessagePool.Satisfies.empty⟩, rfl⟩

theorem KnowledgeRelated.observe_eq (related : KnowledgeRelated runtime known left right)
    (who : Principal) :
    MessageApplication.State.observe _ left who =
      MessageApplication.State.observe _ right who := by
  have hp : left.pool = right.pool := related.sealed.pool
  have hr : left.receipts = right.receipts := related.sealed.receipts
  simp only [MessageApplication.State.observe, messageApplication,
    related.publicState, hp, hr]

theorem KnowledgeRelated.environmentView_eq
    (related : KnowledgeRelated runtime known left right) :
    MessageApplication.State.environmentView _ left =
      MessageApplication.State.environmentView _ right := by
  have hp : left.pool = right.pool := related.sealed.pool
  have hr : left.receipts = right.receipts := related.sealed.receipts
  simp only [MessageApplication.State.environmentView, messageApplication,
    related.publicState, hp, hr]

theorem KnowledgeRelated.register (related : KnowledgeRelated runtime known left right)
    (owner : Principal) (slot : Nat) (leftValue rightValue : Value)
    (hvalue : known (owner, slot) → leftValue = rightValue) :
    KnowledgeRelated runtime known
      { left with application.service :=
        (left.application.service.sealValue owner slot leftValue).state }
      { right with application.service :=
        (right.application.service.sealValue owner slot rightValue).state } :=
  ⟨related.sealed.register owner slot leftValue rightValue hvalue, related.publicState⟩

theorem KnowledgeRelated.submit (related : KnowledgeRelated runtime known left right)
    (owner : Principal) (payload : SealedProgram.Payload Principal Value)
    (hknown : SealedProgram.OpeningKnown known
      ⟨(owner, left.pool.nextSerial owner), payload⟩) :
    KnowledgeRelated runtime known
      { left with pool := (left.pool.submit owner payload).2 }
      { right with pool := (right.pool.submit owner payload).2 } :=
  ⟨related.sealed.submit owner payload hknown, related.publicState⟩

theorem KnowledgeRelated.replay (related : KnowledgeRelated runtime known left right)
    (owner : Principal) (id : MessageId Principal) :
    KnowledgeRelated runtime known
      { left with pool := (left.pool.replay owner id).state }
      { right with pool := (right.pool.replay owner id).state } :=
  ⟨related.sealed.replay owner id, related.publicState⟩

theorem KnowledgeRelated.deliver (related : KnowledgeRelated runtime known left right)
    (owner : Principal) (id : MessageId Principal) :
    KnowledgeRelated runtime known
      { left with pool := (left.pool.deliver owner id).state }
      { right with pool := (right.pool.deliver owner id).state } :=
  ⟨related.sealed.deliver owner id, related.publicState⟩

/-- Deadline decisions and public defaults depend on public state, not on
unopened values. The private service is retained on both sides. -/
theorem KnowledgeRelated.tick (related : KnowledgeRelated runtime known left right) :
    KnowledgeRelated runtime known
      { left with application := runtime.tick left.application }
      { right with application := runtime.tick right.application } := by
  have hvisible : (runtime.tick left.application).visible =
      (runtime.tick right.application).visible := by
    simp only [SealedResolution.tick, related.publicState]
  exact ⟨⟨related.sealed.occupied, related.sealed.values, related.sealed.pool,
    congrArg PublicState.events hvisible, related.sealed.receipts, related.sealed.openings⟩,
    hvisible⟩

/-- Authentication remains essential after discharging timed-out prerequisites:
validation supplies no oracle for unknown values belonging to another owner. -/
theorem KnowledgeRelated.validate_eq (related : KnowledgeRelated runtime known left right)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hknown : SealedProgram.OpeningKnown known message) :
    runtime.validateMessage? left.application message =
      runtime.validateMessage? right.application message := by
  have hkernel : SealedProgram.KnowledgeRelated
      (runtime.program.discharge right.application.visible.timeouts) known
      (runtime.eventState left) (runtime.eventState right) :=
    ⟨related.sealed.occupied, related.sealed.values, related.sealed.pool,
      related.sealed.events, related.sealed.receipts, related.sealed.openings⟩
  simp only [validateMessage?, related.publicState]
  split
  · rfl
  · simpa only [eventState, related.publicState] using hkernel.validate_eq message hknown

theorem KnowledgeRelated.includePending (related : KnowledgeRelated runtime known left right)
    (id : MessageId Principal) :
    KnowledgeRelated runtime known
      (runtime.messageApplication.includePending left id)
      (runtime.messageApplication.includePending right id) := by
  have hsafe := related.sealed.openings.includePending id
  have hp : left.pool = right.pool := related.sealed.pool
  unfold MessageApplication.includePending MessagePool.includeApplication
  cases hl : left.pool.includePending id with
  | mk message pool =>
      have hr : right.pool.includePending id = ⟨message, pool⟩ := by rw [← hp]; exact hl
      simp only [hr]
      have hsafePool : pool.Satisfies (SealedProgram.OpeningKnown known) := by
        simpa only [eventState, hl] using hsafe
      cases message with
      | none =>
          exact ⟨⟨related.sealed.occupied, related.sealed.values, rfl, related.sealed.events,
            related.sealed.receipts, hsafePool⟩, related.publicState⟩
      | some message =>
          have hlookup : left.pool.lookup id = some message := by
            have hm := congrArg (fun result => result.message) hl
            cases hlookup : left.pool.lookup id <;>
              simp_all [MessagePool.includePending, MessagePool.Result.invalid]
          have hknown := related.sealed.openings.1 message (List.mem_of_find?_eq_some hlookup)
          have hvalid := related.validate_eq message hknown
          simp only [messageApplication, handle]
          rw [hvalid]
          cases runtime.validateMessage? right.application message with
          | none =>
              exact ⟨⟨related.sealed.occupied, related.sealed.values, rfl, related.sealed.events,
                congrArg (fun receipts => receipts ++ [(id, false)]) related.sealed.receipts,
                hsafePool⟩, related.publicState⟩
          | some event =>
              have hvisible : runtime.refresh false
                  { left.application.visible with events := left.application.visible.events ++
                    [event] } = runtime.refresh false
                  { right.application.visible with events := right.application.visible.events ++
                    [event] } := by rw [related.publicState]
              exact ⟨⟨related.sealed.occupied, related.sealed.values, rfl,
                congrArg PublicState.events hvisible,
                congrArg (fun receipts => receipts ++ [(id, true)]) related.sealed.receipts,
                hsafePool⟩, hvisible⟩

/-- Honest private commands may differ at unknown handles. Their views and
all public commands still agree entry by entry. -/
def HistoryRelated (runtime : SealedResolution Principal Value)
    (known : CommitmentHandle Principal Nat → Prop) (who : Principal) :
    List runtime.messageApplication.PlayerEntry →
      List runtime.messageApplication.PlayerEntry → Prop :=
  List.Forall₂ fun left right => left.beforeView = right.beforeView ∧
    SealedProgram.CommandAgreement runtime.program known who left.command right.command

private theorem registration_decode_related (who : Principal)
    (left right : runtime.messageApplication.PlayerCommand)
    (related : SealedProgram.CommandAgreement runtime.program known who left right)
    (slot : Nat) :
    let encoding := runtime.program.registrationEncoding (Value := Value) slot
    (encoding.decode left).isSome = (encoding.decode right).isSome ∧
      (known (who, slot) → encoding.decode left = encoding.decode right) := by
  cases left with
  | privateCommand left =>
      cases right with
      | privateCommand right =>
          rcases left with ⟨leftSlot, leftValue⟩
          rcases right with ⟨rightSlot, rightValue⟩
          obtain ⟨hslot, hvalue⟩ := related
          dsimp only at hslot hvalue
          subst rightSlot
          by_cases hs : leftSlot = slot
          · subst slot
            simp only [SealedProgram.registrationEncoding, ↓reduceIte]
            exact ⟨rfl, fun h => congrArg some (hvalue h)⟩
          · simp only [SealedProgram.registrationEncoding, if_neg hs,
              Option.isSome_none, implies_true, and_self]
      | submit | replay | wait => cases related
  | submit payload =>
      cases right <;> cases related
      exact ⟨rfl, fun _ => rfl⟩
  | replay id =>
      cases right <;> cases related
      exact ⟨rfl, fun _ => rfl⟩
  | wait =>
      cases right <;> cases related
      exact ⟨rfl, fun _ => rfl⟩

/-- First-registration memory has equal occupancy, and equal values at known
handles. This uses local histories only, without a service-memory premise. -/
theorem HistoryRelated.cache
    {who : Principal} {left right : List runtime.messageApplication.PlayerEntry}
    (related : HistoryRelated runtime known who left right) (slot : Nat) :
    let encoding := runtime.program.registrationEncoding (Value := Value) slot
    (encoding.cachedValue runtime.messageApplication left).isSome =
        (encoding.cachedValue runtime.messageApplication right).isSome ∧
      (known (who, slot) → encoding.cachedValue runtime.messageApplication left =
        encoding.cachedValue runtime.messageApplication right) := by
  induction related with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | @cons left right lefts rights hentry htail ih =>
      have hdecode := registration_decode_related (runtime := runtime)
        who left.command right.command hentry.2 slot
      dsimp only at hdecode ⊢
      simp only [MessageApplication.ChoiceEncoding.cachedValue]
      cases hl : (runtime.program.registrationEncoding (Value := Value) slot).decode
          left.command <;>
        cases hr : (runtime.program.registrationEncoding (Value := Value) slot).decode
          right.command <;>
        simp only [hl, hr, Option.isSome_none, Option.isSome_some] at hdecode
      · exact ih
      · exact False.elim (Bool.false_ne_true hdecode.1)
      · exact False.elim (Bool.false_ne_true hdecode.1.symm)
      · exact ⟨rfl, hdecode.2⟩

/-- Knowing all of an owner's private values makes its complete local history
equal, not just its public-command projection. -/
theorem HistoryRelated.eq {who : Principal}
    {left right : List runtime.messageApplication.PlayerEntry}
    (related : HistoryRelated runtime known who left right)
    (hknown : ∀ slot, known (who, slot)) : left = right := by
  induction related with
  | nil => rfl
  | @cons left right lefts rights hentry htail ih =>
      have hcommand : left.command = right.command := by
        have hc := hentry.2
        cases hl : left.command <;> cases hr : right.command <;>
          simp only [hl, hr, SealedProgram.CommandAgreement] at hc
        · obtain ⟨hslot, hvalue⟩ := hc
          exact congrArg _ (ULift.ext _ _ (Prod.ext hslot (hvalue (hknown _))))
        all_goals first | exact hc | rfl
      have heq : left = right := by
        cases left
        cases right
        cases hentry.1
        cases hcommand
        rfl
      exact congrArg₂ List.cons heq ih

structure ExecutionRelated (runtime : SealedResolution Principal Value)
    (known : CommitmentHandle Principal Nat → Prop)
    (left right : runtime.messageApplication.PolicyExecution) : Prop where
  native : KnowledgeRelated runtime known left.native right.native
  histories : ∀ who, HistoryRelated runtime known who
    (left.principalHistory who) (right.principalHistory who)
  environmentHistory : left.environmentHistory = right.environmentHistory
  bindingLeft : BeforeTimeoutBinding runtime left.native.application
  bindingRight : BeforeTimeoutBinding runtime right.native.application

end Interaction.SealedResolution
