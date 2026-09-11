/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockService

/-! # Delivery-enabled fixed block service

This service uses the existing message-application runner and native state. A
block gives every roster member two ordinary polls, reserves one delivery slot
for each fixed recipient, gives every roster member one unrestricted reaction
invocation, performs normal service and clock advancement, and finally gives
each roster member an expiry relay and inclusion pair.

Reference players wait during the reaction slot. A raw policy installed after
the reference profile is constructed remains unrestricted and receives the
unfiltered native history and observation on that invocation.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- One delivery-enabled service block for an emitted instruction. -/
def deliveryBlockInvocations (roster recipients : List P) : List (@Invocation P) :=
  roster.flatMap (fun who => [.player who, .player who]) ++
    recipients.map (fun _ => Invocation.environment) ++
      roster.map Invocation.player ++
        [.environment, .environment] ++
          roster.flatMap (fun who => [.player who, .environment])

/-- The delivery-enabled reference policy. The base policy sees the real
history only in the two ordinary slots; the reaction slot waits and the final
slot relays a due expiry. -/
def deliveryBlockPlayer (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy) : runtime.application.PlayerPolicy :=
  fun history view =>
    match runtime.image.instructions[history.length / 4]? with
    | none => FinDist.pure .wait
    | some instruction =>
        if runtime.image.activeAddress? view.application.1 = some instruction.address then
          match history.length % 4 with
          | 0 | 1 =>
              if instruction.submitter = some who then base history view
              else FinDist.pure .wait
          | 2 => FinDist.pure .wait
          | _ => FinDist.pure
              (runtime.relayCommand (runtime.dueExpiry? view.application) .wait)
        else FinDist.pure .wait

/-- Convert only the envelope identifier selected by ordinary head service
into a delivery command. No payload or private application state is read. -/
private def deliveryCommand (runtime : WindowedApplication P L)
    (recipient : P) (instruction : ApplicationInstruction P L)
    (view : runtime.application.EnvironmentObservation) :
    runtime.application.EnvironmentPolicyCommand :=
  match runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view)) with
  | .include id => .deliver recipient id
  | _ => .wait

/-- Delivery-enabled environment service. Its history alone selects both the
current instruction and the fixed coordinate within that instruction's block. -/
def deliveryBlockEnvironment (runtime : WindowedApplication P L)
    (roster recipients : List P) : runtime.application.EnvironmentPolicy :=
  fun history view => FinDist.pure <|
    let width := recipients.length + roster.length + 2
    match runtime.image.instructions[history.length / width]? with
    | none => .wait
    | some instruction =>
        if runtime.image.activeAddress? view.application.1 = some instruction.address then
          let slot := history.length % width
          if slot < recipients.length then
            match recipients[slot]? with
            | none => .wait
            | some recipient => runtime.deliveryCommand recipient instruction view
          else if slot = recipients.length then
            runtime.liftEnvironmentCommand
              (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view))
          else if slot = recipients.length + 1 then
            match view.application.2 with
            | none => .wait
            | some activation =>
                if activation.key = instruction.address then
                  .application (.advance
                    (activation.since + runtime.windowOf instruction.address + 1))
                else .wait
          else
            match roster[slot - (recipients.length + 2)]? with
            | none => .wait
            | some who => runtime.application.latestSubmissionCommand who view
        else .wait

theorem deliveryBlockPlayer_ordinary (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length / 4]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % 4 = 0 ∨ history.length % 4 = 1)
    (howner : instruction.submitter = some who) :
    runtime.deliveryBlockPlayer who base history view = base history view := by
  rcases hslot with hslot | hslot <;>
    simp [deliveryBlockPlayer, hindex, hactive, hslot, howner]

theorem deliveryBlockPlayer_reaction (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (hslot : history.length % 4 = 2) :
    runtime.deliveryBlockPlayer who base history view = FinDist.pure .wait := by
  simp only [deliveryBlockPlayer]
  split
  · rfl
  · split
    · simp only [hslot]
    · rfl

theorem deliveryBlockPlayer_relay (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (instruction : ApplicationInstruction P L) (payload : ApplicationImage.Payload P L)
    (hindex : runtime.image.instructions[history.length / 4]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % 4 = 3)
    (hdue : runtime.dueExpiry? view.application = some payload) :
    runtime.deliveryBlockPlayer who base history view = FinDist.pure (.submit payload) := by
  simp [deliveryBlockPlayer, hindex, hactive, hslot, hdue, relayCommand]

theorem deliveryBlockEnvironment_delivery (runtime : WindowedApplication P L)
    (roster recipients : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L) (slot : Nat) (recipient : P)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (recipients.length + roster.length + 2) = slot)
    (hslotRange : slot < recipients.length) (hrecipient : recipients[slot]? = some recipient) :
    runtime.deliveryBlockEnvironment roster recipients history view =
      FinDist.pure (runtime.deliveryCommand recipient instruction view) := by
  simp only [deliveryBlockEnvironment, hindex, hactive, if_pos, hslot,
    hslotRange, hrecipient]

/-- A recipient delivery coordinate can only wait or copy the identifier
selected by ordinary service into a delivery command. -/
theorem deliveryBlockEnvironment_delivery_only (runtime : WindowedApplication P L)
    (roster recipients : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L) (slot : Nat) (recipient : P)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (recipients.length + roster.length + 2) = slot)
    (hslotRange : slot < recipients.length) (hrecipient : recipients[slot]? = some recipient)
    (hcommand : command ∈ (runtime.deliveryBlockEnvironment roster recipients
      history view).support) :
    command = .wait ∨ ∃ id, command = .deliver recipient id := by
  rw [runtime.deliveryBlockEnvironment_delivery roster recipients history view instruction
    slot recipient hindex hactive hslot hslotRange hrecipient,
    FinDist.mem_support_pure] at hcommand
  subst command
  unfold deliveryCommand
  split <;> simp

/-- At a recipient coordinate, delivery service is delivery-only even when
the observed active address has changed, in which case it waits. -/
theorem deliveryBlockEnvironment_recipient_only (runtime : WindowedApplication P L)
    (roster recipients : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L) (slot : Nat) (recipient : P)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hslot : history.length % (recipients.length + roster.length + 2) = slot)
    (hslotRange : slot < recipients.length) (hrecipient : recipients[slot]? = some recipient)
    (hcommand : command ∈ (runtime.deliveryBlockEnvironment roster recipients
      history view).support) :
    command = .wait ∨ ∃ id, command = .deliver recipient id := by
  by_cases hactive : runtime.image.activeAddress? view.application.1 = some instruction.address
  · exact runtime.deliveryBlockEnvironment_delivery_only roster recipients history view
      instruction slot recipient command hindex hactive hslot hslotRange hrecipient hcommand
  · simp only [deliveryBlockEnvironment, hindex, hactive, if_false,
      FinDist.mem_support_pure] at hcommand
    exact Or.inl hcommand

/-- A delivery slot copies only the identifier of the inclusion selected by
ordinary head service. -/
theorem deliveryBlockEnvironment_delivery_include (runtime : WindowedApplication P L)
    (roster recipients : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L) (slot : Nat) (recipient : P)
    (id : MessageId P)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (recipients.length + roster.length + 2) = slot)
    (hslotRange : slot < recipients.length) (hrecipient : recipients[slot]? = some recipient)
    (hinclude : runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view)) =
        .include id) :
    runtime.deliveryBlockEnvironment roster recipients history view =
      FinDist.pure (.deliver recipient id) := by
  rw [runtime.deliveryBlockEnvironment_delivery roster recipients history view instruction
    slot recipient hindex hactive hslot hslotRange hrecipient]
  simp [deliveryCommand, hinclude]

theorem deliveryBlockEnvironment_normal (runtime : WindowedApplication P L)
    (roster recipients : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (recipients.length + roster.length + 2) = recipients.length) :
    runtime.deliveryBlockEnvironment roster recipients history view = FinDist.pure
      (runtime.liftEnvironmentCommand
        (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view))) := by
  simp [deliveryBlockEnvironment, hindex, hactive, hslot]

theorem deliveryBlockEnvironment_advance (runtime : WindowedApplication P L)
    (roster recipients : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (recipients.length + roster.length + 2) =
      recipients.length + 1)
    (hactivation : view.application.2 = some activation)
    (hkey : activation.key = instruction.address) :
    runtime.deliveryBlockEnvironment roster recipients history view = FinDist.pure
      (.application (.advance
        (activation.since + runtime.windowOf instruction.address + 1))) := by
  simp [deliveryBlockEnvironment, hindex, hactive, hslot, hactivation, hkey]

theorem deliveryBlockEnvironment_relay (runtime : WindowedApplication P L)
    (roster recipients : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L) (index : Nat) (who : P)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (recipients.length + roster.length + 2) =
      recipients.length + 2 + index)
    (hwho : roster[index]? = some who) :
    runtime.deliveryBlockEnvironment roster recipients history view =
      FinDist.pure (runtime.application.latestSubmissionCommand who view) := by
  have hnotDelivery : ¬ recipients.length + 2 + index < recipients.length := by omega
  have hnotNormal : recipients.length + 2 + index ≠ recipients.length := by omega
  have hnotClock : recipients.length + 2 + index ≠ recipients.length + 1 := by omega
  simp only [deliveryBlockEnvironment, hindex, hactive, if_pos, hslot, hnotDelivery,
    hnotNormal, hnotClock, if_false, Nat.add_sub_cancel_left, hwho]

omit [DecidableEq P] in
/-- Environment history advances by the delivery slots, two fixed service
slots, and the roster-indexed inclusion slots. -/
theorem deliveryBlockInvocations_environment_count (roster recipients : List P) :
    (deliveryBlockInvocations roster recipients).countP Invocation.isEnvironment =
      recipients.length + roster.length + 2 := by
  have hrelays : (roster.flatMap (fun who =>
      [Invocation.player who, Invocation.environment])).countP Invocation.isEnvironment =
      roster.length := by
    induction roster with
    | nil => rfl
    | cons who rest ih =>
        simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
          List.countP_nil, List.length_cons, Invocation.isEnvironment, Bool.false_eq_true,
          ↓reduceIte, ih]
        omega
  have hpolls : (roster.flatMap (fun who =>
      [Invocation.player who, Invocation.player who])).countP Invocation.isEnvironment = 0 := by
    clear hrelays
    induction roster with
    | nil => rfl
    | cons who rest ih =>
        simp [List.flatMap_cons, Invocation.isEnvironment, ih]
  have hdeliveries : (recipients.map (fun _ =>
      (Invocation.environment : @Invocation P))).countP Invocation.isEnvironment =
      recipients.length := by
    induction recipients with
    | nil => rfl
    | cons recipient rest ih =>
        simp only [List.map_cons, List.countP_cons, Invocation.isEnvironment, ↓reduceIte, ih,
          List.length_cons]
  have hreactions : (roster.map Invocation.player).countP Invocation.isEnvironment = 0 := by
    clear hrelays hpolls
    induction roster with
    | nil => rfl
    | cons who rest ih => simp [Invocation.isEnvironment, ih]
  simp only [deliveryBlockInvocations, List.countP_append, hpolls, hdeliveries, hreactions,
    hrelays, List.countP_cons, List.countP_nil, Invocation.isEnvironment, ↓reduceIte]
  omega

omit [DecidableEq P] in
theorem deliveryBlockInvocations_length (roster recipients : List P) :
    (deliveryBlockInvocations roster recipients).length =
      5 * roster.length + recipients.length + 2 := by
  simp [deliveryBlockInvocations, List.length_flatMap]
  omega

end Vegas.WindowedApplication
