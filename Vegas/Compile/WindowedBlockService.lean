/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationService
import Vegas.Compile.WindowedExpiry
import Vegas.Compile.WindowedProjection
import Interaction.MessageApplicationNoDelivery

/-! # Address-gated ordinary and expiry service

Each emitted instruction has a fixed polling block: two ordinary turns for
every roster member, ordinary inclusion or chance, clock advancement, then
one relay turn and reserved inclusion for every roster member. A member's
own history determines its slot. The environment uses its own history.

All service commands are gated by the block's expected instruction address.
Resolving an instruction therefore disables the rest of its block's service;
the next instruction gets its own ordinary opportunity before expiry.
Only reference player policies are gated. A unilateral raw replacement is
installed after this policy construction and retains every native command.

The definitions add no interpreter or runtime state. Roster coverage, history
alignment, handler readiness, and source-certified defaults are obligations
of the blockwise execution and strategic theorems.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Two ordinary polls per member accommodate private registration followed
by submission. Relay polls are separated from those ordinary opportunities. -/
def blockInvocations (roster : List P) : List (@Invocation P) :=
  roster.flatMap (fun who => [.player who, .player who]) ++
    [.environment, .environment] ++
      roster.flatMap (fun who => [.player who, .environment])

def blockSchedule (runtime : WindowedApplication P L) (roster : List P) :
    List (@Invocation P) :=
  runtime.image.instructions.flatMap (fun _ => blockInvocations roster)

/-- A coordinatewise reference-policy construction. The base policy receives
the real, unfiltered native history and observation. Relay slots never call
the base policy, even when a successor owned by this player is already active. -/
def blockPlayer (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy) : runtime.application.PlayerPolicy :=
  fun history view =>
    match runtime.image.instructions[history.length / 3]? with
    | none => FinDist.pure .wait
    | some instruction =>
        if runtime.image.activeAddress? view.application.1 = some instruction.address then
          if history.length % 3 < 2 then
            if instruction.submitter = some who then base history view
            else FinDist.pure .wait
          else FinDist.pure (runtime.relayCommand (runtime.dueExpiry? view.application) .wait)
        else FinDist.pure .wait

/-- The first environment slot serves the ordinary source action; the second
advances only the still-active block. Remaining slots reserve inclusion for
the corresponding roster member. Selection uses no private commitment state. -/
def blockEnvironment (runtime : WindowedApplication P L) (roster : List P) :
    runtime.application.EnvironmentPolicy := fun history view => FinDist.pure <|
  match runtime.image.instructions[history.length / (roster.length + 2)]? with
  | none => .wait
  | some instruction =>
      if runtime.image.activeAddress? view.application.1 = some instruction.address then
        match history.length % (roster.length + 2) with
        | 0 => runtime.liftEnvironmentCommand
            (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view))
        | 1 =>
            match view.application.2 with
            | none => .wait
            | some activation =>
                if activation.key = instruction.address then
                  .application (.advance
                    (activation.since + runtime.windowOf instruction.address + 1))
                else .wait
        | index + 2 =>
            match roster[index]? with
            | none => .wait
            | some who => runtime.application.latestSubmissionCommand who view
      else .wait

private theorem latestSubmissionCommand_ne_deliver (runtime : WindowedApplication P L)
    (actor observer : P) (id : MessageId P)
    (view : runtime.application.EnvironmentObservation) :
    runtime.application.latestSubmissionCommand actor view ≠ .deliver observer id := by
  rcases runtime.application.latestSubmissionCommand_cases actor view with hwait | ⟨key, hinclude⟩
  · rw [hwait]; simp
  · rw [hinclude]; simp

private theorem serviceCommand_ne_deliver (runtime : WindowedApplication P L)
    (instruction : ApplicationInstruction P L) (observer : P) (id : MessageId P)
    (view : runtime.application.EnvironmentObservation) :
    runtime.liftEnvironmentCommand
        (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view)) ≠
      .deliver observer id := by
  cases instruction with
  | sample code => simp [ApplicationImage.serviceCommand, liftEnvironmentCommand]
  | bind code | publicChoice code | conditional code =>
      simp only [ApplicationImage.serviceCommand]
      rcases runtime.image.application.latestSubmissionCommand_cases _ _ with
        hwait | ⟨key, hinclude⟩
      · rw [hwait]; simp [liftEnvironmentCommand]
      · rw [hinclude]; simp [liftEnvironmentCommand]

/-- This service includes messages but never delivers pending packets to a
local inbox. Wider delivery policies need their own information-flow proof. -/
theorem blockEnvironment_noDelivery (runtime : WindowedApplication P L) (roster : List P) :
    MessageApplication.EnvironmentPolicy.NoDelivery runtime.application
      (runtime.blockEnvironment roster) := by
  intro history view observer id
  simp only [blockEnvironment, FinDist.mem_support_pure]
  split
  · simp
  · split
    · split
      · exact Ne.symm (runtime.serviceCommand_ne_deliver _ observer id view)
      · split
        · simp
        · split <;> simp
      · split
        · simp
        · exact Ne.symm (runtime.latestSubmissionCommand_ne_deliver _ observer id view)
    · simp

theorem blockPlayer_inactive (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length / 3]? = some instruction)
    (hinactive : runtime.image.activeAddress? view.application.1 ≠ some instruction.address) :
    runtime.blockPlayer who base history view = FinDist.pure .wait := by
  simp only [blockPlayer, hindex, hinactive, ↓reduceIte]

theorem blockPlayer_normal (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length / 3]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % 3 < 2) (howner : instruction.submitter = some who) :
    runtime.blockPlayer who base history view = base history view := by
  simp only [blockPlayer, hindex, hactive, hslot, howner, ↓reduceIte]

theorem blockPlayer_relay (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (instruction : ApplicationInstruction P L) (payload : ApplicationImage.Payload P L)
    (hindex : runtime.image.instructions[history.length / 3]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % 3 = 2)
    (hdue : runtime.dueExpiry? view.application = some payload) :
    runtime.blockPlayer who base history view = FinDist.pure (.submit payload) := by
  simp only [blockPlayer, hindex, hactive, hslot, Nat.lt_irrefl, ↓reduceIte,
    hdue, relayCommand]

theorem blockEnvironment_inactive (runtime : WindowedApplication P L) (roster : List P)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation) (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length / (roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? view.application.1 ≠ some instruction.address) :
    runtime.blockEnvironment roster history view = FinDist.pure .wait := by
  simp only [blockEnvironment, hindex, hinactive, ↓reduceIte]

theorem blockEnvironment_normal (runtime : WindowedApplication P L) (roster : List P)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation) (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length / (roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (roster.length + 2) = 0) :
    runtime.blockEnvironment roster history view = FinDist.pure
      (runtime.liftEnvironmentCommand
        (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view))) := by
  simp only [blockEnvironment, hindex, hactive, hslot, ↓reduceIte]

theorem blockEnvironment_advance (runtime : WindowedApplication P L) (roster : List P)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation) (instruction : ApplicationInstruction P L)
    (activation : Activation Nat)
    (hindex : runtime.image.instructions[history.length / (roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (roster.length + 2) = 1)
    (hactivation : view.application.2 = some activation)
    (hkey : activation.key = instruction.address) :
    runtime.blockEnvironment roster history view = FinDist.pure
      (.application (.advance (activation.since + runtime.windowOf instruction.address + 1))) := by
  simp only [blockEnvironment, hindex, hactive, hslot, hactivation, hkey, ↓reduceIte]

theorem blockEnvironment_relay (runtime : WindowedApplication P L) (roster : List P)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation) (instruction : ApplicationInstruction P L)
    (index : Nat) (who : P)
    (hindex : runtime.image.instructions[history.length / (roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? view.application.1 = some instruction.address)
    (hslot : history.length % (roster.length + 2) = index + 2)
    (hwho : roster[index]? = some who) :
    runtime.blockEnvironment roster history view =
      FinDist.pure (runtime.application.latestSubmissionCommand who view) := by
  simp only [blockEnvironment, hindex, hactive, hslot, hwho, ↓reduceIte]

omit [DecidableEq P] in
/-- Slot counts depend only on the fixed roster, not on successful calls. -/
theorem blockInvocations_environment_count (roster : List P) :
    (blockInvocations roster).countP Invocation.isEnvironment = roster.length + 2 := by
  have hnormal : (roster.flatMap (fun who =>
      [Invocation.player who, Invocation.player who])).countP Invocation.isEnvironment = 0 := by
    induction roster with
    | nil => rfl
    | cons who rest ih => simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
        List.countP_nil, Invocation.isEnvironment, Bool.false_eq_true, ↓reduceIte, ih, Nat.zero_add]
  have hrelay : (roster.flatMap (fun who =>
      [Invocation.player who, Invocation.environment])).countP Invocation.isEnvironment =
      roster.length := by
    clear hnormal
    induction roster with
    | nil => rfl
    | cons who rest ih => simp [List.flatMap_cons, Invocation.isEnvironment, ih]
  simp only [blockInvocations, List.countP_append, hnormal, hrelay, List.countP_cons,
    List.countP_nil, Invocation.isEnvironment, ↓reduceIte]
  omega

end Vegas.WindowedApplication
