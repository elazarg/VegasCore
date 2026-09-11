/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedApplication
import Vegas.Compile.ApplicationBindingTimeouts
import Vegas.Compile.ApplicationImageBindings
import Interaction.MessageApplicationPolicies

/-! # Permissionless expiry relays for activation-relative applications

The public activation observation determines whether the current emitted
instruction has an expiry entry point and is strictly overdue. Any principal
may relay that raw request. Before the boundary, the relay delegates to its
supplied policy on the actual, unmodified windowed history and view.
-/

noncomputable section

namespace Vegas

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationInstruction

/-- The permissionless expiry request supplied by an emitted instruction.
Optional binding and public-choice fallbacks remain disabled when their code
contains no timeout. Conditional publication always has an expiry request. -/
def expiryPayload? : ApplicationInstruction P L →
    Option (ApplicationImage.Payload P L)
  | .sample _ => none
  | .bind code => if code.timeout.isSome then some (.expireBinding code.node) else none
  | .publicChoice code =>
      if code.timeout.isSome then some (.expireChoice code.endpoint.publicationNode) else none
  | .conditional code => some (.conditional code.endpoint.publicationNode .expire)

omit [DecidableEq P] in
/-- Every selected expiry request targets its instruction's dispatch address. -/
theorem expiryPayload?_address (instruction : ApplicationInstruction P L)
    (payload : ApplicationImage.Payload P L)
    (hpayload : instruction.expiryPayload? = some payload) :
    payload.address? = some instruction.address := by
  cases instruction with
  | sample code => simp [expiryPayload?] at hpayload
  | bind code =>
      simp only [expiryPayload?] at hpayload
      split at hpayload <;> try contradiction
      cases hpayload
      rfl
  | publicChoice code =>
      simp only [expiryPayload?] at hpayload
      split at hpayload <;> try contradiction
      cases hpayload
      rfl
  | conditional code =>
      cases hpayload
      rfl

end ApplicationInstruction

namespace WindowedApplication

/-- Select the current instruction's permissionless expiry request exactly
when activation metadata agrees with public completion state and its strict
relative deadline has passed. -/
def dueExpiry? (runtime : WindowedApplication P L)
    (view : ApplicationImage.Memory P L × Option (Activation Nat)) :
    Option (ApplicationImage.Payload P L) := do
  let activation ← view.2
  if runtime.image.activeAddress? view.1 = some activation.key ∧
      activation.since + runtime.windowOf activation.key < view.1.clock then
    let instruction ← runtime.image.lookup activation.key
    instruction.expiryPayload?
  else none

omit [DecidableEq P] in
/-- A selected request exposes only public operational facts: the matching
active instruction, strict overdue clock, and its installed expiry entry. -/
theorem dueExpiry?_some (runtime : WindowedApplication P L)
    (view : ApplicationImage.Memory P L × Option (Activation Nat))
    (payload : ApplicationImage.Payload P L)
    (hresult : runtime.dueExpiry? view = some payload) :
    ∃ activation instruction,
      view.2 = some activation ∧
      runtime.image.activeAddress? view.1 = some activation.key ∧
      activation.since + runtime.windowOf activation.key < view.1.clock ∧
      runtime.image.lookup activation.key = some instruction ∧
      instruction.expiryPayload? = some payload := by
  unfold dueExpiry? at hresult
  cases hactive : view.2 with
  | none => simp [hactive] at hresult
  | some activation =>
      simp only [hactive, Option.bind_eq_bind, Option.bind_some] at hresult
      split at hresult
      · rename_i hdue
        cases hlookup : runtime.image.lookup activation.key with
        | none => simp [hlookup] at hresult
        | some instruction =>
            simp only [hlookup, Option.bind_some] at hresult
            exact ⟨activation, instruction, rfl, hdue.1, hdue.2, hlookup, hresult⟩
      · contradiction

omit [DecidableEq P] in
/-- At or before the strict boundary no expiry request is selected, even if
the supplied activation metadata does not match the current instruction. -/
theorem dueExpiry?_eq_none_before_window (runtime : WindowedApplication P L)
    (memory : ApplicationImage.Memory P L) (activation : Activation Nat)
    (hclock : memory.clock ≤ activation.since + runtime.windowOf activation.key) :
    runtime.dueExpiry? (memory, some activation) = none := by
  unfold dueExpiry?
  simp only [Option.bind_eq_bind, Option.bind_some]
  split
  · rename_i hdue
    exact False.elim (Nat.not_lt_of_ge hclock hdue.2)
  · rfl

/-- Replace a wait command by the publicly due expiry submission. Every other
command is preserved, including ordinary owner actions after the deadline. -/
def relayCommand (runtime : WindowedApplication P L)
    (due : Option (ApplicationImage.Payload P L)) :
    runtime.application.PlayerCommand → runtime.application.PlayerCommand
  | .wait =>
      match due with
      | none => .wait
      | some payload => .submit payload
  | .privateCommand command => .privateCommand command
  | .submit payload => .submit payload
  | .replay id => .replay id

/-- Add permissionless expiry relaying without changing the policy's actual
view or history. A due expiry replaces only a sampled wait; all non-wait
commands produced by the supplied policy remain unchanged. -/
def relayWhenWaiting (runtime : WindowedApplication P L)
    (base : runtime.application.PlayerPolicy) : runtime.application.PlayerPolicy :=
  fun history view =>
    (base history view).map (runtime.relayCommand (runtime.dueExpiry? view.application))

/-- Throughout the active window, the relay is exactly its supplied policy on
the original windowed history and observation. -/
theorem relayWhenWaiting_eq_base_before_window (runtime : WindowedApplication P L)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (memory : ApplicationImage.Memory P L) (activation : Activation Nat)
    (hview : view.application = (memory, some activation))
    (hclock : memory.clock ≤ activation.since + runtime.windowOf activation.key) :
    runtime.relayWhenWaiting base history view = base history view := by
  unfold relayWhenWaiting
  rw [hview, runtime.dueExpiry?_eq_none_before_window memory activation hclock]
  have hid : runtime.relayCommand none = id := by
    funext command
    cases command <;> rfl
  rw [hid, FinDist.map_id]

/-- If the base policy cannot wait on this observation, expiry relaying leaves
its whole command distribution unchanged, even after the deadline. -/
theorem relayWhenWaiting_eq_of_wait_not_supported (runtime : WindowedApplication P L)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (hwait : (.wait : runtime.application.PlayerCommand) ∉
      (base history view).support) :
    runtime.relayWhenWaiting base history view = base history view := by
  unfold relayWhenWaiting
  calc
    (base history view).map
        (runtime.relayCommand (runtime.dueExpiry? view.application)) =
        (base history view).map id := by
      apply FinDist.map_congr_of_eq_on_support
      intro command hcommand
      cases command with
      | privateCommand command => rfl
      | submit payload => rfl
      | replay id => rfl
      | wait => exact False.elim (hwait hcommand)
    _ = base history view := FinDist.map_id _

/-- A deterministic base wait becomes exactly the publicly selected raw expiry
submission. The relay does not manufacture an inclusion or owner action. -/
theorem relayWhenWaiting_pure_wait (runtime : WindowedApplication P L)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (payload : ApplicationImage.Payload P L)
    (hbase : base history view = FinDist.pure .wait)
    (hdue : runtime.dueExpiry? view.application = some payload)
    : runtime.relayWhenWaiting base history view =
      FinDist.pure (.submit payload) := by
  simp only [relayWhenWaiting, hbase, hdue, FinDist.map_pure, relayCommand]

/-- Complete support classification for relaying. A result is either an
unchanged non-wait base command, an unchanged wait when nothing is due, or the
raw due submission replacing a supported base wait. -/
theorem relayWhenWaiting_supported (runtime : WindowedApplication P L)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (command : runtime.application.PlayerCommand)
    (hcommand : command ∈ (runtime.relayWhenWaiting base history view).support) :
    (command ∈ (base history view).support ∧ command ≠ .wait) ∨
    (command = .wait ∧ .wait ∈ (base history view).support ∧
      runtime.dueExpiry? view.application = none) ∨
    ∃ payload, runtime.dueExpiry? view.application = some payload ∧
      .wait ∈ (base history view).support ∧ command = .submit payload := by
  unfold relayWhenWaiting at hcommand
  rw [FinDist.support_map] at hcommand
  obtain ⟨baseCommand, hbaseCommand, rfl⟩ := hcommand
  cases baseCommand with
  | privateCommand prepared => exact Or.inl ⟨hbaseCommand, by simp [relayCommand]⟩
  | submit original => exact Or.inl ⟨hbaseCommand, by simp [relayCommand]⟩
  | replay id => exact Or.inl ⟨hbaseCommand, by simp [relayCommand]⟩
  | wait =>
      cases hdue : runtime.dueExpiry? view.application with
      | none => exact Or.inr (Or.inl ⟨rfl, hbaseCommand, rfl⟩)
      | some payload => exact Or.inr (Or.inr ⟨payload, rfl, hbaseCommand, rfl⟩)

end WindowedApplication

end Vegas

/-- info: 'Vegas.ApplicationInstruction.expiryPayload?_address' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationInstruction.expiryPayload?_address

/-- info: 'Vegas.WindowedApplication.dueExpiry?_some' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.dueExpiry?_some

/-- info: 'Vegas.WindowedApplication.relayWhenWaiting_supported' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.relayWhenWaiting_supported
