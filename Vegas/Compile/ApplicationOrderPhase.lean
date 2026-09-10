/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationPhaseCaches
import Interaction.MessagePoolFreshness

/-! # Exact ordered-admission phase laws

Source-ordered admission is transparent for a current-address submission and
its subsequent inclusion.  The theorem in this file runs the ordinary player
and environment policies through the shared message runner; it does not splice
or reproduce their transitions.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Inclusion through the ordered application is identical when the selected
pending envelope targets the current address. -/
theorem ordered_includePending_eq (image : ApplicationImage P L)
    (state : image.application.State) (id : MessageId P)
    (message : Message P (Payload P L)) (address : Nat)
    (hlookup : state.pool.lookup id = some message)
    (haddress : message.payload.address? = some address)
    (hactive : image.activeAddress? state.application.memory = some address) :
    image.orderedApplication.includePending state id =
      image.application.includePending state id := by
  apply image.application.includePending_withAdmission_of_allowed
    image.admitsMessage image.admitsEnvironment state id message hlookup
  change image.admitsMessage state.application.memory message = true
  simp [admitsMessage, haddress, admitsAddress, hactive]

/-- One supported current-address submission followed by a service inclusion
has exactly the unordered application's execution law. Freshness ensures that
the included identifier selects this submission even in a nonempty pool.

The environment-policy premise is stated only at executions supported by the
actual submission step. It permits arbitrary policy behavior elsewhere. -/
theorem ordered_submit_environment_phase_eq
    {Value : Type} (image : ApplicationImage P L)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (who : P) (execution : image.application.PolicyExecution)
    (draw : FinDist Value) (payload : Value → Payload P L) (address : Nat)
    (hplayer : players who (execution.principalHistory who)
      (MessageApplication.State.observe image.application execution.native who) =
        draw.map (fun value => .submit (payload value)))
    (henvironment : ∀ value, value ∈ draw.support →
      ∀ submitted, submitted ∈
        (image.application.playerStep who execution (.submit (payload value))).support →
      environment submitted.environmentHistory
          (MessageApplication.State.environmentView image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)))
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (haddress : ∀ value, value ∈ draw.support →
      (payload value).address? = some address)
    (hactive : image.activeAddress? execution.native.application.memory = some address) :
    image.orderedApplication.runPolicies players environment
        [.player who, .environment] execution =
      image.application.runPolicies players environment
        [.player who, .environment] execution := by
  change (image.application.withAdmission image.admitsMessage
      image.admitsEnvironment).runPolicies players environment
        [.player who, .environment] execution = _
  apply image.application.runPolicies_withAdmission_eq
  constructor
  · trivial
  · intro submitted hsubmitted
    simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hsubmitted
    obtain ⟨command, hcommand, hstep⟩ := hsubmitted
    rw [hplayer, FinDist.support_map] at hcommand
    obtain ⟨value, hvalue, rfl⟩ := hcommand
    constructor
    · intro environmentCommand hcommand
      rw [henvironment value hvalue submitted hstep] at hcommand
      simp only [FinDist.mem_support_pure] at hcommand
      subst environmentCommand
      intro message hlookup
      change image.admitsMessage submitted.native.application.memory message = true
      have hnative : submitted.native ∈
          ((image.application.playerStep who execution (.submit (payload value))).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨submitted, hstep, rfl⟩
      rw [image.application.playerStep_native] at hnative
      simp only [PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      have hlookupSubmitted : submitted.native.pool.lookup
          (who, execution.native.pool.nextSerial who) =
            some ⟨(who, execution.native.pool.nextSerial who), payload value⟩ := by
        rw [hnative]
        exact execution.native.pool.lookup_submit_fresh who (payload value) hfresh
      rw [hlookupSubmitted] at hlookup
      cases hlookup
      have hmemory := image.playerStep_memory who execution submitted
        (.submit (payload value)) hstep
      simp [admitsMessage, haddress value hvalue, admitsAddress, hmemory, hactive]
    · intro final _
      trivial

/-- A private command, a supported current-address submission, and its service
inclusion also have exactly the unordered law. This is the phase shape used by
opaque bindings: the first invocation may prepare private application state,
but cannot consume a message identifier or alter public completion memory. -/
theorem ordered_private_submit_environment_phase_eq
    {Value : Type} (image : ApplicationImage P L)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (who : P) (execution : image.application.PolicyExecution)
    (draw : FinDist Value) (privateCommand : Value → image.application.PrivateCommand)
    (payload : Value → Payload P L) (address : Nat)
    (hprefix : image.application.runPolicies players environment
      [.player who, .player who] execution =
        draw.bind fun value =>
          (image.application.playerStep who execution
            (.privateCommand (privateCommand value))).bind fun prepared =>
          image.application.playerStep who prepared (.submit (payload value)))
    (henvironment : ∀ value, value ∈ draw.support →
      ∀ prepared, prepared ∈ (image.application.playerStep who execution
        (.privateCommand (privateCommand value))).support →
      ∀ submitted, submitted ∈
        (image.application.playerStep who prepared (.submit (payload value))).support →
      environment submitted.environmentHistory
          (MessageApplication.State.environmentView image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)))
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (haddress : ∀ value, value ∈ draw.support →
      (payload value).address? = some address)
    (hactive : image.activeAddress? execution.native.application.memory = some address) :
    image.orderedApplication.runPolicies players environment
        [.player who, .player who, .environment] execution =
      image.application.runPolicies players environment
        [.player who, .player who, .environment] execution := by
  have hplayers : image.orderedApplication.runPolicies players environment
      [.player who, .player who] execution =
        image.application.runPolicies players environment
          [.player who, .player who] execution := by
    change (image.application.withAdmission image.admitsMessage
        image.admitsEnvironment).runPolicies players environment
          [.player who, .player who] execution = _
    apply image.application.runPolicies_withAdmission_eq
    constructor
    · trivial
    · intro prepared _
      constructor
      · trivial
      · intro submitted _
        trivial
  rw [show ([.player who, .player who, .environment] : List (@Invocation P)) =
      [.player who, .player who] ++ [.environment] by rfl,
    image.orderedApplication.runPolicies_append,
    image.application.runPolicies_append, hplayers, hprefix]
  apply FinDist.bind_congr
  intro submitted hsubmitted
  simp only [FinDist.support_bind, Set.mem_iUnion] at hsubmitted
  obtain ⟨value, hvalue, prepared, hfirstStep, hsecondStep⟩ := hsubmitted
  change (image.application.withAdmission image.admitsMessage
      image.admitsEnvironment).runPolicies players environment [.environment] submitted = _
  apply image.application.runPolicies_withAdmission_eq
  constructor
  · intro environmentCommand hcommand
    rw [henvironment value hvalue prepared hfirstStep submitted hsecondStep] at hcommand
    simp only [FinDist.mem_support_pure] at hcommand
    subst environmentCommand
    intro message hlookup
    change image.admitsMessage submitted.native.application.memory message = true
    have hpreparedNative : prepared.native ∈
        ((image.application.playerStep who execution
          (.privateCommand (privateCommand value))).map
            MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨prepared, hfirstStep, rfl⟩
    rw [image.application.playerStep_native] at hpreparedNative
    simp only [PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hpreparedNative
    have hpool : prepared.native.pool = execution.native.pool :=
      congrArg (·.pool) hpreparedNative
    have hsubmittedNative : submitted.native ∈
        ((image.application.playerStep who prepared (.submit (payload value))).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨submitted, hsecondStep, rfl⟩
    rw [image.application.playerStep_native] at hsubmittedNative
    simp only [PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hsubmittedNative
    have hlookupSubmitted : submitted.native.pool.lookup
        (who, execution.native.pool.nextSerial who) =
          some ⟨(who, execution.native.pool.nextSerial who), payload value⟩ := by
      rw [hsubmittedNative]
      simpa only [hpool] using
        prepared.native.pool.lookup_submit_fresh who (payload value)
          (by simpa only [hpool] using hfresh)
    rw [hlookupSubmitted] at hlookup
    cases hlookup
    have hfirstMemory := image.playerStep_memory who execution prepared
      (.privateCommand (privateCommand value)) hfirstStep
    have hsecondMemory := image.playerStep_memory who prepared submitted
      (.submit (payload value)) hsecondStep
    simp [admitsMessage, haddress value hvalue, admitsAddress,
      hsecondMemory, hfirstMemory, hactive]
  · intro final _
    trivial

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.ordered_includePending_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_includePending_eq

/-- info: 'Vegas.ApplicationImage.ordered_submit_environment_phase_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_submit_environment_phase_eq

/-- info: 'Vegas.ApplicationImage.ordered_private_submit_environment_phase_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_private_submit_environment_phase_eq
