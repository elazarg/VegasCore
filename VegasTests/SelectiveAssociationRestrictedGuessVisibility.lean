/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrefix
import VegasTests.SelectiveAssociationRestrictedOpening
import Vegas.Pending.ReactiveDisclosureStability

/-! # Public guessing information between the two binding visits

After Alice's binding settles, its accepted association is immutable. A
prescribed guesser correction publishes no certificate, so inclusion of that
fresh envelope cannot change the public guess used by the other guesser.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private def trueCertificate (chosen : Handle nativeGraph) (message : Message Player app.Payload) :
    Bool :=
  (show WitnessedPacket nativeGraph from message.payload).evidence.any fun fact =>
    decide (fact.handle = chosen) && (fact.raw.as? .bool).getD false

theorem publicGuess_congr (first second : app.Execution) (left right : Player)
    (accepted : first.application.accepted aliceBindingRef.field =
      second.application.accepted aliceBindingRef.field)
    (ledger : first.network.ledger = second.network.ledger) :
    publicGuess (first.observe app left) = publicGuess (second.observe app right) := by
  change (match first.application.accepted aliceBindingRef.field with
    | none => false
    | some chosen => first.network.ledger.any (trueCertificate chosen)) =
    (match second.application.accepted aliceBindingRef.field with
    | none => false
    | some chosen => second.network.ledger.any (trueCertificate chosen))
  rw [accepted, ledger]

theorem publicGuess_append_uncertified (first second : app.Execution) (left right : Player)
    (accepted : first.application.accepted aliceBindingRef.field =
      second.application.accepted aliceBindingRef.field)
    (message : Message Player app.Payload)
    (ledger : first.network.ledger = second.network.ledger ++ [message])
    (absent : (show WitnessedPacket nativeGraph from message.payload).evidence = none) :
    publicGuess (first.observe app left) = publicGuess (second.observe app right) := by
  change (match first.application.accepted aliceBindingRef.field with
    | none => false
    | some chosen => first.network.ledger.any (trueCertificate chosen)) =
    (match second.application.accepted aliceBindingRef.field with
    | none => false
    | some chosen => second.network.ledger.any (trueCertificate chosen))
  rw [accepted, ledger]
  cases second.application.accepted aliceBindingRef.field with
  | none => rfl
  | some chosen =>
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      have missing : trueCertificate chosen message = false := by
        simp only [trueCertificate, absent, Option.any_none]
      rw [missing, Bool.or_false]

theorem publicGuess_respond (execution : app.Execution) (actor observer : Player)
    (action : app.Action) :
    publicGuess ((execution.respond app actor action).observe app observer) =
      publicGuess (execution.observe app observer) := by
  apply publicGuess_congr
  · exact congrFun (congrArg PublicView.accepted
      (nativeRuntime.reactive_respond_application leaks execution actor action).2)
        aliceBindingRef.field
  · rcases action with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some transmission =>
        cases transmission with
        | submit => rfl
        | replay id =>
            dsimp only [ReactiveApplication.Execution.respond]
            unfold MessageNetwork.replay
            split <;> rfl

theorem publicGuess_activate (execution : app.Execution) (actor observer : Player) :
    publicGuess ((activate execution actor).observe app observer) =
      publicGuess (execution.observe app observer) := rfl

theorem publicGuess_environment (execution : app.Execution)
    (command : EnvironmentCommand nativeGraph)
    (observer : Player) :
    publicGuess ((Prefix.environmentResult execution (.application command)).observe app observer) =
      publicGuess (execution.observe app observer) := by
  have reached : Prefix.environmentResult execution (.application command) ∈
      (execution.environmentStep app (.application command)).support := by
    rw [Prefix.environmentResult_law]
    exact FinDist.mem_support_pure.mpr rfl
  obtain ⟨next, nextMem, nextEq⟩ := FinDist.support_map .. ▸ reached
  obtain ⟨state, stateMem, stateEq⟩ := FinDist.support_map .. ▸ nextMem
  subst next
  rw [← nextEq]
  apply publicGuess_congr
  · exact congrFun (environmentStep_tables nativeRuntime execution.application state command
      stateMem).1 aliceBindingRef.field
  · rfl

theorem publicGuess_include_uncertified (execution : app.Execution)
    (id : MessageId Player) (message : Message Player (WitnessedPacket nativeGraph))
    (found : execution.network.lookup id = some message)
    (absent : message.payload.evidence = none)
    (present : (execution.application.config.store aliceBindingRef.field).isSome = true)
    (observer : Player) :
    publicGuess ((Prefix.environmentResult execution (.include id)).observe app observer) =
      publicGuess (execution.observe app observer) := by
  have exactState := Prefix.environmentResult_eq execution (.include id)
    { execution.includePending app id with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include id⟩] } (by
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure])
  rw [exactState]
  refine publicGuess_append_uncertified _ execution observer observer ?_ message ?_ absent
  · change (execution.includePending app id).application.accepted aliceBindingRef.field = _
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change ((handle nativeRuntime execution.application ⟨message.id, message.payload.call⟩).getD
      execution.application).accepted aliceBindingRef.field = _
    cases handled : handle nativeRuntime execution.application ⟨message.id, message.payload.call⟩
      with
    | none => rfl
    | some state =>
        exact handle_accepted_of_present nativeRuntime execution.application state
          aliceBindingRef.field present _ handled
  · change (execution.includePending app id).network.ledger = _
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]

theorem corrective_inclusion_keeps_guess (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some carol)
    (granted : control.execution.application.serviceGrant = some carolBinding) (bit : Bool)
    (observer : Player) :
    publicGuess ((Prefix.includeLatest
      (control.execution.respond app carol
        (correctiveBinding carol carolBinding bit (control.execution.observe app carol)))
          carolBinding carol).observe app observer) =
      publicGuess (control.execution.observe app observer) := by
  obtain ⟨slot, selected, _⟩ := binding_fresh control trace carol active granted
  have serials := (history_invariants control trace).2.2
  have complete := earlier_completed carolBinding aliceBinding (by decide) control trace active
    granted
  have present := (control.execution.application.config.output_available aliceBinding).mpr complete
  simp only [correctiveBinding, selected]
  let submitted := control.execution.respond app carol (bindingResponse carol carolBinding slot bit)
  have choose := binding_selected control.execution carol slot bit serials
  change nativeRuntime.reactiveLatest leaks carolBinding carol
    (submitted.observeEnvironment app) =
      .include (carol, control.execution.network.nextSerial carol) at choose
  change publicGuess ((Prefix.includeLatest submitted carolBinding carol).observe app observer) = _
  unfold Prefix.includeLatest
  rw [choose]
  have lookup : submitted.network.lookup (carol, control.execution.network.nextSerial carol) =
      some ⟨(carol, control.execution.network.nextSerial carol),
        ⟨.commitment carolBinding (carol, .prepared slot.val), none⟩⟩ :=
    serials.lookup_submit carol _
  rw [publicGuess_include_uncertified submitted _ _ lookup rfl (by
    rw [(nativeRuntime.reactive_respond_application leaks control.execution carol
      (bindingResponse carol carolBinding slot bit)).1]
    exact present) observer]
  exact publicGuess_respond control.execution carol observer _

end VegasTests.SelectiveAssociation.Restricted
