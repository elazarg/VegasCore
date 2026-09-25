/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedCarolSymmetry

/-! # Reconstructing Alice's accepted handle from a concrete prefix

There is one inclusion before Carol binds. The prelude and submission leave
the accepted table empty, and subsequent clock, expiry and grant operations
leave it unchanged. An accepted handle at Carol's input must therefore be the
handle in that actual successful inclusion.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem respond_accepted (execution : app.Execution) (who : Player) (action : app.Action) :
    (execution.respond app who action).application.accepted = execution.application.accepted :=
  congrArg PublicView.accepted
    (nativeRuntime.reactive_respond_application leaks execution who action).2

theorem alice_before_inclusion_empty (responses : Prefix.CarolResponses) :
    (((Prefix.aliceInput responses.alicePrelude responses.bobPrelude).respond app alice
      responses.aliceBinding).application.accepted aliceBindingRef.field) = none := by
  rw [respond_accepted]
  unfold Prefix.aliceInput
  change (Prefix.environmentResult _ (.application (.grant aliceBinding))).application.accepted
    aliceBindingRef.field = none
  rw [environment_accepted, respond_accepted]
  unfold Prefix.bobPreludeInput
  change ((activate initial alice).respond app alice responses.alicePrelude).application.accepted
    aliceBindingRef.field = none
  rw [respond_accepted]
  rfl

theorem carolInput_accepted (responses : Prefix.CarolResponses) :
    (Prefix.carolInput responses).application.accepted =
      (Prefix.includeLatest
        ((Prefix.aliceInput responses.alicePrelude responses.bobPrelude).respond app alice
          responses.aliceBinding) aliceBinding alice).application.accepted := by
  unfold Prefix.carolInput
  change (Prefix.environmentResult _ (.application (.grant carolBinding))).application.accepted = _
  rw [environment_accepted, environment_accepted, environment_accepted]

theorem included_application (execution : app.Execution) (id : MessageId Player)
    (sent : Message Player app.Payload) (found : execution.network.lookup id = some sent) :
    (Prefix.environmentResult execution (.include id)).application =
      (app.handle execution.application sent).getD execution.application := by
  have shape := Prefix.environmentResult_eq execution (.include id)
    { execution.includePending app id with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include id⟩] } (by
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure])
  rw [shape]
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]

theorem alice_handler_of_accepted (selected : Handle nativeGraph) (before : State nativeGraph)
    (sent : Message Player (Payload nativeGraph))
    (addressed : sent.payload.event? nativeGraph = some aliceBinding)
    (vacant : before.accepted aliceBindingRef.field = none)
    (accepted : ((handle nativeRuntime before sent).getD before).accepted aliceBindingRef.field =
      some selected) :
    handle nativeRuntime (StoreFlip.state selected before) sent =
      (handle nativeRuntime before sent).map (StoreFlip.state selected) := by
  rcases sent with ⟨id, packet⟩
  cases packet with
  | malformed value => cases addressed
  | opening event candidate raw =>
      cases Option.some.inj addressed
      have rejected : handle nativeRuntime before ⟨id, .opening aliceBinding candidate raw⟩ =
          none := by
        simp only [handle]
        split_ifs <;> rfl
      rw [rejected, Option.getD_none, vacant] at accepted
      cases accepted
  | withhold event =>
      cases Option.some.inj addressed
      have rejected : handle nativeRuntime before ⟨id, .withhold aliceBinding⟩ = none := by
        simp only [handle]
        split_ifs <;> rfl
      rw [rejected, Option.getD_none, vacant] at accepted
      cases accepted
  | commitment event candidate =>
      cases Option.some.inj addressed
      by_cases good : before.config.cut.Ready aliceBinding ∧
          before.WithinDeadline nativeRuntime aliceBinding ∧ id.1 = alice ∧ candidate.1 = alice ∧
          before.accepted (.inr aliceBinding) = none ∧ before.HandleUnused candidate
      · obtain ⟨ready, timely, sender, owner, empty, unused⟩ := good
        have handled := handle_commitment_eq nativeRuntime before id aliceBinding candidate alice
          .bool rfl rfl rfl ready timely sender owner empty unused
        rw [handled] at accepted
        change some candidate = some selected at accepted
        cases Option.some.inj accepted
        exact StoreFlip.handle_alice_commitment selected before id owner ready timely sender
          empty unused
      · have rejected : handle nativeRuntime before ⟨id, .commitment aliceBinding candidate⟩ =
            none := by
          have view : nodeView nativeGraph aliceBinding =
              .bind alice .bool rfl rfl := rfl
          simp only [handle, view, Message.sender]
          split_ifs <;> simp_all
        rw [rejected, Option.getD_none, vacant] at accepted
        cases accepted

theorem related_alice_inclusion (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second)
    (audit : first.SubmissionAudit app publicProjection)
    (vacant : first.application.accepted aliceBindingRef.field = none)
    (accepted : (Prefix.includeLatest first aliceBinding alice).application.accepted
      aliceBindingRef.field = some selected) :
    Related selected (Prefix.includeLatest first aliceBinding alice)
      (Prefix.includeLatest second aliceBinding alice) := by
  apply related_includeLatest selected first second related aliceBinding alice
  intro id chosen sent found
  have addressed := latest_lookup_addressed first audit aliceBinding alice id chosen sent found
  have handled : ((app.handle first.application sent).getD first.application).accepted
      aliceBindingRef.field = some selected := by
    unfold Prefix.includeLatest at accepted
    rw [chosen, included_application first id sent found] at accepted
    exact accepted
  change handle nativeRuntime second.application
      ⟨(CandidateFlip.message selected sent).id,
        (CandidateFlip.message selected sent).payload.call⟩ =
    (handle nativeRuntime first.application ⟨sent.id, sent.payload.call⟩).map
      (StoreFlip.state selected)
  rw [related.application]
  exact alice_handler_of_accepted selected first.application ⟨sent.id, sent.payload.call⟩
    addressed vacant handled

end VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry
