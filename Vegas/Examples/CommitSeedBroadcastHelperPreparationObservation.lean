/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialPublicLaw
import Vegas.Pending.PhaseBindingOpaqueStep
import Vegas.Pending.ReactiveContinuationObservation

/-! # Original helper preparations remain private before their publication -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem external_fields (hidden : Player) (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) :
    left.network = right.network ∧ left.receipts = right.receipts ∧
      left.environmentRecall = right.environmentRecall ∧
      left.application.publicView = right.application.publicView ∧
      ∀ who, who ≠ hidden → (left.recall who, left.observe app who) =
        (right.recall who, right.observe app who) := by
  refine ⟨congrArg Prod.fst same, congrArg (fun data => data.2.1) same,
    congrArg (fun data => data.2.2.1) same,
    congrArg (fun data => data.2.2.2.1.application) same, ?_⟩
  intro who different
  have visible := congrFun (congrArg (fun data => data.2.2.2.2) same) who
  change (if who = hidden then none else some (left.recall who, left.observe app who)) =
    (if who = hidden then none else some (right.recall who, right.observe app who)) at visible
  exact Option.some.inj (by simpa only [different, ite_false] using visible)

/-- Actual complete-pending sampling has identical external effects when only
one helper's private preparation and own response word differ. -/
theorem helper_preparation_activation (hidden actor : Player) (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) :
    phaseExternalObservation runtime leaks hidden (completeActivation left actor) =
      phaseExternalObservation runtime leaks hidden (completeActivation right actor) := by
  obtain ⟨network, receipts, service, publicView, inputs⟩ :=
    external_fields hidden left right same
  apply phaseExternalObservation_congr runtime leaks _ _ hidden
  · change (left.network.learn actor (left.network.pending.map Message.id).toFinset) =
      (right.network.learn actor (right.network.pending.map Message.id).toFinset)
    rw [network]
  · exact receipts
  · change left.environmentRecall ++ [⟨left.observeEnvironment app, .activate actor⟩] =
      right.environmentRecall ++ [⟨right.observeEnvironment app, .activate actor⟩]
    have environment : left.observeEnvironment app = right.observeEnvironment app :=
      congrArg (fun data => data.2.2.2.1) same
    rw [service, environment]
  · exact publicView
  · intro who different
    exact congrArg (fun input => input.2.application) (inputs who different)
  · intro who different
    exact congrArg Prod.fst (inputs who different)

/-- Once a helper has sent, its required silent response cannot transmit its
hidden preparation to any other owner, even when its own full input differs. -/
theorem helper_preparation_silent (hidden : Player) (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) :
    phaseExternalObservation runtime leaks hidden (left.respond app hidden ⟨none⟩) =
      phaseExternalObservation runtime leaks hidden (right.respond app hidden ⟨none⟩) := by
  obtain ⟨network, receipts, service, publicView, inputs⟩ :=
    external_fields hidden left right same
  apply phaseExternalObservation_congr runtime leaks
    (left.respond app hidden ⟨none⟩) (right.respond app hidden ⟨none⟩) hidden
      network receipts service publicView
  · intro who different
    exact congrArg (fun input => input.2.application) (inputs who different)
  · intro who different
    rw [app.respond_recall_other _ hidden who different,
      app.respond_recall_other _ hidden who different]
    exact congrArg Prod.fst (inputs who different)

/-- The same raw response by an unsent owner preserves the external comparison.
Its private preparation, evidence alias and emitted packet are all retained;
only the other helper's hidden state is omitted from the readout. -/
theorem helper_preparation_response (hidden actor : Player) (different : actor ≠ hidden)
    (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) (action : app.Action) :
    phaseExternalObservation runtime leaks hidden (left.respond app actor action) =
      phaseExternalObservation runtime leaks hidden (right.respond app actor action) := by
  obtain ⟨network, receipts, service, publicView, inputs⟩ :=
    external_fields hidden left right same
  have observed : left.observe app actor = right.observe app actor :=
    congrArg Prod.snd (inputs actor different)
  have recalled (who : Player) (other : who ≠ hidden) :
      left.recall who = right.recall who := congrArg Prod.fst (inputs who other)
  have views (who : Player) (other : who ≠ hidden) :
      left.application.current.native.playerView who =
        right.application.current.native.playerView who :=
    congrArg (fun input => input.2.application.1) (inputs who other)
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      apply phaseExternalObservation_congr runtime leaks
        (left.respond app actor ⟨none⟩) (right.respond app actor ⟨none⟩) hidden
          network receipts service publicView
      · intro who other
        exact congrArg (fun input => input.2.application) (inputs who other)
      · intro who other
        by_cases active : who = actor
        · subst who
          simp only [ReactiveApplication.Execution.respond, ite_true, recalled actor different,
            observed]
        · rw [app.respond_recall_other _ actor who active,
            app.respond_recall_other _ actor who active]
          exact recalled who other
  | some material =>
      have packet : app.packet (app.submit left.application actor material) actor
          (left.network.known actor) material =
        app.packet (app.submit right.application actor material) actor
          (right.network.known actor) material := by
        change (left.application.submit actor material).emit actor _ material =
          (right.application.submit actor material).emit actor _ material
        rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
        let payload (publicState : PhasePublicView graph) (own : EventGraphRuntime.PlayerView graph)
            (known : List (Message Player (CommitAttemptPacket graph))) :
            CommitAttemptPacket graph :=
          ⟨publicState.attempt, PhaseCount.maskPacket publicState
            ⟨material.call.packet, material.evidence.resolve actor
              (material.call.candidateAfter actor own.candidates)
              (known.map PhaseCount.nativeMessage), own.publicView.tokenFor material.call.packet⟩⟩
        change payload left.application.publicView
          (left.application.current.native.playerView actor) (left.network.known actor) =
            payload right.application.publicView
              (right.application.current.native.playerView actor) (right.network.known actor)
        rw [network]
        exact congrArg₂ (fun publicState own => payload publicState own (right.network.known actor))
          publicView (views actor different)
      have nextPublic : (left.application.submit actor material).publicView =
          (right.application.submit actor material).publicView :=
        (PhaseCount.submit_publicView _ actor material).trans
          (publicView.trans (PhaseCount.submit_publicView _ actor material).symm)
      apply phaseExternalObservation_congr runtime leaks _ _ hidden
      · change (left.network.submit actor _).2 = (right.network.submit actor _).2
        rw [packet, network]
      · exact receipts
      · exact service
      · exact nextPublic
      · intro who other
        change ((left.application.submit actor material).current.native.playerView who,
          (left.application.submit actor material).publicView) =
            ((right.application.submit actor material).current.native.playerView who,
              (right.application.submit actor material).publicView)
        apply Prod.ext _ nextPublic
        by_cases active : who = actor
        · subst who
          exact submit_playerView_congr runtime (fun _ _ => PMF.pure ∅)
            left.application.current.native right.application.current.native actor material
              (views actor different)
        · have foreign (execution : app.Execution) :
              (execution.application.submit actor material).current.native.playerView who =
                execution.application.current.native.playerView who :=
            (submitStep_playerView_other _ actor who active material.call.packet).trans
              (material.call.register_other _ actor who active)
          exact (foreign left).trans ((views who other).trans (foreign right).symm)
      · intro who other
        by_cases active : who = actor
        · subst who
          have packetAfter : app.packet (app.submit left.application actor material) actor
              (right.network.known actor) material =
            app.packet (app.submit right.application actor material) actor
              (right.network.known actor) material := by
            simpa only [network] using packet
          simp only [ReactiveApplication.Execution.respond, ite_true]
          rw [recalled actor different, observed, network, packetAfter]
        · rw [app.respond_recall_other _ actor who active,
            app.respond_recall_other _ actor who active]
          exact recalled who other

/-- Two actual initial submissions with the same public packet may have
arbitrary different hidden preparation and evidence requests. Their complete
external successors agree; no candidate-success equation is assumed. -/
theorem helper_preparation_alias_submission (hidden : Player) (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right)
    (first second : WitnessedSubmission graph)
    (packet : app.packet (app.submit left.application hidden first) hidden
        (left.network.known hidden) first =
      app.packet (app.submit right.application hidden second) hidden
        (right.network.known hidden) second) :
    phaseExternalObservation runtime leaks hidden (left.respond app hidden ⟨some first⟩) =
      phaseExternalObservation runtime leaks hidden (right.respond app hidden ⟨some second⟩) := by
  obtain ⟨network, receipts, service, publicView, inputs⟩ :=
    external_fields hidden left right same
  have nextPublic : (left.application.submit hidden first).publicView =
      (right.application.submit hidden second).publicView :=
    (PhaseCount.submit_publicView _ hidden first).trans
      (publicView.trans (PhaseCount.submit_publicView _ hidden second).symm)
  apply phaseExternalObservation_congr runtime leaks _ _ hidden
  · change (left.network.submit hidden _).2 = (right.network.submit hidden _).2
    rw [packet, network]
  · exact receipts
  · exact service
  · exact nextPublic
  · intro who different
    change ((left.application.submit hidden first).current.native.playerView who,
      (left.application.submit hidden first).publicView) =
        ((right.application.submit hidden second).current.native.playerView who,
          (right.application.submit hidden second).publicView)
    apply Prod.ext _ nextPublic
    have foreign (execution : app.Execution) (material : WitnessedSubmission graph) :
        (execution.application.submit hidden material).current.native.playerView who =
          execution.application.current.native.playerView who :=
      (submitStep_playerView_other _ hidden who different material.call.packet).trans
        (material.call.register_other _ hidden who different)
    exact (foreign left first).trans
      ((congrArg (fun input => input.2.application.1) (inputs who different)).trans
        (foreign right second).symm)
  · intro who different
    rw [app.respond_recall_other _ hidden who different,
      app.respond_recall_other _ hidden who different]
    exact congrArg Prod.fst (inputs who different)

/-- The actual unsent response kernel, rather than only its support, is
independent of another helper's hidden initial preparation. -/
theorem helper_preparation_invocation (players : Player → app.Policy)
    (hidden actor : Player) (different : actor ≠ hidden) (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) :
    (app.invoke players actor left).map (phaseExternalObservation runtime leaks hidden) =
      (app.invoke players actor right).map (phaseExternalObservation runtime leaks hidden) := by
  have inputs := (external_fields hidden left right same).2.2.2.2 actor different
  have pasts : left.recall actor = right.recall actor := congrArg Prod.fst inputs
  have views : left.observe app actor = right.observe app actor := congrArg Prod.snd inputs
  have kernel : players actor (left.recall actor) (left.observe app actor) =
      players actor (right.recall actor) (right.observe app actor) := by rw [pasts, views]
  simp only [ReactiveApplication.invoke, PMF.map_comp, Function.comp_def]
  rw [kernel]
  apply congrArg (fun readout =>
    (players actor (right.recall actor) (right.observe app actor)).map readout)
  funext action
  exact helper_preparation_response hidden actor different left right same action

/-- Replacing only a previously-sent helper's next response by WAIT gives the
same entire external invocation law across hidden preparation aliases. -/
theorem helper_preparation_wait_invocation (hidden : Player) (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right)
    (players : Player → app.Policy)
    (waitLeft : players hidden (left.recall hidden) (left.observe app hidden) =
      PMF.pure ⟨none⟩)
    (waitRight : players hidden (right.recall hidden) (right.observe app hidden) =
      PMF.pure ⟨none⟩) :
    (app.invoke players hidden left).map (phaseExternalObservation runtime leaks hidden) =
      (app.invoke players hidden right).map (phaseExternalObservation runtime leaks hidden) := by
  simp only [ReactiveApplication.invoke, waitLeft, waitRight, PMF.pure_map]
  exact congrArg PMF.pure (helper_preparation_silent hidden left right same)

end Vegas.Examples.CommitSeedBroadcast
