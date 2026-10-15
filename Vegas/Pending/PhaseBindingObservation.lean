/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePreparedBinding
import Vegas.Pending.PhaseBindingRepairObservation
import Vegas.Pending.ReactiveRawBindingFrame
import Vegas.Pending.PhaseBindingSlotHistory

/-! # Joint public observations of arbitrary typed binding encodings -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A canonical nonmissing binding emits one identical complete packet for
every typed result. Neither accepted failure nor its preparation is public. -/
theorem phaseBindingResponse_packet (state : PhaseRuntimeState graph) (owner : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    let material (result : PublicationResult (L.Val payload)) : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, .prepared serial), match result with
        | .failure => none
        | .success value => some ⟨payload, value⟩⟩, .none⟩
    (state.submit owner (material first)).emit owner known (material first) =
      (state.submit owner (material second)).emit owner known (material second) := by
  dsimp only
  rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
  rfl

/-- The transport nonce and complete newly authored envelope are the same
when only the private typed result of a nonmissing binding changes. -/
theorem phaseBindingResponse_emission (execution : (app).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    let material (result : PublicationResult (L.Val payload)) : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, .prepared serial), match result with
        | .failure => none
        | .success value => some ⟨payload, value⟩⟩, .none⟩
    (execution.network.submit owner
      ((execution.application.submit owner (material first)).emit owner
        (execution.network.known owner) (material first))).1 =
      (execution.network.submit owner
        ((execution.application.submit owner (material second)).emit owner
          (execution.network.known owner) (material second))).1 :=
  congrArg (fun packet => (execution.network.submit owner packet).1)
    (phaseBindingResponse_packet execution.application owner (execution.network.known owner)
      event payload first second serial)

private theorem submit_playerView_other (state : PhaseRuntimeState graph)
    (owner observer : Player) (different : observer ≠ owner)
    (material : WitnessedSubmission graph) :
    (state.submit owner material).playerView observer = state.playerView observer := by
  apply Prod.ext
  · exact (submitStep_playerView_other (material.call.register state.current.native owner)
      owner observer different material.call.packet).trans
        (material.call.register_other state.current.native owner observer different)
  · exact PhaseCount.submit_publicView state owner material

/-- Both encodings retain the entire network, receipts and environment recall,
the full current environment input, and every other owner's complete next input.
Only the sender's private catalogue and own response word may differ. -/
theorem phaseBindingResponse_hidden_congr
    (execution : (app).Execution) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    let left := execution.respond app owner
      (phaseBindingResponse runtime leaks owner event payload first serial)
    let right := execution.respond app owner
      (phaseBindingResponse runtime leaks owner event payload second serial)
    left.network = right.network ∧ left.receipts = right.receipts ∧
      left.environmentRecall = right.environmentRecall ∧
      left.observeEnvironment app = right.observeEnvironment app ∧
      left.application.publicView = right.application.publicView ∧
      (∀ observer, observer ≠ owner →
        (left.recall observer, left.observe app observer) =
          (right.recall observer, right.observe app observer)) := by
  let material (result : PublicationResult (L.Val payload)) : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  let left := execution.respond app owner
    (phaseBindingResponse runtime leaks owner event payload first serial)
  let right := execution.respond app owner
    (phaseBindingResponse runtime leaks owner event payload second serial)
  have packet := phaseBindingResponse_packet execution.application owner
    (execution.network.known owner) event payload first second serial
  have network : left.network = right.network :=
    congrArg (fun packet => (execution.network.submit owner packet).2) packet
  have visible (result : PublicationResult (L.Val payload)) :
      (execution.respond app owner
        (phaseBindingResponse runtime leaks owner event payload result
          serial)).application.publicView =
          execution.application.publicView :=
      PhaseCount.submit_publicView _ owner (material result)
  have publicEq : left.application.publicView = right.application.publicView :=
    (visible first).trans (visible second).symm
  refine ⟨network, rfl, rfl, ?_, publicEq, ?_⟩
  · change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) =
        ⟨right.network.publicView, right.application.publicView, right.receipts⟩
    rw [network, publicEq]
    rfl
  · intro observer different
    have recalled := ((app).respond_recall_other execution owner observer different
      (phaseBindingResponse runtime leaks owner event payload first serial)).trans
        ((app).respond_recall_other execution owner observer different
          (phaseBindingResponse runtime leaks owner event payload second serial)).symm
    apply Prod.ext recalled
    change (⟨left.network.observe observer, left.application.playerView observer, left.receipts⟩ :
      (app).PlayerView) = ⟨right.network.observe observer, right.application.playerView observer,
        right.receipts⟩
    rw [network]
    have observed := (submit_playerView_other execution.application owner observer different
      (material first)).trans
        (submit_playerView_other execution.application owner observer different
          (material second)).symm
    exact congrArg (fun view => (⟨right.network.observe observer, view, execution.receipts⟩ :
      (app).PlayerView)) observed

/-- Candidate freshness after an encoded binding is independent of its typed
result, including the distinction between an unusable and an openable handle. -/
theorem phaseBindingResponse_fresh_iff (execution : (app).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty) (first second : PublicationResult (L.Val payload))
    (serial : Nat) (query : CandidateSlot graph) :
    (execution.respond app owner (phaseBindingResponse runtime leaks owner event payload first
      serial)).application.current.native.candidates.lookup (owner, query) = .fresh ↔
    (execution.respond app owner (phaseBindingResponse runtime leaks owner event payload second
      serial)).application.current.native.candidates.lookup (owner, query) = .fresh := by
  let nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
    fun _ _ => PMF.pure ∅
  let native := ReactiveApplication.Execution.initial (runtime.reactiveApplication nativeLeaks)
    execution.application.current.native
  exact (submitted_binding_fresh_iff runtime nativeLeaks native owner event serial
    (match first with | .failure => none | .success value => some ⟨payload, value⟩) query).trans
      (submitted_binding_fresh_iff runtime nativeLeaks native owner event serial
        (match second with | .failure => none | .success value => some ⟨payload, value⟩) query).symm

/-- The entire joint external channel of a nonmissing encoded binding is a
single result-independent atom. This retains every other owner's full input
together with the complete network and scheduler observation. -/
theorem phaseBindingResponse_observation_law (execution : (app).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty) (law : PMF (PublicationResult (L.Val payload)))
    (serial : Nat) :
    let observe (next : (app).Execution) :=
      (next.network, next.receipts, next.environmentRecall, next.observeEnvironment app,
        fun observer => if observer = owner then none
          else some (next.recall observer, next.observe app observer))
    (law.map fun result => observe (execution.respond app owner
      (phaseBindingResponse runtime leaks owner event payload result serial))) =
      PMF.pure (observe (execution.respond app owner
        (phaseBindingResponse runtime leaks owner event payload .failure serial))) := by
  intro observe
  calc
    _ = law.map (fun _ => observe (execution.respond app owner
        (phaseBindingResponse runtime leaks owner event payload .failure serial))) := by
      apply map_congr_on_support
      intro result _supported
      obtain ⟨network, receipts, service, environment, _public, foreign⟩ :=
        phaseBindingResponse_hidden_congr runtime leaks execution owner event payload result
          .failure serial
      dsimp only [observe]
      refine Prod.ext network (Prod.ext receipts (Prod.ext service (Prod.ext environment ?_)))
      funext observer
      by_cases same : observer = owner
      · simp only [same, ↓reduceIte]
      · simp only [same, ↓reduceIte]
        exact congrArg some (foreign observer same)
    _ = _ := PMF.map_const _ _

variable [Fintype Player]

/-- The actual slot encoder's entire joint external observation law depends
only on its independent slot draw, with arbitrary typed-result laws integrated
out. Accepted failure remains part of the original result law. -/
theorem phaseBindingSlotPolicy_observation_law
    (bounds : MessageBounds graph) (execution : (app).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (results : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (nonempty : (PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
      (execution.recall owner) (execution.observe app owner)).Nonempty) :
    let observe (next : (app).Execution) :=
      (next.network, next.receipts, next.environmentRecall, next.observeEnvironment app,
        fun observer => if observer = owner then none
          else some (next.recall observer, next.observe app observer))
    ((PhaseCount.phaseBindingSlotPolicy runtime leaks bounds owner event payload results
      (execution.recall owner) (execution.observe app owner)).map
        (fun response => observe (execution.respond app owner response))) =
      (PMF.uniformOfFinset _ nonempty).map fun serial =>
        observe (execution.respond app owner
          (phaseBindingResponse runtime leaks owner event payload .failure serial)) := by
  intro observe
  rw [PhaseCount.phaseBindingSlotPolicy, dite_eq_left nonempty, PMF.map_bind]
  calc
    _ = (PMF.uniformOfFinset _ nonempty).bind (fun serial =>
        PMF.pure (observe (execution.respond app owner
          (phaseBindingResponse runtime leaks owner event payload .failure serial)))) := by
      apply bind_congr_on_support
      intro serial _selected
      simpa only [PMF.map_comp, Function.comp_def] using
        phaseBindingResponse_observation_law runtime leaks execution owner event payload
          (results (execution.recall owner) (execution.observe app owner)) serial
    _ = _ := PMF.bind_pure_comp _ _

end Vegas.EventGraphRuntime
