/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingUsableWindow

/-! # Arbitrary foreign responses around fresh usable owner registrations

The same retained implementation handles the owner at reconstructed own input.
All other raw response laws stay unchanged. Current completed memory and actual
commitment provenance evolve with each response, rather than being pinned to an
initial shadow. No narrower service-menu admission or utility bound is asserted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- One actual resumption has exact original and retained-implementation
marginals, including arbitrary foreign responses. Its owner slice permits
noncommitment calls and fresh typed private registrations. -/
theorem usable_effective_resume_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsSettledOrMatching owner original repaired)
    (bounds : MessageBounds graph)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (effective : ∀ earlier view response, response ∈ (players owner earlier view).support →
      response ∈ (bounds.menu runtime leaks).actions owner earlier view)
    (usable : ∀ earlier view response, response ∈ (players owner earlier view).support →
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshUsableBindingResponse runtime leaks owner view.application response)
    (actor : Option Player) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks (bounds.menu runtime leaks)
      owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.resume players actor original ∧
      coupling.map Prod.snd = strategy.resume owner players actor repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsSettledOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          ∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw := by
  let app := runtime.reactiveApplication leaks
  let strategy := retainedImplementation runtime leaks (bounds.menu runtime leaks)
    owner reference (players owner)
  cases actor with
  | none =>
      exact ⟨PMF.pure (original, repaired, memory), PMF.pure_map ..,
        PMF.pure_map .., fun next member => by
          cases (PMF.mem_support_pure_iff _ _).mp member
          exact ⟨frame, onlyBindings, past, provenance, started, leftRecall, rightRecall,
            preserved⟩⟩
  | some actor =>
      by_cases own : actor = owner
      · subst actor
        exact frame.usable_effective_response_coupling onlyBindings past provenance bounds
          leftRecall rightRecall preserved players reference started (effective _ _) (usable _ _)
      · let law := players actor (original.recall actor) (original.observe app actor)
        let coupling := law.map fun response =>
          (original.respond app actor response, repaired.respond app actor response, memory)
        have lawEq : players actor (repaired.recall actor) (repaired.observe app actor) = law := by
          rw [← frame.recall actor own, ← frame.foreign_observed actor own]
        refine ⟨coupling, ?_, ?_, ?_⟩
        · simp only [coupling, PMF.map_comp]
          rfl
        · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume,
            own, ↓reduceIte, ReactiveApplication.invoke, PMF.map_comp]
          change law.map _ =
            (players actor (repaired.recall actor) (repaired.observe app actor)).map _
          rw [lawEq]
          rfl
        · intro next member
          obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ member
          have fixed (execution : app.Execution) (slot : CandidateSlot graph) :
              (execution.respond app actor response).application.candidates.lookup (owner, slot) =
                execution.application.candidates.lookup (owner, slot) := by
            rcases response with ⟨transmission⟩
            cases transmission with
            | none => rfl
            | some material =>
                have view := (submitStep_playerView_other
                  (material.call.register execution.application actor) actor owner (Ne.symm own)
                    material.call.packet).trans
                      (material.call.register_other execution.application actor owner (Ne.symm own))
                exact congrFun (congrArg PlayerView.candidates view) slot
          refine ⟨frame.foreign_response actor own response, onlyBindings, ?_,
            provenance.respond_noncommitment actor response response
              (fun same => (own same).elim), ?_,
            app.respond_inputRecall original actor response leftRecall,
            app.respond_inputRecall repaired actor response rightRecall, ?_⟩
          · rw [(runtime.reactive_respond_application leaks original actor response).1]
            exact past
          · rw [app.respond_recall_other repaired actor owner (Ne.symm own) response]
            exact started
          · intro slot raw opened
            rw [fixed original slot] at opened
            rw [fixed repaired slot]
            exact preserved slot raw opened

end Vegas.EventGraphRuntime.BindingMemory.Frame
