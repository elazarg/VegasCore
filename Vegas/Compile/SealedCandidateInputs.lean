/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceInputs
import Vegas.Compile.SealedCandidatePolicy
import Interaction.SealedCandidateOpening
import Interaction.SealedCandidateMemory

/-! # Candidate-host draws at the original source inputs

Before timeout, actual opening admission supplies the value of its accepted
candidate. Agreement of openable accepted values and the honest player's cache
with a source realization therefore gives exact declared-read kernel equality.
Unopenable commitments are permitted, and no private table enters the policy.
The generated policy establishes its own cache/catalog agreement even when
all opponents deviate. The whole-program probability proof must still show
that accepted values agree with its extracted source realization.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty)

/-- A generated player's cache remains exact under arbitrary opponent and
environment policies. Its preparation discipline follows from the generated
command selector and is imposed on no other player. -/
theorem candidatePolicy_memory (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : CommitPolicy G who)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment : MessageApplication.EnvironmentPolicy
      (supported.resolvingRuntime nullValue window).candidateApplication)
    (hplayer : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hactual : execution ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
        players environment schedule (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support) :
    SealedResolution.PreparedCandidateOwner (supported.resolvingRuntime nullValue window)
      who execution := by
  let runtime := supported.resolvingRuntime nullValue window
  apply SealedResolution.runPolicies_preparedCandidateOwner who players environment ?_
    schedule execution hactual
  intro current payload hcurrent hsubmit site handle hpacket
  rw [hplayer] at hsubmit
  rcases supported.resolvingPolicy_submission nullValue window who policy
      (runtime.registeredPlayerHistory (current.principalHistory who))
      (runtime.registeredPlayerView (State.observe _ current.native who)) payload hsubmit with
    ⟨node, hcommit, hcache⟩ | ⟨node, openingHandle, value, hopening, _hready⟩
  · rw [hpacket] at hcommit
    cases hcommit
    rw [runtime.registeredPlayerHistory_cache] at hcache
    obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp hcache
    erw [hcurrent.memory, hvalue]
    simp
  · rw [hpacket] at hopening
    contradiction

variable (cfg : ReachableConfig G) (hterminal : Terminal G cfg.1)
variable (nullValue : L.Val ty) (window : Nat)

include hterminal

/-- An actual successful opening has the source reveal value whenever its
openable accepted candidate has the source commitment value. Openability of
other accepted candidates is neither assumed nor needed. -/
theorem candidate_opened_source_value
    (state : (supported.resolvingRuntime nullValue window).candidateApplication.Application)
    (hopening : SealedResolution.CandidateOpeningInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hclear : state.visible.timeouts = [])
    (haccepted : ∀ index handle value,
      SealedProgram.Event.accepted index handle ∈ state.visible.events →
      state.service.lookup handle = .openable value →
      cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L))
    (index : Nat) (value : L.Val ty)
    (hopened : SealedProgram.Event.opened index value ∈ state.visible.events) :
    cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L) := by
  obtain ⟨owner, source, requires, handle, hrule, hselected, _howner, hvalue⟩ :=
    hopening hclear index value hopened
  obtain ⟨node, producer, guard, rfl, rfl, hsem, _hcommit⟩ :=
    supported.ruleAt_reveal hrule rfl
  have hstored := haccepted producer.val handle value
    (SealedProgram.accepted_mem_of_accepted?_eq_some hselected) hvalue
  have hsource : cfg.1.nodeValues nullValue producer = value := by
    simp only [Config.nodeValues, Store.getAs, hstored, TypedValue.as?, dite_true,
      Option.getD_some, cast_eq]
  rw [supported.terminal_reveal_store cfg hterminal nullValue node producer hsem, hsource]

/-- A generated preparation in an actual candidate-host execution fills a
fresh catalog slot and uses the original source kernel at its exact declared
source reads. Cache agreement is derived from the generated policy. The
remaining premise concerns accepted values, not equality of input environments
or execution laws. -/
theorem candidate_registration_kernel
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment : MessageApplication.EnvironmentPolicy
      (supported.resolvingRuntime nullValue window).candidateApplication)
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hactual : execution ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
        players environment schedule (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (hclear : execution.native.application.visible.timeouts = [])
    (who : Player) (original replacement : CommitPolicy G who)
    (hplayer : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who original))
    (haccepted : ∀ index handle value,
      SealedProgram.Event.accepted index handle ∈ execution.native.application.visible.events →
      execution.native.application.service.lookup handle = .openable value →
      cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L))
    (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈
      ((supported.resolvingRuntime nullValue window).candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who original)
        (execution.principalHistory who) (State.observe _ execution.native who)).support) :
    ∃ (node : Fin G.nodeCount) (guard : EventGuard L)
      (hsem : (G.nodeRow node).sem = .commit who guard) (reads : ReadEnv L guard.choiceReads),
      slot = node.val ∧
      execution.native.application.service.lookup (who, node.val) = .fresh ∧
      ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
      (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who replacement)
        (execution.principalHistory who) (State.observe _ execution.native who) =
        (replacement node guard hsem reads).map (fun choice =>
          .privateCommand ⟨(node.val,
            cast (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩) := by
  let runtime := supported.resolvingRuntime nullValue window
  rw [SealedResolution.candidatePlayerPolicy,
    supported.resolvingPolicy_no_timeout _ _ _ _ _ _ hclear] at hcommand
  obtain ⟨node, guard, hsem, reads, hslot, hcache, hreads, hkernel⟩ :=
    supported.selected_registration_kernel who [] original _ _ _ slot value hcommand
  have hopening := SealedResolution.runPolicies_candidate_openings players environment
    schedule _ execution SealedResolution.CandidateOpeningInvariant.initial hactual
  have hprepared := supported.candidatePolicy_memory nullValue window who original players
    environment hplayer schedule execution hactual
  refine ⟨node, guard, hsem, reads, hslot, ?_, ?_, ?_⟩
  · erw [runtime.eventHistory_cache, runtime.registeredPlayerHistory_cache] at hcache
    erw [hprepared.memory node.val, hcache]
    rfl
  · apply cfg.sealedPlayerStore_reads_eq ty who _ execution.native.application.visible.events ?_
      (supported.candidate_opened_source_value cfg hterminal nullValue window
        execution.native.application hopening hclear haccepted)
      guard.choiceReads reads (ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hreads)
    intro index handle stored hmem howner hcache
    erw [runtime.eventHistory_cache, runtime.registeredPlayerHistory_cache] at hcache
    have hlookup : execution.native.application.service.lookup (who, handle.2) =
        .openable stored := by
      erw [hprepared.memory handle.2, hcache]
      rfl
    rw [← howner] at hlookup
    exact haccepted index handle stored hmem hlookup
  · rw [SealedResolution.candidatePlayerPolicy,
      supported.resolvingPolicy_no_timeout _ _ _ _ _ _ hclear]
    exact hkernel replacement

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidate_registration_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_registration_kernel
