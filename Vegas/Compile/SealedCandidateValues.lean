/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateInputs
import Vegas.Compile.SealedCandidateReadBound
import Interaction.SealedCandidateAcceptance

/-! # Honest candidate values under arbitrary native deviations

Generated submissions retain their source-site identity through delivery and
replay. In assigned-value execution, each honest player's private cache and
openable candidate slots retain exactly those assigned values. The focal
player's preparations, candidate identities, and submission policies are unrestricted.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)

/-- A generated owner's accepted handle belongs to that very source site,
even when every other player and the environment behaves arbitrarily. -/
theorem candidatePolicy_accepted_slot (who : Player) (policy : CommitPolicy G who)
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
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (node : Nat) (handle : CommitmentHandle Player Nat)
    (haccepted : SealedProgram.Event.accepted node handle ∈
      execution.native.application.visible.events) (howner : handle.1 = who) :
    handle = (who, node) := by
  let runtime := supported.resolvingRuntime nullValue window
  apply runtime.runPolicies_candidate_accepted_property
    (fun index selected => selected.1 = who → selected = (who, index)) players environment ?_
    schedule execution hactual node handle haccepted howner
  intro current sender payload hsubmit index selected hpacket hauth hwho
  have hsender := hauth.trans hwho
  rw [hsender, hplayer] at hsubmit
  rcases supported.resolvingPolicy_submission nullValue window who policy _ _ payload hsubmit with
    ⟨site, hpayload, _hcache⟩ | ⟨site, openingHandle, value, hpayload, _hready⟩
  · rw [hpacket] at hpayload
    cases hpayload
    rfl
  · rw [hpacket] at hpayload
    contradiction

variable (values : Fin G.nodeCount → L.Val ty) (focal : Player)
variable (deviator :
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
variable (environment : MessageApplication.EnvironmentPolicy
  (supported.resolvingRuntime nullValue window).candidateApplication)

/-- The actual assigned-value policy leaves only its assigned value in each
honest candidate slot. This includes execution after earlier timeouts. -/
theorem runPolicies_candidateValues_lookup
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hactual : execution ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
        (supported.candidateValuePlayers nullValue window values focal deviator)
        environment schedule (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (who : Player) (hwho : who ≠ focal) (node : Fin G.nodeCount) (value : L.Val ty)
    (hlookup : execution.native.application.service.lookup (who, node.val) = .openable value) :
    value = values node := by
  let runtime := supported.resolvingRuntime nullValue window
  let encoding : ChoiceEncoding (L.Val ty) runtime.candidateApplication.PlayerCommand :=
    runtime.program.registrationEncoding node.val
  have hmemory := supported.candidatePolicy_memory nullValue window who
    (supported.valuePolicy values who)
    (supported.candidateValuePlayers nullValue window values focal deviator) environment
    (by rw [candidateValuePlayers, Profile.update_of_ne _ _ hwho]) schedule execution hactual
  have hcache : encoding.cachedValue runtime.candidateApplication
      (execution.principalHistory who) = some value := by
    rw [hmemory.memory node.val] at hlookup
    change ((encoding.cachedValue runtime.candidateApplication
      (execution.principalHistory who)).map CommitmentCandidate.openable).getD .fresh =
        .openable value at hlookup
    cases hc : encoding.cachedValue runtime.candidateApplication
        (execution.principalHistory who) with
    | none => simp only [hc, Option.map_none, Option.getD_none] at hlookup; contradiction
    | some cached =>
        simp only [hc, Option.map_some, Option.getD_some,
          CommitmentCandidate.openable.injEq] at hlookup
        exact congrArg some hlookup
  apply encoding.runPolicies_cachedValue_property runtime.candidateApplication who
    (fun stored => stored = values node)
    (supported.candidateValuePlayers nullValue window values focal deviator) environment ?_
    schedule _ execution (by intro stored h; cases h) hactual value hcache
  intro history view command stored hchosen hdecode
  have hcommand : command = encoding.encode stored := encoding.decode_sound command stored hdecode
  rw [hcommand] at hchosen
  rw [candidateValuePlayers, Profile.update_of_ne _ _ hwho] at hchosen
  obtain ⟨actual, hindex, hvalue, guard, _hsem⟩ :=
    supported.selected_valuePolicy_registration values who view.application.timeouts
      (runtime.eventHistory (runtime.registeredPlayerHistory history))
      (runtime.eventView (runtime.registeredPlayerView view)) _ node.val stored hchosen
  have hnode : actual = node := Fin.ext hindex.symm
  simpa only [hnode] using hvalue

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.runPolicies_candidateValues_lookup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.runPolicies_candidateValues_lookup
