/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationPrefixHistory

/-! # Carol's native guess is independent of Alice's hidden bit

The comparison permits different arbitrary earlier Bob responses. Carol's
complete input agrees, and every current raw response produces the same
owner-visible binding result after reserved inclusion and ordinary expiry.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open ReactiveAssociationEvidence

theorem native_carol_prefix_recall (bit : Bool) (response : nativeApp.Action) :
    (carolSite bit response).recall carol = [] := by
  cases bit
  · exact congrArg Prod.fst (carolSite_input response ⟨none⟩)
  · exact (congrArg Prod.fst (carolSite_input ⟨none⟩ response)).symm

theorem native_carol_reserved_views (left right response : nativeApp.Action)
    (players : Player → nativeApp.Policy) (afterLeft afterRight : nativeApp.Execution)
    (leftMem : afterLeft ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest carolBinding carol)
      ((carolSite false left).respond nativeApp carol response)).support)
    (rightMem : afterRight ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest carolBinding carol)
      ((carolSite true right).respond nativeApp carol response)).support) :
    afterLeft.application.playerView carol = afterRight.application.playerView carol := by
  obtain ⟨leftTrace⟩ := native_carol_raw_trace false left
  obtain ⟨rightTrace⟩ := native_carol_raw_trace true right
  obtain ⟨leftOrigins, leftRecall, leftRetained, leftSerials, leftMemory, leftAudit⟩ :=
    native_transport_raw_history _ leftTrace carol rfl
  obtain ⟨rightOrigins, rightRecall, rightRetained, rightSerials, rightMemory, rightAudit⟩ :=
    native_transport_raw_history _ rightTrace carol rfl
  have inputs := carolSite_input left right
  have recalls := congrArg Prod.fst inputs
  have views := congrArg Prod.snd inputs
  have applicationViews := congrArg ReactiveApplication.PlayerView.application views
  have ledgers := congrArg (fun view : nativeApp.PlayerView => view.messages.ledger) views
  have ownerViews := nativeRuntime.reactive_playerView_congr nativeLeaks _ _ carol
    applicationViews (leftMemory.trans rightMemory.symm)
  have unique (bit : Bool) (prior : nativeApp.Action) :
      nativeRuntime.UniqueEventOutput nativeLeaks carol carolBinding
        ((carolSite bit prior).recall carol) := by
    rw [native_carol_prefix_recall]
    intro first firstMem
    cases firstMem
  have law := nativeRuntime.reactive_reserved_playerView_congr nativeLeaks carol carolBinding
    _ _ response ownerViews recalls ledgers leftOrigins rightOrigins leftRecall rightRecall
    leftRetained rightRetained (unique false left) (unique true right) leftSerials rightSerials
    (leftAudit response) (rightAudit response)
  dsimp only at law
  rw [nativeRuntime.interaction_includeLatest_environment] at leftMem rightMem
  obtain ⟨next, pureStep⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks carol carolBinding
    ((carolSite false left).respond nativeApp carol response)
  rw [pureStep] at leftMem
  have firstEq := FinDist.mem_support_pure.mp leftMem
  subst afterLeft
  rw [pureStep, FinDist.map_pure] at law
  have mapped : afterRight.application.playerView carol ∈
      (FinDist.pure (next.application.playerView carol)).support := by
    rw [law, FinDist.support_map]
    exact ⟨afterRight, rightMem, rfl⟩
  exact (FinDist.mem_support_pure.mp mapped).symm

private theorem maintenance_views (players : Player → nativeApp.Policy)
    (left right afterLeft afterRight : nativeApp.Execution)
    (who : Player) (command : EnvironmentCommand nativeGraph)
    (maintenance : ∀ event, command ≠ .executeSample event)
    (views : left.application.playerView who = right.application.playerView who)
    (leftMem : afterLeft ∈ (nativeApp.dispatch players (.application command) left).support)
    (rightMem : afterRight ∈ (nativeApp.dispatch players (.application command) right).support) :
    afterLeft.application.playerView who = afterRight.application.playerView who := by
  have leftMoved := nativeRuntime.reactive_application_support nativeLeaks players command
    left afterLeft leftMem
  have rightMoved := nativeRuntime.reactive_application_support nativeLeaks players command
    right afterRight rightMem
  have law := nativeRuntime.maintenance_playerView_congr left.application right.application
    who command maintenance views
  have mapped : afterLeft.application.playerView who ∈
      ((environmentStep nativeRuntime right.application command).map
        fun state => state.playerView who).support := by
    rw [← law, FinDist.support_map]
    exact ⟨afterLeft.application, leftMoved, rfl⟩
  cases command with
  | executeSample event => exact (maintenance event rfl).elim
  | advanceClock | grant event | expire event =>
      simp only [environmentStep, FinDist.mem_support_pure] at rightMoved
      simp only [environmentStep, FinDist.map_pure, FinDist.mem_support_pure] at mapped
      rw [rightMoved]
      exact mapped

def nativeCarolSettlement : List (ServiceInstruction nativeGraph) :=
  [.includeLatest carolBinding carol, .tick, .tick, .expire carolBinding]

def nativeCarolGuess (players : Player → nativeApp.Policy)
    (bit : Bool) (prior response : nativeApp.Action) : FinDist nativeApp.Execution :=
  nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork nativeCarolSettlement
    ((carolSite bit prior).respond nativeApp carol response)

theorem native_carol_guess_rounds (players : Player → nativeApp.Policy)
    (bit : Bool) (prior response : nativeApp.Action) :
    nativeApp.runRounds nativeScheduler players 4
      ((carolSite bit prior).respond nativeApp carol response) =
      nativeCarolGuess players bit prior response := by
  exact native_segment_rounds players (nativePlan.take 9) nativeCarolSettlement
    (nativePlan.drop 13) rfl _ (by
      rw [nativeApp.respond_environmentRecall, carolSite_rounds]
      rfl)

theorem native_carol_settled_views (players : Player → nativeApp.Policy)
    (left right response : nativeApp.Action) (afterLeft afterRight : nativeApp.Execution)
    (leftMem : afterLeft ∈ (nativeCarolGuess players false left response).support)
    (rightMem : afterRight ∈ (nativeCarolGuess players true right response).support) :
    afterLeft.application.playerView carol = afterRight.application.playerView carol := by
  simp only [nativeCarolGuess, nativeCarolSettlement, runInteractionPlan,
    FinDist.bind_pure] at leftMem rightMem
  obtain ⟨leftIncluded, leftIn, leftMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftMem)
  obtain ⟨rightIncluded, rightIn, rightMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightMem)
  have included := native_carol_reserved_views left right response players
    leftIncluded rightIncluded leftIn rightIn
  obtain ⟨leftTicked, leftTick, leftMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftMem)
  obtain ⟨rightTicked, rightTick, rightMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightMem)
  have ticked := maintenance_views players _ _ _ _ carol .advanceClock (by simp) included
    (by simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using leftTick)
    (by simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using rightTick)
  obtain ⟨leftDue, leftTick, leftMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftMem)
  obtain ⟨rightDue, rightTick, rightMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightMem)
  have due := maintenance_views players _ _ _ _ carol .advanceClock (by simp) ticked
    (by simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using leftTick)
    (by simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using rightTick)
  exact maintenance_views players _ _ _ _ carol (.expire carolBinding) (by simp) due
    (by simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using leftMem)
    (by simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using rightMem)

theorem native_carol_binding_views (left right : State nativeGraph)
    (views : left.playerView carol = right.playerView carol) :
    carolBindingRef.get? left.config.store = carolBindingRef.get? right.config.store := by
  have observed := congrArg (fun view : PlayerView nativeGraph =>
    carolBindingRef.get? view.observation.store) views
  change carolBindingRef.get? (nativeGraph.playerStore carol left.config.store) =
    carolBindingRef.get? (nativeGraph.playerStore carol right.config.store) at observed
  rwa [carolBindingRef.get?_playerStore carol _ rfl,
    carolBindingRef.get?_playerStore carol _ rfl] at observed

theorem native_carol_guess_law (players : Player → nativeApp.Policy)
    (left right response : nativeApp.Action) :
    (nativeCarolGuess players false left response).map (fun final =>
      carolBindingRef.get? final.application.config.store) =
    (nativeCarolGuess players true right response).map (fun final =>
      carolBindingRef.get? final.application.config.store) := by
  obtain ⟨first, firstMem⟩ := (nativeCarolGuess players false left response).support_nonempty
  obtain ⟨second, secondMem⟩ := (nativeCarolGuess players true right response).support_nonempty
  have comparison := native_carol_binding_views _ _
    (native_carol_settled_views players left right response first second firstMem secondMem)
  trans FinDist.pure (carolBindingRef.get? second.application.config.store)
  · apply FinDist.eq_pure_of_support_subset_singleton _
      (carolBindingRef.get? second.application.config.store)
    intro value member
    obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ member
    exact native_carol_binding_views _ _
      (native_carol_settled_views players left right response final second finalMem secondMem)
  · symm
    apply FinDist.eq_pure_of_support_subset_singleton _
      (carolBindingRef.get? second.application.config.store)
    intro value member
    obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ member
    have equal := native_carol_binding_views _ _
      (native_carol_settled_views players left right response first final firstMem finalMem)
    exact equal.symm.trans comparison

/-- Carol uses one behavioral policy on her entire input. Bob's earlier raw
response may differ arbitrarily between the two hidden-bit worlds. -/
def nativeCarolPlay (players : Player → nativeApp.Policy)
    (bit : Bool) (prior : nativeApp.Action) : FinDist nativeApp.Execution :=
  (players carol ((carolSite bit prior).recall carol)
    ((carolSite bit prior).observe nativeApp carol)).bind (nativeCarolGuess players bit prior)

theorem native_carol_policy_law (players : Player → nativeApp.Policy)
    (left right : nativeApp.Action) :
    (nativeCarolPlay players false left).map
        (fun final => carolBindingRef.get? final.application.config.store) =
    (nativeCarolPlay players true right).map
        (fun final => carolBindingRef.get? final.application.config.store) := by
  have inputs := carolSite_input left right
  have same : players carol ((carolSite false left).recall carol)
      ((carolSite false left).observe nativeApp carol) =
      players carol ((carolSite true right).recall carol)
        ((carolSite true right).observe nativeApp carol) :=
    congrArg (fun input => players carol input.1 input.2) inputs
  simp only [nativeCarolPlay, FinDist.map_bind]
  rw [same]
  exact FinDist.bind_congr fun response _ => native_carol_guess_law players left right response

/-- Even type-dependent or certificate-dependent randomization in Bob's
earlier response leaves Carol's committed-guess law unchanged. -/
theorem native_carol_mixture_law (players : Player → nativeApp.Policy)
    (left right : FinDist nativeApp.Action) :
    (left.bind (nativeCarolPlay players false)).map (fun final =>
      carolBindingRef.get? final.application.config.store) =
    (right.bind (nativeCarolPlay players true)).map (fun final =>
      carolBindingRef.get? final.application.config.store) := by
  rw [FinDist.map_bind, FinDist.map_bind]
  trans (nativeCarolPlay players true ⟨none⟩).map
    (fun final => carolBindingRef.get? final.application.config.store)
  · calc
      _ = left.bind (fun _ => (nativeCarolPlay players true ⟨none⟩).map
          (fun final => carolBindingRef.get? final.application.config.store)) :=
        FinDist.bind_congr fun response _ => native_carol_policy_law players response ⟨none⟩
      _ = _ := FinDist.bind_const _ _
  · symm
    calc
      _ = right.bind (fun _ => (nativeCarolPlay players true ⟨none⟩).map
          (fun final => carolBindingRef.get? final.application.config.store)) := by
        apply FinDist.bind_congr
        intro response _
        exact (native_carol_policy_law players ⟨none⟩ response).symm.trans
          (native_carol_policy_law players ⟨none⟩ ⟨none⟩)
      _ = _ := FinDist.bind_const _ _

def nativeCarolGuessLaw (players : Player → nativeApp.Policy) :
    FinDist (PublicationResult Bool) :=
  (nativeCarolPlay players false ⟨none⟩).map (fun final =>
    (carolBindingRef.get? final.application.config.store).getD .failure)

theorem native_carol_common_law (players : Player → nativeApp.Policy)
    (bit : Bool) (prior : nativeApp.Action) :
    (nativeCarolPlay players bit prior).map (fun final =>
      (carolBindingRef.get? final.application.config.store).getD .failure) =
      nativeCarolGuessLaw players := by
  have options : (nativeCarolPlay players bit prior).map
      (fun final => carolBindingRef.get? final.application.config.store) =
      (nativeCarolPlay players false ⟨none⟩).map
        (fun final => carolBindingRef.get? final.application.config.store) := by
    cases bit
    · exact (native_carol_policy_law players prior ⟨none⟩).trans
        (native_carol_policy_law players ⟨none⟩ ⟨none⟩).symm
    · exact (native_carol_policy_law players ⟨none⟩ prior).symm
  simpa only [FinDist.map_comp, Function.comp_def, nativeCarolGuessLaw] using
    congrArg (fun law => law.map (fun result => result.getD .failure)) options
theorem native_carol_prefix_ready (bit : Bool) (response : nativeApp.Action) :
    (carolSite bit response).application.config.cut.Ready carolBinding :=
  carolSite_ready bit response

theorem native_carol_prefix_invariant (bit : Bool) (response : nativeApp.Action) :
    (carolSite bit response).application.Invariant nativeInputs := by
  obtain ⟨trace⟩ := native_carol_raw_trace bit response
  exact (nativeRuntime.reactiveStateInvariant nativeLeaks nativeInputs).history
    (FinDist.pure nativeInitial) nativeHorizon nativeScheduler (by
      intro state member
      cases FinDist.mem_support_pure.mp member
      exact State.initial_invariant nativeInputs) trace

theorem native_carol_guess_stored (players : Player → nativeApp.Policy)
    (bit : Bool) (prior response : nativeApp.Action) (final : nativeApp.Execution)
    (supported : final ∈ (nativeCarolGuess players bit prior response).support) :
    final.application.Invariant nativeInputs ∧
      ∃ guess, carolBindingRef.get? final.application.config.store = some guess := by
  let execution := (carolSite bit prior).respond nativeApp carol response
  have submitted := nativeRuntime.reactive_respond_progress nativeLeaks nativeInputs
    (carolSite bit prior) carol response (native_carol_prefix_invariant bit prior)
  have ready : execution.application.config.cut.Ready carolBinding := by
    have configEq : execution.application.config =
        (carolSite bit prior).application.config := by
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => rfl
      | some transmission =>
          cases transmission with
          | submit material =>
              exact (submitStep_config _ _ _).trans (material.call.register_facts _ _).1
          | replay id =>
              cases found : ((carolSite bit prior).network.known carol).find?
                  (fun message => message.id = id) <;>
                simp only [execution, ReactiveApplication.Execution.respond,
                  MessageNetwork.replay, found]
    rw [configEq]
    exact native_carol_prefix_ready bit prior
  have strategic : (nativeGraph.actor? carolBinding).isSome = true := by decide
  obtain ⟨entered, activated⟩ := submitted.invariant.activatedAt_eq_some_of_ready_actor
    carolBinding ready strategic
  have enteredLe := submitted.invariant.activated_le carolBinding entered activated
  change entered ≤ execution.application.clock at enteredLe
  have progress := nativeRuntime.runInteractionPlan_facts nativeLeaks nativeInputs players
    nativeNetwork nativeCarolSettlement execution final submitted.invariant supported
  refine ⟨progress.invariant, ?_⟩
  have completed : carolBinding ∈ final.application.config.cut.completed := by
    obtain ⟨due, dueMem, expired, expiryMem, finalMem⟩ :=
      nativeRuntime.runInteractionPlan_support_instruction nativeLeaks players nativeNetwork
        [.includeLatest carolBinding carol, .tick, .tick] [] (.expire carolBinding)
        execution final supported
    have beforeExpiry := nativeRuntime.runInteractionPlan_facts nativeLeaks nativeInputs players
      nativeNetwork _ execution due submitted.invariant dueMem
    have expiredProgress := nativeRuntime.interactionStep_facts nativeLeaks nativeInputs players
      nativeNetwork (.expire carolBinding) due expired beforeExpiry.invariant expiryMem
    have finalEq : final = expired := FinDist.mem_support_pure.mp finalMem
    rw [finalEq]
    rcases beforeExpiry.ready_or_completed carolBinding ready with completed | stillReady
    · exact expiredProgress.completed completed
    · apply nativeRuntime.interactionStep_expire_complete nativeLeaks players nativeNetwork
        carolBinding due expired stillReady strategic entered
        (beforeExpiry.activated carolBinding entered activated stillReady.1) _ expiryMem
      have clock := beforeExpiry.clock
      change due.application.clock = execution.application.clock + 2 at clock
      change 2 ≤ due.application.clock - entered
      omega
  have present := final.application.config.output_available carolBinding
  have field : (final.application.config.store (.inr carolBinding)).isSome := present.mpr completed
  have refPresent := carolBindingRef.get?_isSome final.application.config.store field
  exact Option.isSome_iff_exists.mp refPresent

end VegasTests.SelectiveAssociation
