/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryPrefix
import Vegas.Compile.WindowedDeliveryRelay
import Vegas.Compile.WindowedDeliveryActivePrefix
import Vegas.Compile.WindowedApplicationInvariants

/-! # Settlement of a complete delivery-enabled response window

An unchanged relay receives an inclusion slot after the response deadline.
The constructor-specific premise certifies a legal expiry at each still-active
source checkpoint. Earlier resolution instead makes the rest of the block idle.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

theorem runPolicies_delivery_block_resolves
    (runtime : WindowedApplication P L) (beforeRoster afterRoster recipients : List P)
    (relay owner : P) (hroster : (beforeRoster ++ relay :: afterRoster).Nodup)
    (players : P → runtime.application.PlayerPolicy) (base : runtime.application.PlayerPolicy)
    (hrelay : players relay = runtime.deliveryBlockPlayer relay base)
    (instruction : ApplicationInstruction P L) (howner : instruction.submitter = some owner)
    {G : Graph P L} (cfg : Config G) (blockIndex : Nat)
    (execution final : runtime.application.PolicyExecution) (activation : Activation Nat)
    (henvironment : execution.environmentHistory.length =
      blockIndex * (recipients.length + (beforeRoster ++ relay :: afterRoster).length + 2))
    (hprincipal : (execution.principalHistory relay).length = 4 * blockIndex)
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hrefines : execution.native.application.base.Refines cfg)
    (hfresh : execution.native.application.FreshActivation)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (initialFields : Nat)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ candidate ∈ runtime.image.instructions,
      candidate.AllocatedAt initialFields)
    (hresolved : runtime.image.ResolvedBindings execution.native.application.base)
    (eligible : ∀ state : runtime.application.PolicyExecution,
      runtime.Consistent state.native.application →
      state.native.application.base.Refines cfg →
      state.native.application.active = some activation →
      activation.since + runtime.windowOf instruction.address <
        state.native.application.base.memory.clock →
      state.native.pool.lookup (relay, state.native.pool.nextSerial relay) = none →
      runtime.image.ResolvedBindings state.native.application.base →
      ∃ payload resolved,
        runtime.dueExpiry? (state.native.application.base.memory,
          state.native.application.active) = some payload ∧
        runtime.handle state.native.application
          ⟨(relay, state.native.pool.nextSerial relay), payload⟩ = some resolved)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment (beforeRoster ++ relay :: afterRoster) recipients)
      (deliveryBlockInvocations (beforeRoster ++ relay :: afterRoster) recipients)
      execution).support) :
    runtime.image.activeAddress? final.native.application.base.memory ≠
      some instruction.address := by
  let roster := beforeRoster ++ relay :: afterRoster
  let environment := runtime.deliveryBlockEnvironment roster recipients
  let preparation := deliveryPreparation roster recipients
  let relays := roster.flatMap fun actor => [Invocation.player actor, Invocation.environment]
  let beforeRelays := beforeRoster.flatMap fun actor =>
    [Invocation.player actor, Invocation.environment]
  let afterRelays := afterRoster.flatMap fun actor =>
    [Invocation.player actor, Invocation.environment]
  let width := recipients.length + roster.length + 2
  have hrosterLength : roster.length = beforeRoster.length + afterRoster.length + 1 := by
    simp [roster, Nat.add_assoc]
  have hrelayMem : relay ∈ roster := by simp [roster]
  have hbeforeNodup : beforeRoster.Nodup := (List.nodup_append.mp hroster).1
  have hnotBefore : relay ∉ beforeRoster := by
    intro hmem
    exact (List.nodup_append.mp hroster).2.2 relay hmem relay (by simp) rfl
  have hrelayCount : relays.countP Invocation.isEnvironment = roster.length :=
    relayInvocations_environment_count roster
  have hbeforeCount : beforeRelays.countP Invocation.isEnvironment = beforeRoster.length :=
    relayInvocations_environment_count beforeRoster
  have hafterCount : afterRelays.countP Invocation.isEnvironment = afterRoster.length :=
    relayInvocations_environment_count afterRoster
  have hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + width →
      runtime.image.instructions[index / width]? = some instruction := by
    intro index hlo hhi
    have hquotient : index / width = blockIndex := by
      apply Nat.div_eq_of_lt_le
      · rw [← henvironment]
        exact hlo
      · rw [Nat.add_mul, Nat.one_mul, ← henvironment]
        exact hhi
    rw [hquotient]
    exact hindex
  have hschedule : deliveryBlockInvocations roster recipients =
      preparation ++ (.environment :: .environment :: relays) := by
    simp [deliveryBlockInvocations, deliveryPreparation, preparation, relays, List.append_assoc]
  rw [hschedule, MessageApplication.runPolicies_append] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨prepared, hprepared, hrest⟩ := hfinal
  have hpreparedResolved := runtime.runPolicies_resolvedBindings initialFields hnodup hallocated
    players environment preparation execution prepared hresolved hprepared
  obtain ⟨hpreparedRefines, hpreparedPublic, _, _, _, hpreparedLength⟩ :=
    runtime.runPolicies_deliveryPreparation roster recipients hroster players execution prepared
      instruction blockIndex henvironment hindex hrefines hfresh hconsistent hprepared
  have hpreparedMemory := congrArg Prod.fst hpreparedPublic
  change prepared.native.application.base.memory = execution.native.application.base.memory
    at hpreparedMemory
  have hpreparedActive : runtime.image.activeAddress? prepared.native.application.base.memory =
      some instruction.address := by rwa [hpreparedMemory]
  have hpreparedActivation : prepared.native.application.active = some activation :=
    (congrArg Prod.snd hpreparedPublic).trans hactivation
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hrest
  obtain ⟨included, hincluded, clocked, hclocked, hrelays⟩ := hrest
  have hincludedRun : included ∈ (runtime.application.runPolicies players environment
      [.environment] prepared).support := by
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincluded
  have hincludedResolved := runtime.runPolicies_resolvedBindings initialFields hnodup hallocated
    players environment [.environment] prepared included hpreparedResolved hincludedRun
  have hincludedLength := runtime.application.runPolicies_environmentHistory_length players
    environment [.environment] prepared included hincludedRun
  simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
    Nat.zero_add] at hincludedLength
  intro hfinalActive
  have hincludedActive : runtime.image.activeAddress? included.native.application.base.memory =
      some instruction.address := by
    by_contra hinactive
    have hremaining : final ∈ (runtime.application.runPolicies players environment
        (.environment :: relays) included).support := by
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
      exact ⟨clocked, hclocked, hrelays⟩
    have hpublic := runtime.runPolicies_deliveryBlock_inactive roster recipients players
      (.environment :: relays) included final instruction (by
        intro index hlo hhi
        apply hindexRange index
        · omega
        · simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte, hrelayCount] at hhi
          dsimp only [width]
          omega) hinactive hremaining
    have hmemory := congrArg Prod.fst hpublic
    change final.native.application.base.memory = included.native.application.base.memory at hmemory
    exact hinactive (hmemory ▸ hfinalActive)
  have hpreparedIndex : runtime.image.instructions[prepared.environmentHistory.length / width]? =
      some instruction := hindexRange _ (by omega) (by dsimp [width]; omega)
  obtain ⟨hincludedRefines, hincludedActivation, _⟩ := runtime.invoke_delivery_refines_of_active
    roster recipients players prepared included .environment instruction owner cfg
    hpreparedIndex howner hpreparedRefines hpreparedActive hincludedActive hincluded
  have hincludedIndex : runtime.image.instructions[included.environmentHistory.length / width]? =
      some instruction := hindexRange _ (by omega) (by dsimp [width]; omega)
  have hincludedSlot : included.environmentHistory.length % width = recipients.length + 1 := by
    rw [hincludedLength, hpreparedLength, henvironment]
    change (blockIndex * width + recipients.length + 1) % width = _
    have hlt : recipients.length + 1 < width := by dsimp [width]; omega
    simpa [Nat.add_assoc, Nat.add_mod] using Nat.mod_eq_of_lt hlt
  obtain ⟨expectedClocked, hclockLaw, hclockValue, hclockedRefines, hclockedActivation,
      hclockedActive⟩ :=
    runtime.delivery_clock_step_checkpoint roster recipients players included instruction
      activation cfg hincludedIndex hincludedSlot hincludedActive
      (hincludedActivation.trans hpreparedActivation) hkey hincludedRefines
  have hclockedRun : clocked ∈ (runtime.application.runPolicies players environment
      [.environment] included).support := by
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hclocked
  have hclockedResolved := runtime.runPolicies_resolvedBindings initialFields hnodup hallocated
    players environment [.environment] included clocked hincludedResolved hclockedRun
  have hclockedEq : clocked = expectedClocked := by
    rw [hclockLaw] at hclockedRun
    exact FinDist.mem_support_pure.mp hclockedRun
  subst expectedClocked
  have hclockedLength := runtime.application.runPolicies_environmentHistory_length players
    environment [.environment] included clocked hclockedRun
  simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
    Nat.zero_add] at hclockedLength
  have hrelaysSplit : relays = beforeRelays ++
      ([Invocation.player relay, .environment] ++ afterRelays) := by
    simp [relays, roster, beforeRelays, afterRelays, List.flatMap_append]
  rw [hrelaysSplit, MessageApplication.runPolicies_append] at hrelays
  simp only [FinDist.support_bind, Set.mem_iUnion] at hrelays
  obtain ⟨atRelay, hbeforeRelay, hpairAndAfter⟩ := hrelays
  have hatRelayLength := runtime.application.runPolicies_environmentHistory_length players
    environment beforeRelays clocked atRelay hbeforeRelay
  rw [hbeforeCount] at hatRelayLength
  have hatRelayActive : runtime.image.activeAddress? atRelay.native.application.base.memory =
      some instruction.address := by
    by_contra hinactive
    have hpublic := runtime.runPolicies_deliveryBlock_inactive roster recipients players
      ([.player relay, .environment] ++ afterRelays) atRelay final instruction (by
        intro index hlo hhi
        apply hindexRange index
        · omega
        · simp only [List.countP_append, List.countP_cons, List.countP_nil,
            Invocation.isEnvironment, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
            hafterCount] at hhi
          dsimp only [width]
          omega) hinactive hpairAndAfter
    have hmemory := congrArg Prod.fst hpublic
    change final.native.application.base.memory = atRelay.native.application.base.memory at hmemory
    exact hinactive (hmemory ▸ hfinalActive)
  have hclockedBefore : clocked ∈ (runtime.application.runPolicies players environment
      (preparation ++ [.environment, .environment]) execution).support := by
    rw [MessageApplication.runPolicies_append, FinDist.support_bind]
    refine Set.mem_iUnion.mpr ⟨prepared, Set.mem_iUnion.mpr ⟨hprepared, ?_⟩⟩
    simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion,
      FinDist.mem_support_pure]
    exact ⟨included, hincluded, clocked, hclocked, rfl⟩
  obtain ⟨hatRelayRefines, hatRelayActivation, hrelayClock⟩ :=
    runtime.runPolicies_delivery_refines_of_final_active roster recipients players
      beforeRelays clocked atRelay instruction owner cfg howner (by
        intro index hlo hhi
        apply hindexRange index
        · omega
        · rw [hbeforeCount] at hhi
          dsimp only [width]
          omega) hclockedRefines hclockedActive hatRelayActive hbeforeRelay
  have hatRelayReached : atRelay ∈ (runtime.application.runPolicies players environment
      ((preparation ++ [.environment, .environment]) ++ beforeRelays) execution).support := by
    rw [MessageApplication.runPolicies_append, FinDist.support_bind]
    exact Set.mem_iUnion.mpr ⟨clocked, Set.mem_iUnion.mpr ⟨hclockedBefore, hbeforeRelay⟩⟩
  have hatRelayResolved := runtime.runPolicies_resolvedBindings initialFields hnodup hallocated
    players environment beforeRelays clocked atRelay hclockedResolved hbeforeRelay
  have hatRelaySerials := runtime.application.runPolicies_serialsBeforeNext players environment
    _ execution atRelay hserials hatRelayReached
  have hnextSerial := hatRelaySerials.lookup_nextSerial_eq_none relay
  obtain ⟨payload, resolved, hdue, hhandle⟩ := eligible atRelay
    (runtime.runPolicies_consistent players environment _ execution atRelay hconsistent
      hatRelayReached) hatRelayRefines
    (hatRelayActivation.trans (hclockedActivation.trans
      (hincludedActivation.trans hpreparedActivation))) (by
      have hmax := Nat.le_max_right included.native.application.base.memory.clock
        (activation.since + runtime.windowOf instruction.address + 1)
      omega) hnextSerial hatRelayResolved
  have hatRelayPrincipal := runtime.application.runPolicies_principalHistory_length relay
    players environment _ execution atRelay hatRelayReached
  have hbeforePlayerCount := relayInvocations_player_count beforeRoster hbeforeNodup relay
  rw [if_neg hnotBefore] at hbeforePlayerCount
  have hprepPlayerCount := deliveryPreparation_player_count roster recipients hroster relay
  rw [if_pos hrelayMem] at hprepPlayerCount
  have hprincipalRelay : (atRelay.principalHistory relay).length = 4 * blockIndex + 3 := by
    let counts : @Invocation P → Bool := fun invocation => match invocation with
      | .player actor => decide (actor = relay)
      | .environment => false
    change (atRelay.principalHistory relay).length =
      (execution.principalHistory relay).length +
        ((preparation ++ [Invocation.environment, Invocation.environment]) ++
          beforeRelays).countP counts
      at hatRelayPrincipal
    rw [List.countP_append, List.countP_append,
      show preparation.countP counts = 3 from hprepPlayerCount,
      show beforeRelays.countP counts = 0 from hbeforePlayerCount,
      show [Invocation.environment, .environment].countP counts = 0 from rfl,
      hprincipal] at hatRelayPrincipal
    simpa only [Nat.add_zero] using hatRelayPrincipal
  have henvironmentRelay : atRelay.environmentHistory.length =
      blockIndex * width + (recipients.length + beforeRoster.length + 2) := by
    change execution.environmentHistory.length = blockIndex * width at henvironment
    omega
  have hslotRelay : atRelay.environmentHistory.length % width =
      recipients.length + beforeRoster.length + 2 := by
    rw [henvironmentRelay]
    have hlt : recipients.length + beforeRoster.length + 2 < width := by
      dsimp [width]
      omega
    simpa [Nat.add_mod] using Nat.mod_eq_of_lt hlt
  obtain ⟨hlaw, hresolvedInactive, _⟩ := runtime.delivery_relay_resolves_active roster recipients
    players relay base hrelay atRelay instruction beforeRoster.length
    (by rw [hprincipalRelay, show (4 * blockIndex + 3) / 4 = blockIndex by omega]; exact hindex)
    (by rw [hprincipalRelay]; omega)
    (hindexRange _ (by omega) (by dsimp [width]; omega)) hslotRelay (by simp [roster])
    hatRelayActive payload resolved hdue hnextSerial hhandle
  rw [MessageApplication.runPolicies_append] at hpairAndAfter
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpairAndAfter
  obtain ⟨afterPair, hpair, hafter⟩ := hpairAndAfter
  have hprojection : (afterPair.native.application, afterPair.native.pool.ledger,
      afterPair.native.receipts) ∈ (FinDist.pure (resolved,
        atRelay.native.pool.ledger ++
          [⟨(relay, atRelay.native.pool.nextSerial relay), payload⟩],
        atRelay.native.receipts ++
          [((relay, atRelay.native.pool.nextSerial relay), true)])).support := by
    rw [← hlaw, FinDist.support_map]
    exact ⟨afterPair, hpair, rfl⟩
  have happlication := congrArg Prod.fst (FinDist.mem_support_pure.mp hprojection)
  change afterPair.native.application = resolved at happlication
  have hafterPairInactive : runtime.image.activeAddress?
      afterPair.native.application.base.memory ≠ some instruction.address := by
    rw [happlication]
    exact hresolvedInactive
  have hafterPairLength := runtime.application.runPolicies_environmentHistory_length players
    environment [.player relay, .environment] atRelay afterPair hpair
  have hpublic := runtime.runPolicies_deliveryBlock_inactive roster recipients players
    afterRelays afterPair final instruction (by
      intro index hlo hhi
      apply hindexRange index
      · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
          Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hafterPairLength
        omega
      · rw [hafterCount] at hhi
        simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
          Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hafterPairLength
        dsimp only [width]
        omega) hafterPairInactive hafter
  have hmemory := congrArg Prod.fst hpublic
  change final.native.application.base.memory = afterPair.native.application.base.memory at hmemory
  exact hafterPairInactive (hmemory ▸ hfinalActive)

end Vegas.WindowedApplication
