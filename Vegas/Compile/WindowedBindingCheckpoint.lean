/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedBindingBlock
import Vegas.Compile.WindowedBlockSample
import Vegas.Compile.WindowedBlockCaches

/-! # Binding source successors at actual windowed checkpoints -/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {owner : P} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}

/-- If the ordinary service slot resolves a generated binding head after all
raw player polls, its actual accepted message determines a legal source
successor. No canonical focal policy or pre-window timing premise is used. -/
theorem binding_normal_resolution
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (deadline : Nat)
    (hselect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution polled included :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hpolled : polled ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution).support)
    (hincluded : included ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.invoke
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        polled .environment).support)
    (hinactive : (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
      included.native.application.base.memory ≠ some state.nodes.length) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph
        (state.addCommitEvent name owner guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      included.native.application.base.Refines sourceNext.current.graph.1 ∧
      included.native.application.FreshActivation := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let timed := fallback.bindingTimeoutCode fresh state deadline
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf =
        .bind code :: nextPlan.instructions deadlineOf := by
    rfl
  have hindexOriginal := checkpoint.instruction_at (.bind code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.bind code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup code.node = some (.bind code) at hlookupOriginal
  have hlookup : runtime.image.lookup timed.node = some (.bind timed) := by
    change runtime.image.lookup code.node = some (.bind timed)
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, hselect]
    rfl
  have hlength := checkpoint.environmentHistory_length
  have hquotient : execution.environmentHistory.length / (roster.length + 2) = blockIndex := by
    rw [hlength, Nat.mul_div_cancel]
    omega
  have hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.bind timed) := by
    simp only [hquotient, runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hselect]
  have hpublic := runtime.runPolicies_players_publicState players
    (runtime.blockEnvironment roster)
    (roster.flatMap fun actor => [Invocation.player actor, .player actor]) (by simp)
    execution polled hpolled
  have hrefines := runtime.runPolicies_players_refines players (runtime.blockEnvironment roster)
    (roster.flatMap fun actor => [Invocation.player actor, .player actor]) (by simp)
    execution polled checkpoint.refines hpolled
  have hactiveExecution := checkpoint.activeAddress?_head (.bind code) _ hhead
  have hactive : runtime.image.activeAddress? polled.native.application.base.memory =
      some timed.node := by
    have hmemory : polled.native.application.base.memory =
        execution.native.application.base.memory := by
      exact congrArg Prod.fst hpublic
    rw [hmemory]
    change runtime.image.activeAddress? execution.native.application.base.memory =
      some code.node
    exact hactiveExecution
  have hpolledLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster)
    (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution polled hpolled
  have hcount : (roster.flatMap fun actor =>
      [Invocation.player actor, Invocation.player actor]).countP
        Invocation.isEnvironment = 0 := by
    apply List.countP_eq_zero.mpr
    intro invocation hmem
    rcases List.mem_flatMap.mp hmem with ⟨actor, _, hpair⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    rcases hpair with hpair | hpair <;> subst invocation <;>
      simp [Invocation.isEnvironment]
  have hslot : polled.environmentHistory.length % (roster.length + 2) = 0 := by
    rw [hpolledLength, hcount, Nat.add_zero, hlength]
    exact Nat.mul_mod_left _ _
  have hactivationExecution := congrArg Prod.snd hpublic
  have hconsistent := checkpoint.consistent
  cases hactivation : execution.native.application.active with
  | none =>
      have hmap := hconsistent.1
      rw [hactivation, hactiveExecution] at hmap
      simp at hmap
  | some activation =>
      have hactivationPolled : polled.native.application.active = some activation := by
        exact hactivationExecution.trans hactivation
      have hkey : activation.key = timed.node := by
        have hmap := hconsistent.1
        rw [hactivation, Option.map_some, hactiveExecution] at hmap
        change activation.key = code.node
        exact Option.some.inj hmap
      have hpolledEnv : polled.environmentHistory.length =
          execution.environmentHistory.length := by
        rw [hpolledLength, hcount, Nat.add_zero]
      have hindexPolled : runtime.image.instructions[polled.environmentHistory.length /
          (roster.length + 2)]? = some (.bind timed) := by
        rw [hpolledEnv]
        exact hindex
      exact runtime.blockEnvironment_normal_binding_source_coupling roster players guard tail
        fallback fresh state current unrestricted deadline polled included activation hindexPolled
        hslot hactive hactivationPolled hkey hlookup hrefines hinactive hincluded

/-- One complete generated service block resolves a source binding even when
the focal player's replacement policy is completely unrestricted. The public
fallback selector is certified at the emitted binding, and one duplicate-free
roster member distinct from the focal player supplies the unchanged expiry
relay. Every supported final execution carries a legal source successor,
native refinement, a fresh successor activation, and inactivity of the
original binding address. -/
theorem binding_block_resolution
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (deadline : Nat)
    (hselect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hunchanged : relay ≠ focal)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph
        (state.addCommitEvent name owner guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      final.native.application.base.Refines sourceNext.current.graph.1 ∧
      final.native.application.FreshActivation ∧
      (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
        final.native.application.base.memory ≠ some state.nodes.length := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let timed := fallback.bindingTimeoutCode fresh state deadline
  let before := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let relayPairs := roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf =
        .bind code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.bind code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.bind code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup code.node = some (.bind code) at hlookupOriginal
  have hlookup : runtime.image.lookup timed.node = some (.bind timed) := by
    change runtime.image.lookup code.node = some (.bind timed)
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, hselect]
    rfl
  have hlength := checkpoint.environmentHistory_length
  have hquotient : execution.environmentHistory.length / (roster.length + 2) =
      blockIndex := by
    rw [hlength, Nat.mul_div_cancel]
    omega
  have hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.bind timed) := by
    simp only [hquotient, runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hselect]
  have hindexBlock : runtime.image.instructions[blockIndex]? = some (.bind timed) := by
    rwa [hquotient] at hindex
  have hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + roster.length + 2 →
      runtime.image.instructions[index / (roster.length + 2)]? = some (.bind timed) := by
    intro index hlo hhi
    have hsame : index / (roster.length + 2) =
        execution.environmentHistory.length / (roster.length + 2) := by
      have hmod : execution.environmentHistory.length % (roster.length + 2) = 0 := by
        rw [hlength]
        exact Nat.mul_mod_left _ _
      have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      apply Nat.div_eq_of_lt_le
      · rw [hbase]
        omega
      · rw [Nat.add_mul, hbase]
        omega
    rw [hsame]
    exact hindex
  have hactiveExecution := checkpoint.activeAddress?_head (.bind code) _ hhead
  obtain ⟨activation, hactivationExecution, hkeyOriginal, _⟩ :=
    checkpoint.active_origin_clock (.bind code) _ hhead
  have hkey : activation.key = timed.node := hkeyOriginal
  have hbeforeNoEnvironment : Invocation.environment ∉ before := by
    simp [before]
  have hbeforeCount : before.countP Invocation.isEnvironment = 0 := by
    apply List.countP_eq_zero.mpr
    intro invocation hmem
    rcases List.mem_flatMap.mp hmem with ⟨actor, _, hpair⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    rcases hpair with hpair | hpair <;> subst invocation <;>
      simp [Invocation.isEnvironment]
  have hrelayCount : relayPairs.countP Invocation.isEnvironment = roster.length := by
    have relayCount : ∀ entries : List P,
        (entries.flatMap fun actor => [Invocation.player actor, .environment]).countP
          Invocation.isEnvironment = entries.length := by
      intro entries
      induction entries with
      | nil => rfl
      | cons actor rest ih =>
          simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
            List.countP_nil, Invocation.isEnvironment, Bool.false_eq_true,
            ↓reduceIte, ih, List.length_cons, Nat.add_comm]
    exact relayCount roster
  have hrosterPositive : 0 < roster.length := by
    obtain ⟨index, hindexLt, _⟩ := List.mem_iff_getElem.mp hrelay
    omega
  have hdecomposed : WindowedApplication.blockInvocations roster =
      before ++ (Invocation.environment :: Invocation.environment :: relayPairs) := by
    simp only [WindowedApplication.blockInvocations, before, relayPairs,
      List.cons_append, List.nil_append, List.append_assoc]
  rw [hdecomposed, MessageApplication.runPolicies_append] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨polled, hpolled, hremaining⟩ := hfinal
  rw [show Invocation.environment :: Invocation.environment :: relayPairs =
    [Invocation.environment] ++ (Invocation.environment :: relayPairs) by rfl,
    MessageApplication.runPolicies_append] at hremaining
  simp only [FinDist.support_bind, Set.mem_iUnion] at hremaining
  obtain ⟨included, hincludedRun, hafterIncluded⟩ := hremaining
  have hincluded : included ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) polled .environment).support := by
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedRun
  have hpublicPolled := runtime.runPolicies_players_publicState players
    (runtime.blockEnvironment roster) before hbeforeNoEnvironment execution polled hpolled
  have hmemoryPolled := congrArg Prod.fst hpublicPolled
  change polled.native.application.base.memory = execution.native.application.base.memory
    at hmemoryPolled
  have hactivePolled : runtime.image.activeAddress?
      polled.native.application.base.memory = some timed.node := by
    rw [hmemoryPolled]
    exact hactiveExecution
  have hactivationPolledEq := congrArg Prod.snd hpublicPolled
  change polled.native.application.active = execution.native.application.active
    at hactivationPolledEq
  have hactivationPolled : polled.native.application.active = some activation :=
    hactivationPolledEq.trans hactivationExecution
  have hrefinesPolled := runtime.runPolicies_players_refines players
    (runtime.blockEnvironment roster) before hbeforeNoEnvironment execution polled
    checkpoint.refines hpolled
  have hpolledLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster) before execution polled hpolled
  rw [hbeforeCount, Nat.add_zero] at hpolledLength
  have hindexPolled : runtime.image.instructions[polled.environmentHistory.length /
      (roster.length + 2)]? = some (.bind timed) := by
    rw [hpolledLength]
    exact hindex
  have hslotPolled : polled.environmentHistory.length % (roster.length + 2) = 0 := by
    rw [hpolledLength, hlength]
    exact Nat.mul_mod_left _ _
  have hincludedLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster) [Invocation.environment] polled included hincludedRun
  simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
    Nat.zero_add] at hincludedLength
  by_cases hincludedInactive : runtime.image.activeAddress?
      included.native.application.base.memory ≠ some timed.node
  · obtain ⟨chosen, sourceNext, hsource, hincludedRefines, hincludedFresh⟩ :=
      binding_normal_resolution unrestricted nextPlan profile fallback deadline
        hselect current execution polled included checkpoint hpolled hincluded
        (by
          change runtime.image.activeAddress? included.native.application.base.memory ≠
            some state.nodes.length at hincludedInactive
          exact hincludedInactive)
    have hremainingIndex : ∀ index, included.environmentHistory.length ≤ index →
        index < included.environmentHistory.length +
          (Invocation.environment :: relayPairs).countP Invocation.isEnvironment →
        runtime.image.instructions[index / (roster.length + 2)]? = some (.bind timed) := by
      intro index hlo hhi
      apply hindexRange index
      · omega
      · simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte,
          hrelayCount] at hhi
        omega
    have hpublicFinal := runtime.runPolicies_block_inactive roster players
      (Invocation.environment :: relayPairs) included final (.bind timed)
      hremainingIndex hincludedInactive hafterIncluded
    have hfinalInactive : runtime.image.activeAddress?
        final.native.application.base.memory ≠ some timed.node := by
      have hmemory := congrArg Prod.fst hpublicFinal
      change final.native.application.base.memory = included.native.application.base.memory
        at hmemory
      rwa [hmemory]
    refine ⟨chosen, sourceNext, hsource, ?_, ?_, ?_⟩
    · exact runtime.runPolicies_block_inactive_refines sourceNext.current.graph.1 roster
        players (Invocation.environment :: relayPairs) included final (.bind timed)
        hremainingIndex hincludedInactive hincludedRefines hafterIncluded
    · exact runtime.runPolicies_block_inactive_freshActivation roster players
        (Invocation.environment :: relayPairs) included final (.bind timed)
        hremainingIndex hincludedInactive hincludedFresh hafterIncluded
    · change runtime.image.activeAddress? final.native.application.base.memory ≠
          some state.nodes.length at hfinalInactive
      exact hfinalInactive
  · have hincludedActive : runtime.image.activeAddress?
        included.native.application.base.memory = some timed.node :=
      Classical.byContradiction hincludedInactive
    obtain ⟨hincludedRefines, hincludedActivationEq, _⟩ :=
      runtime.invoke_refines_of_active roster players polled included .environment
        (.bind timed) owner current.current.graph.1 hindexPolled (by rfl) hrefinesPolled
        hactivePolled hincludedActive hincluded
    have hactivationIncluded : included.native.application.active = some activation :=
      hincludedActivationEq.trans hactivationPolled
    have hslotIncluded : included.environmentHistory.length % (roster.length + 2) = 1 := by
      rw [hincludedLength, hpolledLength, hlength]
      simp [Nat.add_mod]
    have hindexIncluded : runtime.image.instructions[included.environmentHistory.length /
        (roster.length + 2)]? = some (.bind timed) := by
      apply hindexRange included.environmentHistory.length
      · rw [hincludedLength, hpolledLength]
        omega
      · rw [hincludedLength, hpolledLength]
        omega
    obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp hrelay
    have hrelayPolicy : players relay = runtime.blockPlayer relay
        (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile relay)) := by
      simp only [players, windowedPlayers, Function.update_of_ne hunchanged,
        windowedReferencePlayers, runtime]
    have hprincipalStart := checkpoint.historyAlignment hroster relay hrelay |>.1
    have hprincipalPolled := runtime.application.runPolicies_principalHistory_length relay
      players (runtime.blockEnvironment roster) before execution polled hpolled
    have hpolls := WindowedApplication.ordinaryPolls_player_count roster hroster relay
    change before.countP _ = _ at hpolls
    have hprincipalPolled' : (polled.principalHistory relay).length =
        3 * blockIndex + 2 := by
      have hcounted := hprincipalPolled.trans
        (congrArg (fun count => (execution.principalHistory relay).length + count)
          hpolls)
      simp only [hrelay, if_pos] at hcounted
      omega
    have hprincipalIncluded := runtime.application.runPolicies_principalHistory_length relay
      players (runtime.blockEnvironment roster) [Invocation.environment] polled included
      hincludedRun
    simp only [List.countP_cons, List.countP_nil, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero] at hprincipalIncluded
    have hplayerIndex : runtime.image.instructions[(included.principalHistory relay).length / 3]? =
        some (.bind timed) := by
      rw [hprincipalIncluded, hprincipalPolled']
      have hdivision : (3 * blockIndex + 2) / 3 = blockIndex := by omega
      rw [hdivision]
      exact hindexBlock
    have hplayerSlot : (included.principalHistory relay).length % 3 = 2 := by
      rw [hprincipalIncluded, hprincipalPolled']
      omega
    have hprefixSupport : included ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) (before ++ [Invocation.environment])
        execution).support := by
      rw [MessageApplication.runPolicies_append, FinDist.support_bind]
      exact Set.mem_iUnion.mpr ⟨polled, Set.mem_iUnion.mpr ⟨hpolled, hincludedRun⟩⟩
    have hsettled : runtime.image.activeAddress? final.native.application.base.memory ≠
        some timed.node := by
      have hrosterSplit : (beforeRoster ++ relay :: afterRoster).Nodup := by
        rwa [← hsplit]
      apply runtime.binding_relay_roster_inactive beforeRoster afterRoster owner relay hrosterSplit
        (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile relay)) players
        hrelayPolicy guard tail fallback fresh state deadline current (.bind timed) activation
        included final (by rfl) hplayerIndex hplayerSlot
      · simpa [← hsplit] using hslotIncluded
      · intro index hlo hhi
        have hsplitLength := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons] at hsplitLength
        have hsame := hindexRange index (by omega) (by omega)
        rw [hsplit] at hsame
        exact hsame
      · exact hincludedActive
      · exact hactivationIncluded
      · exact hkey
      · rw [hkey]
        exact hlookup
      · exact hincludedRefines
      · exact runtime.runPolicies_consistent players (runtime.blockEnvironment roster)
          (before ++ [Invocation.environment]) execution included checkpoint.consistent
          hprefixSupport
      · exact runtime.application.runPolicies_serialsBeforeNext players
          (runtime.blockEnvironment roster) (before ++ [Invocation.environment]) execution
          included checkpoint.serialsBeforeNext hprefixSupport
      · simpa [relayPairs, hsplit, List.append_assoc] using hafterIncluded
    obtain ⟨clocked, hclockLaw, _, hclockedRefines, hclockedActivationEq,
        hclockedActive⟩ :=
      runtime.block_clock_step_checkpoint roster players included (.bind timed) activation
        current.current.graph.1 hindexIncluded hslotIncluded hincludedActive
        hactivationIncluded hkey hincludedRefines
    have hrelayFinal : final ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) relayPairs clocked).support := by
      rw [show Invocation.environment :: relayPairs =
        [Invocation.environment] ++ relayPairs by rfl,
        MessageApplication.runPolicies_append, hclockLaw, FinDist.pure_bind] at hafterIncluded
      exact hafterIncluded
    have hclockedLength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) [Invocation.environment] included clocked (by
        rw [hclockLaw]
        exact FinDist.mem_support_pure.mpr rfl)
    simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
      Nat.zero_add] at hclockedLength
    obtain ⟨chosen, sourceNext, hsource, hfinalRefines, hfinalFresh⟩ :=
      runtime.runPolicies_binding_relay_pairs_source_coupling roster players roster 0 guard tail
        fallback fresh state current unrestricted deadline clocked final activation
        (by intro index actor hactor; simpa using hactor) (by simp)
        (by
          intro index hlo hhi
          apply hindexRange index
          · omega
          · omega)
        (by
          rw [hclockedLength, hincludedLength, hpolledLength, hlength]
          have htwo : 2 < roster.length + 2 := by omega
          simp [Nat.add_mod, Nat.mod_eq_of_lt htwo])
        hclockedActive (hclockedActivationEq.trans hactivationIncluded) hkey hlookup
        hclockedRefines hsettled hrelayFinal
    refine ⟨chosen, sourceNext, hsource, hfinalRefines, hfinalFresh, ?_⟩
    change runtime.image.activeAddress? final.native.application.base.memory ≠
      some state.nodes.length at hsettled
    exact hsettled

/-- Every supported execution of the complete binding block is a genuine
initialized successor checkpoint for the source continuation. The result
retains the actual sequential source step and settlement of the predecessor
binding address. -/
theorem binding_block
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (deadline : Nat)
    (hselect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hunchanged : relay ≠ focal)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph
        (state.addCommitEvent name owner guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster focal
        replacement (blockIndex + 1) nextPlan profile.afterCommit sourceNext final ∧
      (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
        final.native.application.base.memory ≠ some state.nodes.length ∧
      SmallStep ⟨Γ, current.current.source, .commit name owner guard tail⟩
        ⟨(name, .sealed owner ty) :: Γ, sourceNext.current.source, tail⟩ := by
  obtain ⟨chosen, sourceNext, hsource, hrefines, hfresh, hinactive⟩ :=
    binding_block_resolution unrestricted nextPlan profile fallback deadline hselect current
      execution final checkpoint hroster relay hrelay hunchanged hfinal
  have hstep : SmallStep ⟨Γ, current.current.source, .commit name owner guard tail⟩
      ⟨(name, .sealed owner ty) :: Γ, sourceNext.current.source, tail⟩ := by
    rw [hsource]
    exact .commit guard tail chosen (unrestricted current.current.source chosen)
  refine ⟨chosen, sourceNext, hsource, ?_, hinactive, hstep⟩
  refine ⟨.binding checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hfresh⟩
  · have hcount := checkpoint.blockCount
    have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
        unrestricted nextPlan).instructions deadlineOf =
          .bind ((.here guard tail : SourceDecisionSite owner
            (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
              ((.here guard tail : SourceDecisionSite owner
                (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) ::
            nextPlan.instructions deadlineOf := rfl
    rw [hhead, List.length_cons] at hcount
    omega
  · exact block_caches
      (.binding (newName := newName) (fresh := fresh) unrestricted nextPlan) nextPlan profile
      deadlineOf _ rfl binding choice windowOf roster hroster focal replacement blockIndex
      current execution final checkpoint hfinal

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_normal_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_normal_resolution

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_resolution

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_block
