/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedConditionalBlock
import Vegas.Compile.WindowedBlockCaches
import Vegas.Compile.ConditionalDisposition

/-! # Conditional source successors at actual windowed checkpoints -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
/-- A relay pair contributes exactly one environment invocation. -/
theorem conditionalRelayPairs_environment_count (relays : List P) :
    (relays.flatMap fun relay =>
      [Invocation.player relay, Invocation.environment]).countP
        Invocation.isEnvironment = relays.length := by
  induction relays with
  | nil => rfl
  | cons relay rest ih =>
      simp [List.flatMap_cons, Invocation.isEnvironment, ih]

/-- After the clock edge and any still-active relay prefix, static binding
origins and resolved-binding preservation make conditional expiry concrete. -/
theorem conditional_source_relay_eligibility_after_clock
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (execution middle : runtime.application.PolicyExecution)
    (priorRelays : List (@Invocation P)) (relay : P) (initialFields : Nat)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ candidate ∈ runtime.image.instructions,
      candidate.AllocatedAt initialFields)
    (horigins : runtime.image.HasBindingOrigins)
    (hresolved : runtime.image.ResolvedBindings execution.native.application.base)
    (hconditional : .conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline) ∈ runtime.image.instructions)
    (howner : instruction.submitter = some who)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (Invocation.environment :: priorRelays).countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 1)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup activation.key = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hmiddleActive : runtime.image.activeAddress?
      middle.native.application.base.memory = some instruction.address)
    (hmiddle : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (.environment :: priorRelays) execution).support) :
    ∃ payload resolved,
      runtime.dueExpiry?
        (middle.native.application.base.memory, middle.native.application.active) =
          some payload ∧
      middle.native.pool.lookup (relay, middle.native.pool.nextSerial relay) = none ∧
      runtime.handle middle.native.application
        ⟨(relay, middle.native.pool.nextSerial relay), payload⟩ = some resolved := by
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let code := site.code fresh build sourceSlot deadline
  have hinitialIndex := hindex execution.environmentHistory.length
    (Nat.le_refl _) (by
      simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte]
      omega)
  obtain ⟨clocked, hclockLaw, hclock, hclockRefines, hclockActivation,
      hclockActive⟩ := runtime.block_clock_step_checkpoint roster players execution
    instruction activation current.current.graph.1 hinitialIndex hslot hactive
    hactivation hkey hrefines
  have hclockedSupport : clocked ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) [.environment] execution).support := by
    rw [hclockLaw]
    simp
  have hclockedLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster) [.environment] execution clocked hclockedSupport
  have hmiddleTail : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) priorRelays clocked).support := by
    rw [show Invocation.environment :: priorRelays =
      [Invocation.environment] ++ priorRelays by rfl,
      MessageApplication.runPolicies_append, hclockLaw, FinDist.pure_bind] at hmiddle
    exact hmiddle
  obtain ⟨hmiddleRefines, hmiddleActivation, hclockMono⟩ :=
    runtime.runPolicies_refines_of_final_active roster players priorRelays clocked middle
      instruction who current.current.graph.1 howner (by
        intro index hlo hhi
        apply hindex index
        · omega
        · simp only [List.countP_cons, List.countP_nil,
            Invocation.isEnvironment, ↓reduceIte] at hclockedLength ⊢
          omega) hclockRefines hclockActive hmiddleActive hmiddleTail
  have hmiddleConsistent := runtime.runPolicies_consistent players
    (runtime.blockEnvironment roster) (.environment :: priorRelays) execution middle
    hconsistent hmiddle
  have hmiddleFresh := (runtime.application.runPolicies_serialsBeforeNext players
    (runtime.blockEnvironment roster) (.environment :: priorRelays) execution middle
    hserials hmiddle).lookup_nextSerial_eq_none relay
  have hmiddleActivation' : middle.native.application.active = some activation :=
    hmiddleActivation.trans (hclockActivation.trans hactivation)
  have hmiddleResolved := runtime.runPolicies_resolvedBindings initialFields hnodup hallocated
    players (runtime.blockEnvironment roster) (.environment :: priorRelays) execution middle
    hresolved hmiddle
  obtain ⟨disposition, hbinding, hcanonical⟩ :=
    ConditionalPublicationSite.bindingDisposition_at_source_prefix guard tail spec fresh build
      sourceSlot deadline current runtime.image middle.native.application.base hmiddleRefines
      hmiddleResolved horigins hconditional
  have hready := ConditionalPublicationSite.readyDisposition_at_source_prefix
    guard tail spec fresh build sourceSlot deadline current
      middle.native.application.base hmiddleRefines disposition hbinding hcanonical
  have hoverdue : activation.since + runtime.windowOf activation.key <
      middle.native.application.base.memory.clock := by
    rw [hkey]
    omega
  let resolved := runtime.advanceTo middle.native.application
    (middle.native.application.base.publishConditional code none)
  have hhandle : runtime.handle middle.native.application
      ⟨(relay, middle.native.pool.nextSerial relay), .conditional activation.key .expire⟩ =
        some resolved := by
    exact runtime.handle_conditionalExpire_after_window middle.native.application activation
      hmiddleConsistent hmiddleActivation' code hcode hready hoverdue _
  exact ⟨.conditional activation.key .expire, resolved,
    runtime.dueExpiry?_of_conditional middle.native.application activation hmiddleConsistent
      hmiddleActivation' code hcode hoverdue, hmiddleFresh, hhandle⟩

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.conditional_source_relay_eligibility_after_clock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.conditional_source_relay_eligibility_after_clock

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending headPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {owner : P} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}
variable {accounted : CommitmentAccounting pending tail}
variable {headAccounted : CommitmentAccounting headPending
  (.commit name owner guard (.reveal publicName owner name .here tail))}

/-- The common complete-block result for both conditional accounting
constructors.  Constructor-specific wrappers only provide the emitted head
and continuation certificate. -/
theorem conditional_block_resolution_common
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (headPlan : ApplicationPlan headAccounted fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (hhead : headPlan.instructions deadlineOf =
      .conditional ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.code fresh state
          ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.sourceField fresh state)
          (deadlineOf ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.choice.publicationNode fresh state))) :: nextPlan.instructions deadlineOf)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex headPlan profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hreference : root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement relay = root.windowedReferencePlayers rootProfile deadlineOf binding
        choice windowOf relay)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
        evalGuard guard (spec.encoding.symm result)
          ((current.current.source.toView owner).eraseEnv) = true ∧
        sourceNext.current.source =
          (current.current.source.cons (spec.encoding.symm result)).cons
            (spec.encoding.symm result) ∧
        final.native.application.base.Refines sourceNext.current.graph.1 ∧
        final.native.application.FreshActivation ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
              |>.choice.publicationNode fresh state) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let sourceSlot := site.sourceField fresh state
  let deadline := deadlineOf (site.choice.publicationNode fresh state)
  let code := site.code fresh state sourceSlot deadline
  let instruction : ApplicationInstruction P L := .conditional code
  have hindexOriginal := checkpoint.instruction_at instruction _ hhead
  have hindexBlock : runtime.image.instructions[blockIndex]? = some instruction := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf instruction
    (List.mem_of_getElem? hindexOriginal)
  have hlookup : runtime.image.lookup instruction.address = some instruction := by
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
  have hlength := checkpoint.environmentHistory_length
  have hprincipal := checkpoint.historyAlignment hroster relay hrelay |>.1
  have hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + roster.length + 2 →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction := by
    intro index hlo hhi
    have hmod : execution.environmentHistory.length % (roster.length + 2) = 0 := by
      rw [hlength]
      exact Nat.mul_mod_left _ _
    have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    have hsame : index / (roster.length + 2) =
        execution.environmentHistory.length / (roster.length + 2) := by
      apply Nat.div_eq_of_lt_le
      · rw [hbase]
        omega
      · rw [Nat.add_mul, hbase]
        omega
    rw [hsame, hlength]
    simpa [Nat.mul_div_left] using hindexBlock
  have hactive := checkpoint.activeAddress?_head instruction _ hhead
  obtain ⟨activation, hactivation, hkey, _⟩ :=
    checkpoint.active_origin_clock instruction _ hhead
  have hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup := by
    dsimp only [runtime, windowed]
    rw [ApplicationImage.coveredNodes_withChoiceTimeouts,
      ApplicationImage.coveredNodes_withBindingTimeouts]
    exact root.coveredNodes_nodup deadlineOf
  have hallocated : ∀ candidate ∈ runtime.image.instructions,
      candidate.AllocatedAt rootState.initialFields.length := by
    apply ApplicationImage.instructions_allocated_withChoiceTimeouts
    apply ApplicationImage.instructions_allocated_withBindingTimeouts
    exact root.instructions_allocated deadlineOf
  have horiginsRuntime : runtime.image.HasBindingOrigins :=
    (horigins.withBindingTimeouts binding).withChoiceTimeouts choice
  let Witness := { pair :
    Option (L.Val spec.secretTy) × CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1 //
    (pair.1 = none ∨ pair.1 = some (current.current.source.get spec.binding)) ∧
      evalGuard guard (spec.encoding.symm pair.1)
        ((current.current.source.toView owner).eraseEnv) = true ∧
      pair.2.current.source =
        (current.current.source.cons (spec.encoding.symm pair.1)).cons
          (spec.encoding.symm pair.1) }
  let target : Witness → Config
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph := fun witness => witness.1.2.current.graph.1
  obtain ⟨witness, hfinalRefines, hfinalFresh, _, hfinalInactive⟩ :=
    runtime.runPolicies_complete_block_source_witness roster players instruction owner
      current.current.graph.1 blockIndex execution final activation Witness target
      (fun _ _ => True) hroster relay hrelay hlength hprincipal hindexBlock hindexRange
      (by rfl) hactive hactivation hkey
      checkpoint.refines checkpoint.consistent checkpoint.serialsBeforeNext
      (by
        intro polled included hpolledIndex hpolledSlot hpolledActive hpolledActivation
          hpolledRefines hincludedInactive hincluded
        exact runtime.environment_latest_source_witness players
          (runtime.blockEnvironment roster) owner polled included instruction.address Witness target
          (fun _ _ => True)
          (runtime.blockEnvironment_normal roster polled.environmentHistory
            (State.environmentView runtime.application polled.native) instruction hpolledIndex
            hpolledActive hpolledSlot |>.trans
              (by
                simp only [instruction, ApplicationImage.serviceCommand]
                have hownerCode : code.endpoint.owner = owner := rfl
                rw [hownerCode]))
          hpolledActive hincludedInactive (by
          intro message resolved hhandle
          obtain ⟨result, sourceNext, hresult, hlegal, hsource, hrefinesResolved⟩ :=
            runtime.handle_conditional_source_coupling guard tail spec fresh state sourceSlot
              deadline current publicGuard polled.native.application resolved
              activation instruction.address message hpolledActivation hkey hlookup
              hpolledRefines hhandle
          exact ⟨⟨(result, sourceNext), hresult, hlegal, hsource⟩,
            hrefinesResolved,
            runtime.handle_freshActivation polled.native.application resolved _ hhandle,
            trivial⟩) hincluded)
      (by
        intro included blockFinal hplayerIndex hplayerSlot henvironmentSlot hremainingIndex
          hincludedActive hincludedActivation hincludedRefines hincludedConsistent
          hincludedSerials hprefixSupport hafterIncluded
        obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp hrelay
        have hrosterSplit : (beforeRoster ++ relay :: afterRoster).Nodup := by rwa [← hsplit]
        have hrelayPolicy : players relay = runtime.blockPlayer relay
            (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile relay)) := hreference
        let before : List (@Invocation P) := [Invocation.environment] ++
          beforeRoster.flatMap fun actor => [Invocation.player actor, Invocation.environment]
        let suffix : List (@Invocation P) := afterRoster.flatMap fun actor =>
          [Invocation.player actor, Invocation.environment]
        have hrelayIndex : (beforeRoster ++ relay :: afterRoster)[beforeRoster.length]? =
            some relay := by simp
        have hrelayIndexRoster : roster[beforeRoster.length]? = some relay := by
          rw [hsplit]
          exact hrelayIndex
        have hsplitLength := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons] at hsplitLength
        have hincludedResolved := runtime.runPolicies_resolvedBindings
          rootState.initialFields.length hnodup hallocated players
          (runtime.blockEnvironment roster)
          ((roster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
            [Invocation.environment]) execution included checkpoint.resolvedBindings
              hprefixSupport
        apply runtime.runPolicies_relay_segment_inactive roster players relay
          (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile relay))
          hrelayPolicy instruction beforeRoster.length hrelayIndexRoster
          before suffix included
        · intro middle hmiddle index hlo hhi
          have henvironmentLength := runtime.application.runPolicies_environmentHistory_length
            players (runtime.blockEnvironment roster) before included middle hmiddle
          apply hremainingIndex index
          · simp only [before, List.countP_append, List.countP_cons, List.countP_nil,
              Invocation.isEnvironment, ↓reduceIte] at henvironmentLength
            omega
          · simp only [before, suffix, List.countP_append, List.countP_cons,
              List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
              Bool.false_eq_true] at hhi henvironmentLength ⊢
            rw [WindowedApplication.conditionalRelayPairs_environment_count]
              at hhi henvironmentLength
            omega
        · intro middle hmiddle hmiddleActive
          have hnotmem : relay ∉ beforeRoster := by
            intro hmem
            exact (List.nodup_append.mp hrosterSplit).2.2 relay hmem relay (by simp) rfl
          have hplayerLength := runtime.application.runPolicies_principalHistory_length relay
            players (runtime.blockEnvironment roster) before included middle hmiddle
          have henvironmentLength := runtime.application.runPolicies_environmentHistory_length
            players (runtime.blockEnvironment roster) before included middle hmiddle
          have hplayerUnchanged : (middle.principalHistory relay).length =
              (included.principalHistory relay).length := by
            rw [hplayerLength]
            simp only [before, List.countP_append, List.countP_cons, List.countP_nil,
              Bool.false_eq_true, ↓reduceIte, Nat.add_eq_left, Nat.zero_add]
            apply List.countP_eq_zero.mpr
            intro invocation hmem
            cases invocation with
            | environment => simp
            | player actor =>
                simp only [List.mem_flatMap] at hmem
                obtain ⟨candidate, hcandidate, hpair⟩ := hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
                rcases hpair with heq | hfalse
                · have hactor : actor = candidate := Invocation.player.inj heq
                  subst actor
                  intro heqRelay
                  have : candidate = relay := of_decide_eq_true heqRelay
                  exact hnotmem (this ▸ hcandidate)
                · simp at hfalse
          simp only [before, List.countP_append, List.countP_cons, List.countP_nil,
            Invocation.isEnvironment, ↓reduceIte] at henvironmentLength
          rw [WindowedApplication.conditionalRelayPairs_environment_count]
            at henvironmentLength
          obtain ⟨payload, resolved, hdue, hfresh, hhandle⟩ :=
            runtime.conditional_source_relay_eligibility_after_clock roster players guard tail
              spec fresh state sourceSlot deadline current instruction activation
              included middle
              (beforeRoster.flatMap fun actor =>
                [Invocation.player actor, Invocation.environment]) relay
              rootState.initialFields.length hnodup hallocated horiginsRuntime
              hincludedResolved (List.mem_of_getElem? hindexBlock) (by rfl)
              (by
                intro index hlo hhi
                apply hremainingIndex index hlo
                simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte] at hhi
                rw [WindowedApplication.conditionalRelayPairs_environment_count] at hhi
                omega)
              henvironmentSlot hincludedActive hincludedActivation hkey (by rwa [hkey])
              hincludedRefines hincludedConsistent hincludedSerials hmiddleActive
              (by simpa [before] using hmiddle)
          refine ⟨payload, resolved, ?_, ?_, ?_, ?_, hdue, hfresh, hhandle, ?_⟩
          · rwa [hplayerUnchanged]
          · rwa [hplayerUnchanged]
          · apply hremainingIndex middle.environmentHistory.length <;> omega
          · have hslot' : included.environmentHistory.length % (roster.length + 2) = 1 :=
              henvironmentSlot
            rw [henvironmentLength, Nat.add_mod, hslot']
            have hlt : 1 + beforeRoster.length < roster.length + 2 := by omega
            have hwhole : 1 + (1 + beforeRoster.length) < roster.length + 2 := by omega
            rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hwhole]
            omega
          · intro index hlo hhi
            apply hremainingIndex index
            · omega
            · simp only [suffix] at hhi ⊢
              rw [WindowedApplication.conditionalRelayPairs_environment_count] at hhi
              omega
        · simpa [before, suffix, hsplit, List.append_assoc] using hafterIncluded)
      (by
        intro actor index afterPlayer afterRelay hactor hrelayIndex hrelaySlot
          hplayerActive hplayerActivation hplayerRefines hafterInactive henvironment
        exact runtime.environment_latest_source_witness players
          (runtime.blockEnvironment roster) actor afterPlayer afterRelay instruction.address
          Witness target (fun _ _ => True)
          (by
          have hpolicy := runtime.blockEnvironment_relay roster
            afterPlayer.environmentHistory (State.environmentView runtime.application
              afterPlayer.native) instruction index actor hrelayIndex hplayerActive
              hrelaySlot hactor
          refine hpolicy.trans (congrArg FinDist.pure ?_)
          simp only [MessageApplication.latestSubmissionCommand,
            WindowedApplication.eraseEnvironmentView, MessageApplication.State.environmentView,
            WindowedApplication.application]
          cases hserial : afterPlayer.native.pool.nextSerial actor with
          | zero => rfl
          | succ serial =>
              simp only [WindowedApplication.liftEnvironmentCommand]
              split <;> rfl)
          hplayerActive hafterInactive (by
          intro message resolved hhandle
          obtain ⟨result, sourceNext, hresult, hlegal, hsource, hrefinesResolved⟩ :=
            runtime.handle_conditional_source_coupling guard tail spec fresh state sourceSlot
              deadline current publicGuard afterPlayer.native.application resolved activation
              instruction.address message hplayerActivation hkey hlookup hplayerRefines hhandle
          exact ⟨⟨(result, sourceNext), hresult, hlegal, hsource⟩,
            hrefinesResolved,
            runtime.handle_freshActivation afterPlayer.native.application resolved _ hhandle,
            trivial⟩) henvironment)
      (by intro witness before after schedule hcertificate hinactive hsupported _; trivial)
      hfinal
  exact ⟨witness.1.1, witness.1.2, witness.2.1, witness.2.2.1, witness.2.2.2,
    hfinalRefines, hfinalFresh, hfinalInactive⟩

/-- A complete ordinary conditional block constructs the genuine initialized
source successor checkpoint, retaining the optional opening result and its
actual adjacent source execution. -/
theorem conditional_block
    {pending : Finset VarId} {unresolved : spec.source ∈ pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (pending.erase spec.source) tail}
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex
        (.conditional (unresolved := unresolved) (newName := newName)
          (fresh := fresh) publicGuard nextPlan) profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hreference : root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement relay = root.windowedReferencePlayers rootProfile deadlineOf binding
        choice windowOf relay)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
        sourceNext.current.source =
          (current.current.source.cons (spec.encoding.symm result)).cons
            (spec.encoding.symm result) ∧
        evalGuard guard (spec.encoding.symm result)
          ((current.current.source.toView owner).eraseEnv) = true ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster focal
          replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
              |>.choice.publicationNode fresh state) := by
  let plan := ApplicationPlan.conditional (unresolved := unresolved) (newName := newName)
    (fresh := fresh) publicGuard nextPlan
  have hhead : plan.instructions deadlineOf =
      .conditional ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.code fresh state
          ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.sourceField fresh state)
          (deadlineOf ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.choice.publicationNode fresh state))) :: nextPlan.instructions deadlineOf := rfl
  obtain ⟨result, sourceNext, hresult, hlegal, hsource, hrefines, hfresh,
      hinactive⟩ := conditional_block_resolution_common publicGuard plan nextPlan profile
        hhead horigins current execution final checkpoint hroster relay hrelay hreference hfinal
  have hsteps := spec.commit_reveal_steps publicName tail current.current.source
    (spec.encoding.symm result) hlegal
  rw [← hsource] at hsteps
  refine ⟨result, sourceNext, hresult, hsource, hlegal, hsteps, ?_, hinactive⟩
  refine ⟨.conditional checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hfresh⟩
  · have hcount := checkpoint.blockCount
    rw [hhead, List.length_cons] at hcount
    omega
  · exact block_caches plan nextPlan profile deadlineOf _ hhead binding choice windowOf roster
      hroster focal replacement blockIndex current execution final checkpoint hfinal

/-- The copied-conditional accounting constructor has the same concrete block
semantics and constructs the same shape of source successor checkpoint. -/
theorem conditionalCopy_block
    {pending : Finset VarId} {unresolved : name ∈ insert name pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex
        (.conditionalCopy (newName := newName) (unresolved := unresolved)
          (fresh := fresh) spec publicGuard nextPlan) profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hreference : root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement relay = root.windowedReferencePlayers rootProfile deadlineOf binding
        choice windowOf relay)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
        sourceNext.current.source =
          (current.current.source.cons (spec.encoding.symm result)).cons
            (spec.encoding.symm result) ∧
        evalGuard guard (spec.encoding.symm result)
          ((current.current.source.toView owner).eraseEnv) = true ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster focal
          replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
              |>.choice.publicationNode fresh state) := by
  let plan := ApplicationPlan.conditionalCopy (newName := newName)
    (unresolved := unresolved) (fresh := fresh) spec publicGuard nextPlan
  have hhead : plan.instructions deadlineOf =
      .conditional ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.code fresh state
          ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.sourceField fresh state)
          (deadlineOf ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.choice.publicationNode fresh state))) :: nextPlan.instructions deadlineOf := rfl
  obtain ⟨result, sourceNext, hresult, hlegal, hsource, hrefines, hfresh,
      hinactive⟩ := conditional_block_resolution_common publicGuard plan nextPlan profile
        hhead horigins current execution final checkpoint hroster relay hrelay hreference hfinal
  have hsteps := spec.commit_reveal_steps publicName tail current.current.source
    (spec.encoding.symm result) hlegal
  rw [← hsource] at hsteps
  refine ⟨result, sourceNext, hresult, hsource, hlegal, hsteps, ?_, hinactive⟩
  refine ⟨.conditionalCopy checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hfresh⟩
  · have hcount := checkpoint.blockCount
    rw [hhead, List.length_cons] at hcount
    omega
  · exact block_caches plan nextPlan profile deadlineOf _ hhead binding choice windowOf roster
      hroster focal replacement blockIndex current execution final checkpoint hfinal

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_resolution_common'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_resolution_common

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditionalCopy_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditionalCopy_block
