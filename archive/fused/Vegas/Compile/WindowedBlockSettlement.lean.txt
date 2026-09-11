/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockResolution
import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.WindowedRelayResolution
import Vegas.Compile.BindingSourceCoupling
import Vegas.Compile.ApplicationBindingDefault
import Vegas.Compile.BindingTimeoutCompilation

/-! # Source-ready eligibility and windowed block settlement -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- No successful handler can preserve the formerly active address. This is
the contradiction used to show that an as-yet-unsettled relay prefix only
stutters at rejected inclusions. -/
theorem handle_eq_none_of_active_preserved (runtime : WindowedApplication P L)
    (before after : WindowedApplication.State P L)
    (message : Message P (ApplicationImage.Payload P L)) (address : Nat)
    (hbefore : runtime.image.activeAddress? before.base.memory = some address)
    (hafter : runtime.image.activeAddress? after.base.memory = some address) :
    runtime.handle before message ≠ some after := by
  intro hhandle
  obtain ⟨resolved, hactive, _, hinactive⟩ :=
    runtime.handle_resolves_active before after message hhandle
  have heq : resolved = address := Option.some.inj (hactive.symm.trans hbefore)
  exact hinactive (heq ▸ hafter)

/-- The aligned second environment slot performs exactly the block's strict
post-window clock advance. -/
theorem block_clock_step (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 1)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address) :
    ∃ next, runtime.application.runPolicies players (runtime.blockEnvironment roster)
      [.environment] execution = FinDist.pure next ∧
      next.native.application.base.memory.clock =
        max execution.native.application.base.memory.clock
          (activation.since + runtime.windowOf instruction.address + 1) := by
  have hpolicy := runtime.blockEnvironment_advance roster execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native)
    instruction activation hindex hactive hslot hactivation hkey
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hpolicy,
    FinDist.pure_bind, MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step, application_advance, FinDist.map_pure]
  refine ⟨_, rfl, ?_⟩
  simp [ApplicationImage.State.advance]

/-- The binding form's source-certified timeout facts instantiate the local
eligibility needed by an unchanged block relay. -/
theorem binding_relay_eligibility (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution) (who : P)
    (activation : Activation Nat)
    (hstate : runtime.Consistent execution.native.application)
    (hactive : execution.native.application.active = some activation)
    (code : BindingCode P L)
    (hcode : runtime.image.lookup activation.key = some (.bind code))
    (timeout : PublicFallbackCode L code.ty) (htimeout : code.timeout = some timeout)
    (hunbound : execution.native.application.base.memory.accepted code.sourceField = none)
    (hnotDone : execution.native.application.base.memory.done code.node = false)
    (hrequires : code.requires.all execution.native.application.base.memory.done = true)
    (hoverdue : activation.since + runtime.windowOf activation.key <
      execution.native.application.base.memory.clock)
    (value : L.Val code.ty)
    (hvalue : timeout.value.evalStore? execution.native.application.base.memory.store =
      some value)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none) :
    ∃ payload next,
      runtime.dueExpiry?
        (execution.native.application.base.memory, execution.native.application.active) =
          some payload ∧
      execution.native.pool.lookup (who, execution.native.pool.nextSerial who) = none ∧
      runtime.handle execution.native.application
        ⟨(who, execution.native.pool.nextSerial who), payload⟩ = some next := by
  refine ⟨.expireBinding activation.key,
    runtime.advanceTo execution.native.application
      (execution.native.application.base.defaultBind code ⟨code.ty, value⟩), ?_, hfresh, ?_⟩
  · exact runtime.dueExpiry?_of_binding execution.native.application activation hstate hactive
      code hcode timeout htimeout hoverdue
  · exact runtime.handle_expireBinding_after_window execution.native.application activation
      hstate hactive code hcode timeout htimeout hunbound hnotDone hrequires hoverdue value
      hvalue _

/-- At a ready source binding checkpoint, a legal public fallback supplies the
complete concrete relay certificate and the matching source successor. -/
theorem binding_source_relay_eligibility
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (execution : runtime.application.PolicyExecution) (activation : Activation Nat) (relay : P)
    (hstate : runtime.Consistent execution.native.application)
    (hactive : execution.native.application.active = some activation)
    (hcode : runtime.image.lookup activation.key = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hoverdue : activation.since + runtime.windowOf activation.key <
      execution.native.application.base.memory.clock)
    (hfresh : execution.native.pool.lookup
      (relay, execution.native.pool.nextSerial relay) = none) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ payload resolved,
      runtime.dueExpiry?
        (execution.native.application.base.memory, execution.native.application.active) =
          some payload ∧
      execution.native.pool.lookup (relay, execution.native.pool.nextSerial relay) = none ∧
      runtime.handle execution.native.application
        ⟨(relay, execution.native.pool.nextSerial relay), payload⟩ = some resolved ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard tail) fresh build).graph
          (build.addCommitEvent name who guard fresh.1).1,
        next.current.source = current.current.source.cons chosen ∧
        resolved.base.Refines next.current.graph.1 := by
  dsimp only
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let code := fallback.bindingTimeoutCode fresh build deadline
  let chosen := L.eval fallback.expr current.current.source.erasePubEnv
  have hready := SourceDecisionSite.binding_ready_at_source_prefix guard tail fresh build current
    execution.native.application.base.memory.done hrefines.memory.completed
  have hunbound : execution.native.application.base.memory.accepted code.sourceField = none :=
    hrefines.accepted_eq_none_of_not_done (site.compiledNode fresh build) hready.1.1
  obtain ⟨hvalue, next, hsource, hnext⟩ := fallback.defaultBind_source_coupling
    guard tail fresh build current execution.native.application.base hrefines
  let resolved := runtime.advanceTo execution.native.application
    (execution.native.application.base.defaultBind code ⟨ty, chosen⟩)
  refine ⟨.expireBinding activation.key, resolved, ?_, hfresh, ?_, next, hsource, hnext⟩
  · exact runtime.dueExpiry?_of_binding execution.native.application activation hstate hactive
      code hcode ⟨deadline, fallback.compiled fresh build⟩ rfl hoverdue
  · exact runtime.handle_expireBinding_after_window execution.native.application activation
      hstate hactive code hcode ⟨deadline, fallback.compiled fresh build⟩ rfl
      hunbound hready.2.1 hready.2.2 hoverdue chosen hvalue
      (relay, execution.native.pool.nextSerial relay)

/-- An arbitrary supported relay prefix settles at an unchanged relay whenever
the still-active state has a certified due message and accepting handler. If an
earlier relay already resolved the instruction, the whole remainder is gated
and preserves that inactive checkpoint. -/
theorem runPolicies_relay_segment_inactive
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (base : runtime.application.PlayerPolicy)
    (hrelay : players who = runtime.blockPlayer who base)
    (instruction : ApplicationInstruction P L) (rosterIndex : Nat)
    (hwho : roster[rosterIndex]? = some who)
    (before suffix : List (@Invocation P))
    (execution : runtime.application.PolicyExecution)
    (hinactiveIndex : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      ∀ index, middle.environmentHistory.length ≤ index →
      index < middle.environmentHistory.length +
        (([Invocation.player who, Invocation.environment] ++ suffix).countP
          Invocation.isEnvironment) →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (heligible : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      runtime.image.activeAddress? middle.native.application.base.memory =
        some instruction.address →
      ∃ payload next,
        runtime.image.instructions[(middle.principalHistory who).length / 3]? =
          some instruction ∧
        (middle.principalHistory who).length % 3 = 2 ∧
        runtime.image.instructions[middle.environmentHistory.length /
          (roster.length + 2)]? = some instruction ∧
        middle.environmentHistory.length % (roster.length + 2) = rosterIndex + 2 ∧
        runtime.dueExpiry?
          (middle.native.application.base.memory, middle.native.application.active) =
            some payload ∧
        middle.native.pool.lookup (who, middle.native.pool.nextSerial who) = none ∧
        runtime.handle middle.native.application
          ⟨(who, middle.native.pool.nextSerial who), payload⟩ = some next ∧
        ∀ index, middle.environmentHistory.length + 1 ≤ index →
          index < middle.environmentHistory.length + 1 +
            suffix.countP Invocation.isEnvironment →
          runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster)
      (before ++ [.player who, .environment] ++ suffix) execution).support) :
    runtime.image.activeAddress? final.native.application.base.memory ≠
      some instruction.address := by
  rw [List.append_assoc, MessageApplication.runPolicies_append] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨middle, hmiddle, hrest⟩ := hfinal
  by_cases hactive : runtime.image.activeAddress? middle.native.application.base.memory =
      some instruction.address
  · obtain ⟨payload, next, hplayerIndex, hplayerSlot, henvironmentIndex,
        henvironmentSlot, hdue, hfresh, hhandle, hsuffixIndex⟩ :=
      heligible middle hmiddle hactive
    have hrelayLaw := runtime.block_relay_accepts roster players who base hrelay
      middle instruction rosterIndex hplayerIndex hplayerSlot henvironmentIndex
      henvironmentSlot hwho hactive payload next hdue hfresh hhandle
    have hrelayInactive : runtime.image.activeAddress? next.base.memory ≠
        some instruction.address := by
      obtain ⟨address, hbefore, _, hinactive⟩ := runtime.handle_resolves_active
        middle.native.application next
        ⟨(who, middle.native.pool.nextSerial who), payload⟩ hhandle
      have haddress : address = instruction.address :=
        Option.some.inj (hbefore.symm.trans hactive)
      rwa [haddress] at hinactive
    rw [MessageApplication.runPolicies_append] at hrest
    simp only [FinDist.support_bind, Set.mem_iUnion] at hrest
    obtain ⟨afterRelay, hafterRelay, hafterSuffix⟩ := hrest
    have happlication : afterRelay.native.application = next := by
      have hmapped : (afterRelay.native.application, afterRelay.native.pool.ledger,
          afterRelay.native.receipts) ∈
          ((runtime.application.runPolicies players (runtime.blockEnvironment roster)
            [.player who, .environment] middle).map
              (fun out => (out.native.application, out.native.pool.ledger,
                out.native.receipts))).support := by
        rw [FinDist.support_map]
        exact ⟨afterRelay, hafterRelay, rfl⟩
      rw [hrelayLaw, FinDist.mem_support_pure] at hmapped
      exact congrArg Prod.fst hmapped
    have hlength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) [.player who, .environment] middle afterRelay
      hafterRelay
    have hstutter := runtime.runPolicies_block_inactive roster players suffix afterRelay final
      instruction (by
        intro index hlo hhi
        apply hsuffixIndex index <;>
          simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
            Bool.false_eq_true, ↓reduceIte] at hlength <;> omega) (by
        rw [happlication]
        exact hrelayInactive) hafterSuffix
    have hmemory : final.native.application.base.memory = next.base.memory := by
      exact (congrArg Prod.fst hstutter).trans (by rw [happlication])
    rwa [hmemory]
  · have hstutter := runtime.runPolicies_block_inactive roster players
      ([.player who, .environment] ++ suffix) middle final instruction
      (hinactiveIndex middle hmiddle) hactive hrest
    have hmemory : final.native.application.base.memory =
        middle.native.application.base.memory := congrArg Prod.fst hstutter
    rwa [hmemory]

/-- One unchanged aligned relay pair makes concrete progress whenever the
certified expiry is due and its form-specific handler accepts. Every supported
outcome has the accepted application state, which has resolved the formerly
active instruction. -/
theorem block_relay_resolves_active (runtime : WindowedApplication P L)
    (roster : List P) (players : P → runtime.application.PlayerPolicy) (who : P)
    (base : runtime.application.PlayerPolicy)
    (hrelay : players who = runtime.blockPlayer who base)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (index : Nat)
    (hplayerIndex : runtime.image.instructions[(execution.principalHistory who).length /
      3]? = some instruction)
    (hplayerSlot : (execution.principalHistory who).length % 3 = 2)
    (henvironmentIndex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (henvironmentSlot : execution.environmentHistory.length %
      (roster.length + 2) = index + 2)
    (hwho : roster[index]? = some who)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (payload : ApplicationImage.Payload P L) (next : WindowedApplication.State P L)
    (hdue : runtime.dueExpiry?
      (execution.native.application.base.memory, execution.native.application.active) =
        some payload)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hhandle : runtime.handle execution.native.application
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ = some next) :
    (runtime.application.runPolicies players (runtime.blockEnvironment roster)
      [.player who, .environment] execution).map
        (fun out => out.native.application) = FinDist.pure next ∧
      runtime.image.activeAddress? next.base.memory ≠ some instruction.address := by
  have hlaw := runtime.block_relay_accepts roster players who base hrelay execution
    instruction index hplayerIndex hplayerSlot henvironmentIndex henvironmentSlot hwho
    hactive payload next hdue hfresh hhandle
  constructor
  · simpa only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] using congrArg
      (FinDist.map fun result => result.1) hlaw
  · obtain ⟨address, hbefore, _, hinactive⟩ := runtime.handle_resolves_active
      execution.native.application next
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ hhandle
    have haddress : address = instruction.address :=
      Option.some.inj (hbefore.symm.trans hactive)
    rwa [haddress] at hinactive

/-- Once a prefix resolves the current instruction to a fixed application
state, every aligned remainder of that gated block preserves its public
checkpoint. The complete execution may still change histories, traffic, and
private preparation. -/
theorem runPolicies_resolved_prefix_suffix_publicState
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (before suffix : List (@Invocation P))
    (execution : runtime.application.PolicyExecution)
    (resolved : WindowedApplication.State P L)
    (instruction : ApplicationInstruction P L)
    (hprefix : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      middle.native.application = resolved)
    (hinactive : runtime.image.activeAddress? resolved.base.memory ≠
      some instruction.address)
    (hindex : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      ∀ index, middle.environmentHistory.length ≤ index →
      index < middle.environmentHistory.length + suffix.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (before ++ suffix) execution).support) :
    (final.native.application.base.memory, final.native.application.active) =
      (resolved.base.memory, resolved.active) := by
  simp only [MessageApplication.runPolicies_append, FinDist.support_bind,
    Set.mem_iUnion] at hfinal
  obtain ⟨middle, hmiddle, hfinal⟩ := hfinal
  have hresolved := hprefix middle hmiddle
  have hstutter := runtime.runPolicies_block_inactive roster players suffix middle final
    instruction (hindex middle hmiddle) (by rwa [hresolved]) hfinal
  exact hstutter.trans (by rw [hresolved])

/-- A successful actual handler call supplies the inactivity premise for the
formerly active instruction, uniformly across ordinary and expiry handlers. -/
theorem handle_resolved_prefix_suffix_publicState
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (before suffix : List (@Invocation P))
    (execution : runtime.application.PolicyExecution)
    (priorState resolved : WindowedApplication.State P L)
    (message : Message P (ApplicationImage.Payload P L))
    (instruction : ApplicationInstruction P L)
    (hactive : runtime.image.activeAddress? priorState.base.memory = some instruction.address)
    (hhandle : runtime.handle priorState message = some resolved)
    (hprefix : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      middle.native.application = resolved)
    (hindex : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      ∀ index, middle.environmentHistory.length ≤ index →
      index < middle.environmentHistory.length + suffix.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (before ++ suffix) execution).support) :
    (final.native.application.base.memory, final.native.application.active) =
      (resolved.base.memory, resolved.active) := by
  obtain ⟨address, hbefore, _, hinactive⟩ :=
    runtime.handle_resolves_active priorState resolved message hhandle
  have haddress : address = instruction.address := Option.some.inj (hbefore.symm.trans hactive)
  subst address
  exact runtime.runPolicies_resolved_prefix_suffix_publicState roster players before suffix
    execution resolved instruction hprefix hinactive hindex final hfinal

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_resolved_prefix_suffix_publicState'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_resolved_prefix_suffix_publicState
