/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceRestriction

/-! # Original source kernels at native registration points

The reference law below retains the original source profile and fixes exactly
the occupied selected-owner slots. Every registered value then agrees with the
ordinary source realization. At a compatible timeout-free native snapshot,
the compiled policy uses that realization's original source kernel. These
are the source-side facts for the all-compiled probability law, with no focal
policy replacement and no independence assumption on source choices.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}
variable (compilation : SealedCompilation source ty)

/-- A selected occupied registration is retained by every realization of the
restricted original source profile. All unselected or unoccupied decisions
still use their original source kernels. -/
theorem sourceRealization_registered (selected : Player → Bool)
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) (fallback : L.Val ty)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (source.sourceRealization
      ((compilation.recordedChoiceRestriction selected service.lookup).apply profile)).support)
    (who : Player) (hselected : selected who = true)
    (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
    (value : L.Val ty) (hlookup : service.lookup (who, node.val) = some value) :
    cfg.1.nodeValues fallback node = value := by
  have hterminal := source.sourceRealization_terminal _ cfg hcfg
  have hchoices := runPolicyNodes_support_commitValues (compile source.core).graphWF
    (compile_guardLive source.core source.legal) _ _ (CommitValuesSupported.initial _)
    (compile source.core).graph.nodeOrder cfg hcfg
  obtain ⟨reads, _, choice, hchoice, hvalue⟩ := hchoices node (hterminal node) who guard hsem
  change choice ∈
    (compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      _ who ((compilation.recordedChoiceRestriction selected service.lookup).apply profile who)
      node guard hsem reads).support at hchoice
  rw [compilation.compile_recordedChoiceRestriction selected service.lookup profile who node guard
    hsem reads, if_pos hselected, hlookup] at hchoice
  simp only [SealedFragment.valuePolicy, FinDist.mem_support_pure] at hchoice
  subst choice
  change cfg.1.store ((compile source.core).graph.nodeTarget node) =
    some (⟨guard.ty, cast (congrArg L.Val
      (compilation.supported.commitType node who guard hsem).symm) value⟩ : TypedValue L) at hvalue
  rw [Config.nodeValues, Store.getAs, hvalue]
  simp only [TypedValue.as?, dif_pos (compilation.supported.commitType node who guard hsem),
    cast_cast, cast_eq, Option.getD_some]

variable [DecidableEq (L.Val ty)]

omit [Fintype Player] in
/-- Every queried registration probability is the original source decision
probability at the retained terminal environment's declared view. The snapshot
can come from any native execution whose occupied source slots agree with that
environment. Zero-probability queried values are included. -/
theorem registration_source_probability
    (nullValue : L.Val ty) (window : Nat) (fallback : L.Val ty)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1)
    (execution :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hclear : execution.native.application.visible.timeouts = [])
    (hmemory : SealedResolution.RegistrationMemory
      (compilation.supported.resolvingRuntime nullValue window) execution)
    (hvalid : SealedProgram.BindingInvariant compilation.program
      ⟨execution.native.application.service, execution.native.pool,
        execution.native.application.visible.events⟩)
    (hvalues : ∀ owner (node : Fin (compile source.core).graph.nodeCount) guard,
      ((compile source.core).graph.nodeRow node).sem = .commit owner guard → ∀ value,
        execution.native.application.service.lookup (owner, node.val) = some value →
          cfg.1.nodeValues fallback node = value)
    (who : Player) (reference : CommitPolicy (compile source.core).graph who)
    (policy : SourceBehavioralPolicy source.core.prog who) (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈
      (compilation.supported.resolvingPolicy nullValue window who reference
        (execution.principalHistory who)
        (State.observe _ execution.native who)).support) :
    ∃ final, observeSourceOutcome source.core cfg = some final ∧
      ∃ Δ name choiceTy guard, ∃ site :
        SourceDecisionSite who source.core.prog Δ name choiceTy guard,
        site.depth = slot ∧ ∀ chosen,
          (compilation.compileResolvingPolicy nullValue window who policy
            (execution.principalHistory who)
            (State.observe _ execution.native who)).prob (.privateCommand ⟨(slot, chosen)⟩) =
          ((policy site ((site.recorded final).tail.toView who).eraseEnv).map
            (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))).prob ⟨ty, chosen⟩ := by
  obtain ⟨node, guard, hsem, reads, hslot, _, hreads, hkernel⟩ :=
    compilation.supported.resolving_registration_kernel cfg hterminal fallback nullValue window
      execution hclear hmemory hvalid hvalues who reference
      (compileSourcePolicy source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        rfl who policy) slot value hcommand
  obtain ⟨Δ, name, choiceTy, sourceGuard, site, hdepth, hlaw⟩ :=
    compileSourcePolicy_recorded_law source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who policy node guard hsem cfg hterminal reads hreads
  refine ⟨_, observeSourceOutcome_of_terminal source.core cfg hterminal,
    Δ, name, choiceTy, sourceGuard, site, hdepth.trans hslot.symm, ?_⟩
  intro chosen
  change (compilation.supported.resolvingPolicy nullValue window who _ _ _).prob _ = _
  rw [hkernel, ← hlaw]
  rw [FinDist.prob_map_eq_probOf_preimage_singleton,
    FinDist.prob_map_eq_probOf_preimage_singleton]
  apply FinDist.probOf_congr
  intro choice _
  have htyped {left right : L.Ty} (heq : left = right)
      (selected : L.Val left) (queried : L.Val right) :
      (⟨left, selected⟩ : TypedValue L) = ⟨right, queried⟩ ↔
        cast (congrArg L.Val heq) selected = queried := by
    cases heq
    simp only [TypedValue.mk.injEq, heq_eq_eq, true_and, cast_eq]
  simp only [Set.mem_preimage, Set.mem_singleton_iff,
    MessageInterface.PlayerCommand.privateCommand.injEq, ← hslot,
    htyped (compilation.supported.commitType node who guard hsem)]
  constructor
  · exact fun h => congrArg (fun request => request.down.2) h
  · intro h
    rw [h]

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.sourceRealization_registered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.sourceRealization_registered

/-- info: 'Vegas.SealedCompilation.registration_source_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.registration_source_probability
