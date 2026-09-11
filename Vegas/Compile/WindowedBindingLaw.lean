/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingReadiness

/-! # Exact complete-block law for unchanged binding owners

The source draw indexes a concrete native branch: private registration,
opaque-handle submission, and the rest of the fixed block service. This
factorization retains probabilities and arbitrary intervening raw commands.
Identifying the final frozen binding with this draw is a separate obligation.
-/

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
variable {windowOf : Nat → Nat} {roster : List P} {focal owner : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}

/-- Factor a complete binding block through its unchanged owner's source
kernel. Earlier polls remain inside the chosen-value branch; the equality
does not condition on acceptance, discard failed runs, or select witnesses. -/
theorem binding_block_source_factorization
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let environment := runtime.blockEnvironment roster
    let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
    let remaining :=
      (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
        [.environment, .environment] ++
          roster.flatMap fun actor => [.player actor, .environment]
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    let kernel := profile owner site ((current.current.source.toView owner).eraseEnv)
    runtime.application.runPolicies players environment
        (WindowedApplication.blockInvocations roster) execution =
      kernel.bind fun chosen =>
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.privateCommand (.register (site.compiledField fresh state) ⟨ty, chosen.1⟩))).bind
              fun registered =>
                (runtime.application.playerStep owner registered
                  (.submit (.binding
                    (site.bindingCode fresh state (site.compiledField fresh state)).node
                    (owner, site.compiledField fresh state)))).bind fun submitted =>
                      runtime.application.runPolicies players environment remaining submitted := by
  dsimp only
  let runtime := root.windowed deadlineOf binding choice windowOf
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let remaining :=
    (afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
      [Invocation.environment, .environment] ++
        roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hnotOwner : owner ∉ beforeRoster := by
    intro hmem
    have hparts := List.nodup_append.mp (hsplit ▸ hroster)
    exact hparts.2.2 owner hmem owner (by simp) rfl
  have hbeforeEnvironment : Invocation.environment ∉ before := by simp [before]
  have hbeforeOwner : Invocation.player owner ∉ before := by simp [before, hnotOwner]
  have hpolls := checkpoint.binding_polls_source_law_after_others hinitial hroster
    howner hother environment before hbeforeEnvironment hbeforeOwner
  have hschedule : WindowedApplication.blockInvocations roster =
      (before ++ [Invocation.player owner, .player owner]) ++ remaining := by
    simp only [WindowedApplication.blockInvocations, before, remaining, hsplit,
      List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hschedule, MessageApplication.runPolicies_append, hpolls]
  simp only [FinDist.bind_bind]
  rw [FinDist.bind_comm]

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_source_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_source_factorization
