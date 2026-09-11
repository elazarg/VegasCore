/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedConditionalReadiness

/-! # Exact complete-block law for unchanged conditional owners

Both conditional plan constructors have the same source-indexed native law.
The accepted binding disposition is an explicit input to the factorization;
it is not reconstructed from a supported output.
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
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}

/-- A complete conditional or conditional-copy block factors through the
unchanged owner's guarded source kernel. Each source value indexes the exact
submit/wait branch formed using the supplied accepted binding disposition. -/
theorem conditional_block_source_factorization
    (head : ConditionalHead spec plan)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
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
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    let kernel := profile owner site.choice.decision
      ((current.current.source.toView owner).eraseEnv)
    runtime.application.runPolicies players environment
        (WindowedApplication.blockInvocations roster) execution =
      kernel.bind fun chosen =>
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.submit (encoding.encode chosen.1))).bind fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment remaining waited := by
  dsimp only
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
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
  have hpolls := checkpoint.conditional_polls_source_law_after_others head hinitial horigins
    hroster howner hother disposition hbinding environment before hbeforeEnvironment hbeforeOwner
  have hschedule : WindowedApplication.blockInvocations roster =
      (before ++ [Invocation.player owner, .player owner]) ++ remaining := by
    simp only [WindowedApplication.blockInvocations, before, remaining, hsplit,
      List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hschedule, MessageApplication.runPolicies_append, hpolls]
  simp only [FinDist.bind_bind]
  rw [FinDist.bind_comm]

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_source_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_source_factorization
