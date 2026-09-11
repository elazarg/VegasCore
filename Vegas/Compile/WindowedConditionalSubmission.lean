/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedConditionalReadiness
import Interaction.MessageApplicationSampleOnce

/-! # Source-supported conditional packets under ordinary polling -/

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
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {current : CoupledAt
  (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
    fresh state).graph state}
variable {execution :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- The unchanged conditional owner leaves exactly one fresh packet carrying
a draw from its actual source kernel. Both opaque commitments and public
defaults use their disposition-specific encoding. -/
theorem conditional_ordinary_submission
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (head : ConditionalHead spec plan)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (polled : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hpolled : polled ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution).support) :
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    ∃ chosen ∈ (profile owner site.choice.decision
        ((current.current.source.toView owner).eraseEnv)).support,
      polled.native.pool.nextSerial owner = execution.native.pool.nextSerial owner + 1 ∧
      polled.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
        some ⟨(owner, execution.native.pool.nextSerial owner),
          .conditional (site.choice.publicationNode fresh state)
            (site.sourceRequestPayload fresh state (site.sourceField fresh state)
              (deadlineOf (site.choice.publicationNode fresh state)) disposition
              (spec.encoding chosen.1))⟩ := by
  intro site
  obtain ⟨beforeRoster, afterRoster, rfl⟩ := List.mem_iff_append.mp howner
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment (beforeRoster ++ owner :: afterRoster)
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let after := afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state)) disposition
    (ApplicationImage.conditionalTransport spec.secretTy)
  have hbeforeOwner : owner ∉ beforeRoster := by
    intro hmem
    exact (List.nodup_append.mp hroster).2.2 owner hmem owner (by simp) rfl
  have hafterOwner : owner ∉ afterRoster :=
    (List.nodup_cons.mp (List.nodup_append.mp hroster).2.1).1
  have hbefore : Invocation.player owner ∉ before := by simp [before, hbeforeOwner]
  have hafter : Invocation.player owner ∉ after := by simp [after, hafterOwner]
  have hdecompose :
      (beforeRoster ++ owner :: afterRoster).flatMap
        (fun actor => [Invocation.player actor, Invocation.player actor]) =
      (before ++ [.player owner, .player owner]) ++ after := by
    simp only [before, after, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hdecompose] at hpolled
  have hpacket := runtime.application.runPolicies_submit_wait_packet owner players environment
    before after (by simp [before]) hbefore (by simp [after]) hafter execution polled
    checkpoint.serialsBeforeNext
    (profile owner site.choice.decision ((current.current.source.toView owner).eraseEnv))
    (fun chosen => encoding.encode chosen.1)
    (checkpoint.conditional_polls_source_law_after_others head hinitial horigins hroster
      (by simp) hother disposition hbinding environment before (by simp [before]) hbefore)
    hpolled
  obtain ⟨chosen, hchosen, hserial, hlookup⟩ := hpacket
  refine ⟨chosen, hchosen, hserial, ?_⟩
  have hencode := site.choiceEncodingFor_encode fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state)) disposition chosen.1
  change encoding.encode chosen.1 = _ at hencode
  rw [hencode] at hlookup
  exact hlookup

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_submission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_submission
