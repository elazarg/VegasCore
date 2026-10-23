/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowResponseRepair
import Vegas.Pending.PhaseProposalShadowEnvironmentRepair
import Interaction.ReactiveOwnPlay

/-! # Initialized counted histories admit general designated-owner repairs -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A genuine counted history has a genuine initialized repaired history
under the same scheduler and original joint input law. Exclusions, canceled
attempts, old pending packets and truthful failed publications are retained.
The conclusion compares the complete external prefix, not a reduced view. -/
theorem repair_counted_history
    (bounds : MessageBounds graph) (covered : bounds.CoversOutputValues)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) (owner : Player)
    {state : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).State}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state)
    (control : (app).Control) (current : state = some control) :
    ∃ (memory : BindingShadow graph) (image : (app).Execution)
      (_imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨control.remaining, control.actor, image⟩)),
      memory.OwnBindings owner ∧
      (∀ slot, memory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame memory owner control.execution.application image.application ∧
      memory.CompletedAt image.application.current.native.config ∧
      phaseExternalObservation runtime leaks owner control.execution =
        phaseExternalObservation runtime leaks owner image ∧
      PreparedBindings runtime leaks owner control.execution image ∧
      control.execution.application.entry.native.config.store.BindingRefines
          image.application.entry.native.config.store ∧
      control.execution.application.current.native.config.store.BindingRefines
          image.application.current.native.config.store := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  induction trace generalizing control with
  | start => cases current
  | @extend before after prior joint legal realized ih =>
      subst current
      let afterTrace := prior.extend joint legal realized
      cases before with
      | none =>
          change some control ∈ (initial.map fun state =>
            some (⟨horizon, none, ReactiveApplication.Execution.initial app state⟩ :
              (app).Control)).support at realized
          obtain ⟨draw, _drawn, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          let physical := ReactiveApplication.Execution.initial app draw
          refine ⟨empty, physical, afterTrace, ownBindings_empty owner,
            empty_candidates_not_fresh, ?_, completedAt_empty _, rfl,
            preparedBindings_initial runtime leaks owner draw draw,
            Store.BindingRefines.refl _, Store.BindingRefines.refl _⟩
          exact ⟨rfl, rfl, (recovery_empty owner _).symm, (recovery_empty owner _).symm, rfl⟩
      | some before =>
          obtain ⟨memory, image, imageTrace, owned, valid, paired, supported, external,
              prepared, entryRef, currentRef⟩ := ih before rfl
          rcases before with ⟨remaining, actor, original⟩
          have network : original.network = image.network := congrArg Prod.fst external
          have receipts : original.receipts = image.receipts :=
            congrArg (fun observation => observation.2.1) external
          have service : original.environmentRecall = image.environmentRecall :=
            congrArg (fun observation => observation.2.2.1) external
          have recalled (who : Player) (different : who ≠ owner) :
              original.recall who = image.recall who := by
            have observed := congrFun (congrArg (fun observation => observation.2.2.2.2)
              external) who
            change (if who = owner then none else
              some (original.recall who, original.observe app who)) =
                (if who = owner then none else
                  some (image.recall who, image.observe app who)) at observed
            simp only [ite_eq_right different] at observed
            exact congrArg Prod.fst (Option.some.inj observed)
          cases actor with
          | some actor =>
              have available := legal.2 actor
              cases responseEq : joint actor with
              | none =>
                  rw [responseEq] at available
                  exact False.elim (available rfl)
              | some response =>
                  rw [responseEq] at available
                  let sourceJoint : Player → Option (app).Action :=
                    fun who => if who = actor then some response else none
                  have jointEq : joint = sourceJoint := by
                    funext who
                    by_cases same : who = actor
                    · subst who
                      simpa only [sourceJoint, ↓reduceIte] using responseEq
                    · have inactive : joint who = none := LegalOption.eq_none_of_inactive _
                        ((menu.protocol initial horizon scheduler).legalOption_of_legal legal who)
                        (by simp [ReactiveApplication.ResponseMenu.protocol,
                          ReactiveApplication.actor, Ne.symm same])
                      simpa only [sourceJoint, same, ↓reduceIte] using inactive
                  subst joint
                  change some control ∈ (PMF.pure (some
                    (⟨remaining, none, original.respond app actor
                      ((sourceJoint actor).getD ⟨none⟩)⟩ : (app).Control))).support at realized
                  simp only [sourceJoint, ↓reduceIte, Option.getD_some,
                    PMF.mem_support_pure_iff] at realized
                  cases Option.some.inj realized
                  obtain ⟨target, nextMemory, targetLegal, _actionEq, nextOwned, nextValid,
                      nextFrame, nextSupport, _nextNetwork, nextExternal, nextPrepared,
                      nextEntryRef, nextCurrentRef⟩ :=
                    response_repair runtime leaks memory owner owned valid original image paired
                      supported network receipts service recalled prepared entryRef currentRef
                        bounds covered plan ordered inputs horizon scheduler remaining actor prior
                          imageTrace response available.2
                  obtain ⟨targetTrace⟩ := menu.trace_respond initial horizon scheduler remaining
                    image actor target imageTrace targetLegal
                  exact ⟨nextMemory, image.respond app actor target, targetTrace, nextOwned,
                    nextValid, nextFrame, nextSupport, nextExternal, nextPrepared, nextEntryRef,
                    nextCurrentRef⟩
          | none =>
              cases remaining with
              | zero => exact False.elim (legal.1 ⟨rfl, rfl⟩)
              | succ remaining =>
                  change some control ∈ ((scheduler original.environmentRecall
                    (original.observeEnvironment app)).bind _).support at realized
                  obtain ⟨command, selected, drawn⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                  obtain ⟨next, moved, same⟩ := PMF.support_map .. ▸ drawn
                  cases Option.some.inj same
                  obtain ⟨nextMemory, target, _targetMoved, ⟨targetTrace⟩, nextOwned, nextValid,
                      nextFrame, nextSupport, _nextNetwork, nextExternal, nextPrepared,
                      nextEntryRef, nextCurrentRef⟩ :=
                    environment_repair runtime leaks bounds plan inputs horizon scheduler remaining
                      original image prior imageTrace memory owner paired owned valid supported
                        network receipts service recalled prepared entryRef currentRef command
                          selected next moved
                  exact ⟨nextMemory, target, targetTrace, nextOwned, nextValid, nextFrame,
                    nextSupport, nextExternal, nextPrepared, nextEntryRef, nextCurrentRef⟩

/-- The actual repair retains the entire immutable input draw and every
other owner's complete own-play word. No behavioral profile, product prior
or equality of the designated owner's private recall is assumed. -/
theorem repair_counted_history_ownPlay
    (bounds : MessageBounds graph) (covered : bounds.CoversOutputValues)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) (owner : Player)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    ∃ (memory : BindingShadow graph) (image : (app).Execution)
      (imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨control.remaining, control.actor, image⟩)),
      PhaseStateFrame memory owner control.execution.application image.application ∧
      PreparedBindings runtime leaks owner control.execution image ∧
      phaseExternalObservation runtime leaks owner control.execution =
        phaseExternalObservation runtime leaks owner image ∧
      control.execution.application.current.native.config.inputs =
        image.application.current.native.config.inputs ∧
      ∀ who, who ≠ owner →
        ((PhaseCount.onePacketMenu runtime leaks bounds).information
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).ownPlay who trace =
        ((PhaseCount.onePacketMenu runtime leaks bounds).information
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).ownPlay who
            imageTrace := by
  obtain ⟨memory, image, imageTrace, _owned, _valid, paired, _supported, external, prepared,
      _entryRef, _currentRef⟩ := repair_counted_history runtime leaks bounds covered plan ordered
        inputs horizon scheduler owner trace control rfl
  refine ⟨memory, image, imageTrace, paired, prepared, external, ?_, ?_⟩
  · rw [paired.current]
    rfl
  · intro who different
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let initial := inputs.map (PhaseRuntimeState.initial plan)
    have word (current : (app).Control)
        (history : (menu.protocol initial horizon scheduler).Trace (some current)) :
        (menu.information initial horizon scheduler).ownPlay who history =
          (app).recallOwnPlay (current.execution.recall who) := by
      change (menu.signals initial horizon scheduler).ownPlay who history = _
      rw [← menu.ownPlay_toRawTrace initial horizon scheduler who history,
        (app).trace_ownPlay]
      rfl
    have observed := congrFun (congrArg (fun observation => observation.2.2.2.2) external) who
    change (if who = owner then none else
      some (control.execution.recall who, control.execution.observe app who)) =
        (if who = owner then none else some (image.recall who, image.observe app who)) at observed
    simp only [ite_eq_right different] at observed
    have recalled : control.execution.recall who = image.recall who :=
      congrArg Prod.fst (Option.some.inj observed)
    rw [word control trace, word _ imageTrace]
    exact congrArg (app).recallOwnPlay recalled

end Vegas.EventGraphRuntime.BindingShadow
