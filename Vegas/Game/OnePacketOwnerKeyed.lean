/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketConditionalPrior
import Vegas.Game.OnePacketKeyedScaling
import Vegas.Game.OnePacketSwapBaseWeight
import Vegas.Game.OnePacketSwapInfo

/-! # Agreeing base laws at two sites with one late key

Take two decision sites of `who` with the same late-delivery key, at neither
of which `who` owes a failure, in a well-formed setup whose hidden initial
cells are independent given an observed public initial signal. Private
splicing must preserve that signal, and all public initial inputs must
determine it. The owner swap between the two sites' views is guarded at both
sites, moves values within the bounds, keeps regularity, and multiplies the
others' source weight of every history of the first site by a common positive
ratio; when it also sends the first site's information state to the second's,
the base laws of the two sites agree on every payoff of the operational record
(`Vegas.ownerSwap_baseLawAgrees`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Alone, every history is regular**: regularity constrains only the
responses of other players. -/
theorem regularTrace_of_alone (assessment : setup.intendedModel.BehavioralAssessment)
    {who : Player} (alone : ∀ player, player = who) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
      RegularTrace setup leaks bounds horizon scheduler assessment who trace
  | _, .start => trivial
  | _, .extend (source := before) (target := after) prior _ _ _ =>
      ⟨regularTrace_of_alone assessment alone prior, by
        cases before with
        | none => trivial
        | some _ =>
            cases after with
            | none => trivial
            | some _ => exact fun actor _ different => (different (alone actor)).elim⟩

/-- **Agreeing base laws at two sites with one late key.** -/
theorem ownerSwap_baseLawAgrees
    {Public : Type*} (signal : State L setup.context → Public)
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (preserves : ∀ (owner : Player) (mine others : State L setup.context),
      signal (splice owner mine others) = signal others)
    (observable : ∀ (first second : State L setup.context),
      (∀ input, (graph setup).fieldPublic (.inl input) →
        setup.eventInputs first input = setup.eventInputs second input) →
      signal first = signal second)
    (covers : bounds.CoversInputValues)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (weight : List (Option (OperationalState setup leaks)) → ℝ) {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup leaks who site₁.1 = lateKey setup leaks who site₂.1)
    (firstDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₁.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (secondDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₂.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (infoEq : (ownerSwap who view₁.application view₂.application).info site₁.1 = site₂.1)
    (payoff : List (Option (OperationalState setup leaks)) → ℝ) :
    BaseLawAgrees
      (fun history => othersSourceWeight setup leaks bounds horizon scheduler assessment who
        history.trace * weight (operationalRecord setup leaks bounds horizon scheduler
          history.trace))
      (fun history => RegularTrace setup leaks bounds horizon scheduler assessment who
        history.trace) site₁ site₂ payoff := by
  set swap := ownerSwap who view₁.application view₂.application with swapEq
  have bounded := ownerSwap_bounded_sites covers firstSite secondSite
  have fixesOthers : ∀ other, other ≠ who → swap.Fixes other := fun other different =>
    ownerSwap_fixes who _ _ different
  have guardedFirst := ownerSwap_guard firstSite secondSite sameKey firstDebtFree secondDebtFree
    (ownerSwap_priorClosed_given_public signal wellFormed independent observable
      firstSite secondSite sameKey)
  have guardedSecond : ∀ history : (onePacketProtocol setup leaks bounds horizon
      scheduler).History,
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf who history.trace =
        site₂.1 → SwapGuardState setup swap (swapAllowed swap) history.state := by
    intro history member
    have guarded := ownerSwap_guard secondSite firstSite sameKey.symm secondDebtFree
      firstDebtFree (ownerSwap_priorClosed_given_public signal wellFormed independent observable
        secondSite firstSite sameKey.symm)
      history member
    rwa [ownerSwap_comm] at guarded
  -- A draw of each site.
  obtain ⟨history₁, -⟩ := site₁.2
  obtain ⟨history₂, -⟩ := site₂.2
  obtain ⟨control₁, base, state₁, baseMember, inputs₁, baseStore⟩ := siteDraw firstSite history₁
  obtain ⟨control₂, other, state₂, otherMember, inputs₂, otherStore⟩ :=
    siteDraw secondSite history₂
  have sameSignal : signal other = signal base := observable other base
    (fun input publicField => same_key_public_initial_inputs secondSite firstSite sameKey.symm
      history₂ history₁ state₂ state₁ inputs₂ inputs₁ input publicField)
  set ratio := (setup.initialLaw (splice who other base)).toReal /
    (setup.initialLaw base).toReal with ratioEq
  have ratioPos : 0 < ratio := by
    have spliceMember := setup.splice_mem_support signal independent who otherMember
      baseMember sameSignal
    exact div_pos
      (ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp spliceMember) (PMF.apply_ne_top _ _))
      (ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp baseMember) (PMF.apply_ne_top _ _))
  let shared : Set (graph setup).Inputs := hiddenPublicFiberInputs signal who base
  have sharedClosed : ∀ state ∈ (initialLaw setup).support,
      state.config.inputs ∈ swapAllowed swap ∩ shared →
        state.swap swap ∈ (initialLaw setup).support :=
    fun state member inside => initialClosed_swapAllowed swap state member inside.1
  have scaled := ownerSwap_priorScaled signal wellFormed independent preserves
    (view₁ := view₁) (view₂ := view₂) baseMember otherMember baseStore otherStore
  refine baseLawAgrees_of_swap_scaled _ _ site₁ site₂ swap (swapAllowed swap)
    (initialClosed_swapAllowed swap) bounded (swapAllowed_closed swap) guardedFirst guardedSecond
    (fun history member => ?_) (fun history member => ?_) (fun history member => ?_) ratio
    ratioPos.ne' (fun history member => ?_) payoff
  · change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
      ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
        (initialClosed_swapAllowed swap) bounded).mapTrace history.trace
          (guardedFirst history member)) = site₂.1
    rw [infoOf_mapTrace, member]
    exact infoEq
  · change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
      ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
        (initialClosed_swapAllowed swap) bounded).mapTrace history.trace
          (guardedSecond history member)) = site₁.1
    rw [infoOf_mapTrace, member, ← infoEq]
    exact swap.info_involutive _
  · by_cases other : ∃ observer, observer ≠ who
    · obtain ⟨observer, distinct⟩ := other
      exact regularTrace_mapTrace_iff_of_fixes swap _ bounded assessment who fixesOthers
        observer distinct history.trace _
    · push Not at other
      exact iff_of_true (regularTrace_of_alone assessment other _)
        (regularTrace_of_alone assessment other _)
  · obtain ⟨state, trace⟩ := history
    obtain ⟨control, stateEq, drawInside⟩ :=
      site_hiddenPublicFiberInputs signal observable firstSite history₁ state₁ inputs₁ baseStore
        ⟨⟨state, trace⟩, member⟩
    change state = some control at stateEq
    subst stateEq
    have inside : ∀ current : (application setup leaks).Control, some control = some current →
        current.execution.application.config.inputs ∈ shared := by
      rintro current same
      cases Option.some.inj same
      exact drawInside
    have restricted := swapGuardState_inter swap (guardedFirst ⟨some control, trace⟩ member)
      inside
    have recordEq := operationalRecord_mapTrace swap (initialClosed_swapAllowed swap) bounded
      trace (guardedFirst ⟨some control, trace⟩ member)
    have congrTrace := mapTrace_allowed_congr swap (initialClosed_swapAllowed swap)
      sharedClosed bounded trace (guardedFirst ⟨some control, trace⟩ member) restricted
    have weightEq := othersSourceWeight_mapTrace_scaled swap sharedClosed bounded assessment who
      fixesOthers ratio scaled trace restricted
    change othersSourceWeight setup leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
          (initialClosed_swapAllowed swap) bounded).mapTrace trace
            (guardedFirst ⟨some control, trace⟩ member)) *
        weight (operationalRecord setup leaks bounds horizon scheduler
          ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
            (initialClosed_swapAllowed swap) bounded).mapTrace trace
              (guardedFirst ⟨some control, trace⟩ member))) =
      ratio * (othersSourceWeight setup leaks bounds horizon scheduler assessment who trace *
        weight (operationalRecord setup leaks bounds horizon scheduler trace))
    rw [recordEq, congrTrace, weightEq]
    ring

end Vegas
