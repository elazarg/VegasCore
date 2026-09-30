/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixChoice
import Vegas.Game.SourceInformation
import Vegas.Game.RevealServiceOwnerSource
import Vegas.Game.RevealServicePerturbation

/-! # Fully mixed source choices in the restricted service

Every real source decision in the reveal-only class offers both Boolean
choices. Full mixing at source information sites therefore supplies both
branches needed to perturb all of their physical native representatives.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem RevealOnly.disclosure_choice (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O), program.RevealOnly →
      ∀ (admission : CommitmentInterface program) (view : ProtocolView who program),
      ProtocolView.actor who program view = some who →
      ∀ disclose : Bool, ∃ choice, ProtocolView.menu who program admission view choice ∧
        OwnAction.disclosure choice = disclose := by
  intro Γ O program
  induction program with
  | ret payoffs =>
      intro _reveals admission view active
      cases active
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | reveal published owner name fresh selected unresolved next ih =>
      intro reveals admission view active disclose
      cases view with
      | inl current =>
          refine ⟨some (.reveal owner name disclose), ?_, rfl⟩
          exact ⟨active, disclose, rfl⟩
      | inr view => exact ih reveals admission view active disclose

theorem Setup.reveal_choice_fullSupport
    (setup : Setup (Player := Player) (L := L)) (reveals : setup.program.RevealOnly)
    (admission : CommitmentInterface setup.program)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Player)
    (site : (setup.informationModel admission).InformationSite who) :
    FullSupport ((assessment.strategy who site.1).map fun choice =>
      OwnAction.disclosure choice.1) := by
  intro disclose
  obtain ⟨history, _running, _action⟩ := site.2
  have active := InformationModel.InformationSite.active _ site history
  have observed := (setup.protocol_info admission who history.1.trace).symm.trans history.2
  cases state : history.1.state with
  | none =>
      rw [state] at active
      cases active
  | some current =>
      have actor : ProtocolView.actor who setup.program
          (ProtocolState.observe who setup.program current) = some who := by
        simpa only [Setup.executionProtocol, state, Setup.protocolObserve, Option.map_some,
          Option.elim_some] using active
      obtain ⟨choice, legal, decoded⟩ := RevealOnly.disclosure_choice who setup.program reveals
        admission (ProtocolState.observe who setup.program current) actor disclose
      have permitted : choice ∈ (setup.informationModel admission).menu who site.1 := by
        rw [← observed, state]
        exact legal
      rw [PMF.support_map]
      exact ⟨⟨choice, permitted⟩, mixed who site ⟨choice, permitted⟩, decoded⟩

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- At an actual owner information value, the source compiler reads precisely
the original source policy, and its canonical opening is covered by the
finite backend bound. The native reference profile need not be compiled. -/
theorem owner_choice_data
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (sourceProfile : Profile (setup.informationModel admission).behavioralSignature)
    (nativeProfile : Profile
      (information setup leaks (bounds.withInitialValues (initialLaw setup))
        watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (history : (protocol setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).History)
    (supported : history ∈
      ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
        nativeProfile (blockOffset event.val + 2 * event.val + 3)).support)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (observed :
      (information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).infoOf
        who history.trace = some (past, view)) :
    sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission sourceProfile) who view =
      (sourceProfile who
        (setup.protocolObserve who (prefixReadout setup leaks event.val history.state))).map
          (fun choice => OwnAction.disclosure choice.1) ∧
    ∃ opening, opening? setup leaks who past view = some opening ∧
      opening ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
        who past view := by
  let extended := bounds.withInitialValues (initialLaw setup)
  let decoded := setup.decodeBehavioralProfile admission sourceProfile
  obtain ⟨boundary, _boundarySupport, nativeState, initial, initialSupport, source,
      _boundaryCheckpoint, opportunityCheckpoint, read⟩ :=
    owner_supported setup leaks extended watcher who reveals observer openable nativeProfile
      event owned history supported
  change ((menu setup leaks extended watcher).signals _ _ _).infoOf who history.trace = _
    at observed
  rw [(menu setup leaks extended watcher).info, nativeState] at observed
  simp only [ReactiveApplication.observe, ↓reduceIte] at observed
  cases Option.some.inj observed
  have data := owner_choices_at_prefix setup leaks bounds decoded who initial initialSupport
    setup.program reveals decoded (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program decoded)
    event.val event.isLt source (ownerOpportunity setup leaks event who boundary)
    (opportunityCheckpoint.toPublic _ _ _ _ _ _ _ _) event (by omega) owned
    ((opportunityCheckpoint.toPublic _ _ _ _ _ _ _ _).ready event (Nat.zero_add _).symm)
  refine ⟨?_, data.2.1⟩
  have encoded : setup.toProtocolBehavioralPolicy admission who (decoded who)
      (((setup.behavioralPolicyEquiv admission who).symm (sourceProfile who)).2) =
      sourceProfile who :=
    (setup.behavioralPolicyEquiv admission who).apply_symm_apply (sourceProfile who)
  have sourceLaw := setup.toProtocolBehavioralPolicy_map_val admission who (decoded who)
    (((setup.behavioralPolicyEquiv admission who).symm (sourceProfile who)).2)
    (some (ProtocolState.observe who setup.program source))
  rw [encoded] at sourceLaw
  simp only [Option.elim_some] at sourceLaw
  have sameRead : prefixReadout setup leaks event.val history.state = some source := by
    simpa only [nativeState, prefixReadout, ownerOpportunity] using read
  rw [sameRead]
  have choiceLaw := data.1
  rw [← sourceLaw, PMF.map_comp] at choiceLaw
  exact choiceLaw

/-- Positive alias trembles make the compiled policy fully mixed at every
native information site, including source-unreachable equilibrium branches. -/
theorem compiledProfile_fullyMixed
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (positive : 0 < weight) :
    (InformationModel.BehavioralAssessment.ofStrategy
      (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
        (setup.decodeBehavioralProfile admission source.strategy) weight nonnegative
        small)).IsFullyMixed := by
  intro who site choice
  let extended := bounds.withInitialValues (initialLaw setup)
  let decoded := setup.decodeBehavioralProfile admission source.strategy
  suffices choice.1 ∈ ((compiledProfile setup leaks extended watcher decoded weight nonnegative
      small who site.1).map Subtype.val).support by
    obtain ⟨other, supported, same⟩ := PMF.support_map .. ▸ this
    exact (Subtype.ext same) ▸ supported
  obtain ⟨history, running, action⟩ := site.2
  have active := InformationModel.InformationSite.active _ site history
  rcases site with ⟨info, occurs⟩
  cases info with
  | none =>
      simp only [compiledProfile, ReactiveApplication.ResponseMenu.restrictPolicy,
        PMF.pure_map, PMF.mem_support_pure_iff _ _]
      exact choice.2
  | some input =>
      rcases input with ⟨past, view⟩
      rw [compiledProfile_map_val]
      obtain ⟨response, member, value⟩ := choice.2
      rw [value, PMF.support_map]
      refine ⟨response, ?_, rfl⟩
      by_cases watches : who = watcher
      · change response ∈ (if who = watcher then _ else _ ) at member
        rw [ite_eq_left watches] at member
        simpa only [policy, ite_eq_left watches] using (Set.Finite.mem_toFinset _).mp member
      · obtain ⟨event, owned, _depth, supported⟩ :=
          owner_history_supported setup leaks extended watcher who reveals watches history.1 active
        let reference := (menu setup leaks extended watcher).uniformPolicy (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher)
        obtain ⟨choiceLaw, opening, selected, covered⟩ := owner_choice_data setup leaks bounds
          watcher who reveals observer openable admission source.strategy reference event owned
          history.1 supported past view history.2
        obtain ⟨sourceSite, sourceView⟩ := owner_source_site setup leaks extended watcher who
          reveals observer openable admission reference event owned history.1 supported
        have sourceMixed := setup.reveal_choice_fullSupport reveals admission source mixed who
          sourceSite
        rw [sourceView, ← choiceLaw] at sourceMixed
        change response ∈ (if who = watcher then _ else _) at member
        rw [ite_eq_right watches] at member
        simpa only [policy, ite_eq_right watches] using ordinaryPolicy_support setup leaks
          extended decoded weight nonnegative small positive who past view opening selected
            covered sourceMixed response member

/-- The same source perturbation sequence and vanishing alias weights converge
at every actual native decision. No positive limiting reach is required. -/
theorem compiledProfile_converges
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (sequence : Nat → Profile (setup.informationModel admission).behavioralSignature)
    (source : Profile (setup.informationModel admission).behavioralSignature)
    (converges : ∀ who (site : (setup.informationModel admission).InformationSite who),
      PMFConvergesPointwise (fun n => sequence n who site.1) (source who site.1))
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (small : ∀ n, weight n ≤ 1)
    (vanishes : Filter.Tendsto weight Filter.atTop (nhds 0))
    (who : Player)
    (site : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationSite who) :
    PMFConvergesPointwise
      (fun n => compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup))
        watcher (setup.decodeBehavioralProfile admission (sequence n)) (weight n)
          (nonnegative n) (small n) who site.1)
      (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
        (setup.decodeBehavioralProfile admission source) 0 le_rfl (by norm_num) who site.1) := by
  let extended := bounds.withInitialValues (initialLaw setup)
  obtain ⟨history, _running, _action⟩ := site.2
  have active := InformationModel.InformationSite.active _ site history
  rcases site with ⟨info, occurs⟩
  cases info with
  | none =>
      intro choice
      simp only [compiledProfile, ReactiveApplication.ResponseMenu.restrictPolicy]
      exact tendsto_const_nhds
  | some input =>
      rcases input with ⟨past, view⟩
      apply compiledProfile_converges_at setup leaks extended watcher _ _ weight nonnegative
        small vanishes who past view
      intro ordinary
      obtain ⟨event, owned, _depth, supported⟩ :=
        owner_history_supported setup leaks extended watcher who reveals ordinary history.1 active
      let reference := (menu setup leaks extended watcher).uniformPolicy (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)
      obtain ⟨sourceSite, sourceView⟩ := owner_source_site setup leaks extended watcher who
        reveals observer openable admission reference event owned history.1 supported
      have law (profile : Profile (setup.informationModel admission).behavioralSignature) :
          sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission profile) who view =
            (profile who sourceSite.1).map (fun choice => OwnAction.disclosure choice.1) := by
        rw [sourceView]
        exact (owner_choice_data setup leaks bounds watcher who reveals observer openable admission
          profile reference event owned history.1 supported past view history.2).1
      simp only [law]
      exact (converges who sourceSite).map (fun choice => OwnAction.disclosure choice.1)

end Vegas
