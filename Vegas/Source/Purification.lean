/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup
import GameTheoryExtensions.Math.Probability.Support
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.SiteDraw

/-! # Every policy is a mixture of pure ones

A deviation certificate may answer a behavioral policy with a *mixture* of
policies, but the mixture is drawn once, before the private setup law and before
any chance step, so a component has to serve every branch at once. That is what
stops the naive induction: a mixture chosen per branch is not a mixture chosen
in advance.

The construction here draws the actions of the whole program up front. A source
program is a straight line — every decision point of a player occurs exactly
once in every run — so a draw at a decision point may be coupled arbitrarily
across the views reachable there, and only independence *between* decision
points is needed. The draws at one point are independent draws at the finitely
many reachable views, whose marginal at the view actually read is the law there
(`GameTheory.Math.Probability.drawAtSites_bind_apply`).

The induction runs over a list of configurations rather than one, so that a
single mixture serves every branch created before the point reached. That list
stays finite because every step branches finitely: chance laws are exact finite
tables, fresh binding types are finite (`FiniteBindingTypes`), disclosures are
Boolean, and a setup's initial law is assumed finitely supported. A policy over
an infinite binding alphabet may mix with infinite support, and a mixture of
pure policies drawn as one probability mass function need not reproduce it.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-! ## Every policy is a mixture of pure ones -/

/-- The finitely many values of a finitely supported law, listed. -/
private def supportList {α : Type*} (law : PMF α) (finite : law.support.Finite) : List α :=
  finite.toFinset.toList

private theorem mem_supportList {α : Type*} {law : PMF α} (finite : law.support.Finite)
    {value : α} (supported : value ∈ law.support) : value ∈ supportList law finite :=
  Finset.mem_toList.mpr (finite.mem_toFinset.mpr supported)

/-- One mixture of pure policies reproduces a behavioral policy's law from every
configuration in a list, against unchanged opponents. The list is what lets a
single mixture serve every branch: the successors of a chance step, or of
another player's action, go into the list for the rest of the program. -/
theorem exists_pureMixture {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    p.FiniteBindingTypes →
    (profile : BehavioralProfile p) → (policy : BehavioralPolicy who p) →
    (configs : List (Config Player L Γ)) →
    ∃ mixture : PMF (PurePolicy who p), mixture.support.Finite ∧ ∀ config ∈ configs,
      runFrom p (Function.update profile who policy) config =
        mixture.bind fun choice =>
          runFrom p (Function.update profile who (PurePolicy.toBehavioral p choice)) config
  | _, _, .ret _, _, _, _, _ =>
      ⟨PMF.pure PUnit.unit, by simp, fun config _ => by simp [runFrom, runWith]⟩
  | Γ, _, .sample name (payload := payload) fresh law k, finite, profile, policy, configs => by
      obtain ⟨mixture, mixtureFinite, hmixture⟩ :=
        exists_pureMixture k finite (afterSample profile) policy
        (configs.flatMap fun config =>
          (supportList (L.evalDist law (sourcePublicEnv config.state))
            (L.evalDist_support_finite _ _)).map (sampleSuccessor name config))
      refine ⟨mixture, mixtureFinite, fun config hconfig => ?_⟩
      have member : ∀ value ∈ (L.evalDist law (sourcePublicEnv config.state)).support,
          sampleSuccessor name config value ∈ configs.flatMap fun other =>
            (supportList (L.evalDist law (sourcePublicEnv other.state))
              (L.evalDist_support_finite _ _)).map (sampleSuccessor name other) :=
        fun value hvalue => List.mem_flatMap.mpr ⟨config, hconfig,
          List.mem_map.mpr ⟨value, mem_supportList _ hvalue, rfl⟩⟩
      simp only [runFrom_sample, afterSample_update]
      rw [bind_congr_on_support _ fun value hvalue => hmixture _ (member value hvalue),
        PMF.bind_comm]
      rfl
  | Γ, _, .commit (payload := payload) name owner fresh guard k, finite, profile, policy,
      configs => by
      classical
      have := finite.1
      by_cases hown : owner = who
      · subst hown
        obtain ⟨tail, tailFinite, htail⟩ :=
          exists_pureMixture k finite.2 (afterCommit profile) policy.2
          (configs.flatMap fun config =>
            (supportList (policy.1 rfl (Config.view owner config)) (Set.toFinite _)).map
              (commitSuccessor name guard config))
        refine ⟨(drawAtSites (policy.1 rfl)
            (configs.map (Config.view owner)).toFinset
            (fun _ => .failure)).bind fun assigned =>
          tail.bind fun rest => PMF.pure (fun _ => assigned, rest),
          bind_support_finite (drawAtSites_support_finite _ _ _ fun _ _ => Set.toFinite _)
            fun _ _ => bind_support_finite tailFinite fun _ _ => by simp,
          fun config hconfig => ?_⟩
        have hview : Config.view owner config ∈ configs.map (Config.view owner) :=
          List.mem_map.mpr ⟨config, hconfig, rfl⟩
        have hmember : ∀ choice ∈ (policy.1 rfl (Config.view owner config)).support,
            commitSuccessor name guard config choice ∈ configs.flatMap fun other =>
              (supportList (policy.1 rfl (Config.view owner other)) (Set.toFinite _)).map
                (commitSuccessor name guard other) := fun choice hchoice =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨choice,
            mem_supportList _ hchoice, rfl⟩⟩
        have hkernel : commitKernel (Function.update profile owner policy) = policy.1 rfl := by
          simp [commitKernel]
        have hpure : ∀ choice : PurePolicy owner (.commit name owner fresh guard k),
            commitKernel (Function.update profile owner (PurePolicy.toBehavioral _ choice)) =
              fun view => PMF.pure (choice.1 rfl view) := by
          intro choice
          simp [commitKernel, PurePolicy.toBehavioral, Function.update_self]
        have hsnd : ∀ choice : PurePolicy owner (.commit name owner fresh guard k),
            (PurePolicy.toBehavioral (.commit name owner fresh guard k) choice).2 =
              PurePolicy.toBehavioral k choice.2 := fun _ => rfl
        simp only [runFrom_commit, hkernel, hpure, hsnd, afterCommit_update, PMF.bind_bind,
          PMF.pure_bind]
        rw [drawAtSites_bind_apply (policy.1 rfl)
          (configs.map (Config.view owner)).toFinset (fun _ => PublicationResult.failure)
          (List.mem_toFinset.mpr hview)
          (fun choice => tail.bind fun rest =>
            runFrom k (Function.update (afterCommit profile) owner
              (PurePolicy.toBehavioral k rest)) (commitSuccessor name guard config choice))]
        exact bind_congr_on_support _ fun choice hchoice => htail _ (hmember choice hchoice)
      · obtain ⟨tail, tailFinite, htail⟩ :=
          exists_pureMixture k finite.2 (afterCommit profile) policy.2
          (configs.flatMap fun config =>
            (supportList (commitKernel profile (Config.view owner config)) (Set.toFinite _)).map
              (commitSuccessor name guard config))
        refine ⟨tail.bind fun rest => PMF.pure (fun own => absurd own hown, rest),
          bind_support_finite tailFinite fun _ _ => by simp, fun config hconfig => ?_⟩
        have hmember : ∀ choice ∈ (commitKernel profile (Config.view owner config)).support,
            commitSuccessor name guard config choice ∈ configs.flatMap fun other =>
              (supportList (commitKernel profile (Config.view owner other)) (Set.toFinite _)).map
                (commitSuccessor name guard other) := fun choice hchoice =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨choice,
            mem_supportList _ hchoice, rfl⟩⟩
        have hkernel : ∀ replacement : BehavioralPolicy who (.commit name owner fresh guard k),
            commitKernel (Function.update profile who replacement) = commitKernel profile := by
          intro replacement
          simp [commitKernel, Function.update_of_ne hown]
        have hsnd : ∀ choice : PurePolicy who (.commit name owner fresh guard k),
            (PurePolicy.toBehavioral (.commit name owner fresh guard k) choice).2 =
              PurePolicy.toBehavioral k choice.2 := fun _ => rfl
        simp only [runFrom_commit, hkernel, hsnd, afterCommit_update, PMF.bind_bind,
          PMF.pure_bind]
        rw [bind_congr_on_support _ fun choice hchoice => htail _ (hmember choice hchoice),
          PMF.bind_comm]
  | Γ, _, .reveal (payload := payload) published owner name fresh source unresolved k,
      finite, profile, policy, configs => by
      classical
      by_cases hown : owner = who
      · subst hown
        obtain ⟨tail, tailFinite, htail⟩ :=
          exists_pureMixture k finite (afterReveal profile) policy.2
          (configs.flatMap fun config =>
            (supportList (policy.1 rfl (Config.view owner config)) (Set.toFinite _)).map
              (revealSuccessor published source config))
        refine ⟨(drawAtSites (policy.1 rfl)
            (configs.map (Config.view owner)).toFinset
            (fun _ => false)).bind fun assigned =>
          tail.bind fun rest => PMF.pure (fun _ => assigned, rest),
          bind_support_finite (drawAtSites_support_finite _ _ _ fun _ _ => Set.toFinite _)
            fun _ _ => bind_support_finite tailFinite fun _ _ => by simp,
          fun config hconfig => ?_⟩
        have hview : Config.view owner config ∈ configs.map (Config.view owner) :=
          List.mem_map.mpr ⟨config, hconfig, rfl⟩
        have hmember : ∀ disclose ∈ (policy.1 rfl (Config.view owner config)).support,
            revealSuccessor published source config disclose ∈ configs.flatMap fun other =>
              (supportList (policy.1 rfl (Config.view owner other)) (Set.toFinite _)).map
                (revealSuccessor published source other) := fun disclose hdisclose =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨disclose,
            mem_supportList _ hdisclose, rfl⟩⟩
        have hkernel : revealKernel (Function.update profile owner policy) = policy.1 rfl := by
          simp [revealKernel]
        have hpure : ∀ choice :
            PurePolicy owner (.reveal published owner name fresh source unresolved k),
            revealKernel (Function.update profile owner (PurePolicy.toBehavioral _ choice)) =
              fun view => PMF.pure (choice.1 rfl view) := by
          intro choice
          simp [revealKernel, PurePolicy.toBehavioral, Function.update_self]
        have hsnd : ∀ choice :
            PurePolicy owner (.reveal published owner name fresh source unresolved k),
            (PurePolicy.toBehavioral
              (.reveal published owner name fresh source unresolved k) choice).2 =
              PurePolicy.toBehavioral k choice.2 := fun _ => rfl
        simp only [runFrom_reveal, hkernel, hpure, hsnd, afterReveal_update, PMF.bind_bind,
          PMF.pure_bind]
        rw [drawAtSites_bind_apply (policy.1 rfl)
          (configs.map (Config.view owner)).toFinset (fun _ => false)
          (List.mem_toFinset.mpr hview)
          (fun disclose => tail.bind fun rest =>
            runFrom k (Function.update (afterReveal profile) owner
              (PurePolicy.toBehavioral k rest))
              (revealSuccessor published source config disclose))]
        exact bind_congr_on_support _ fun disclose hdisclose => htail _ (hmember disclose hdisclose)
      · obtain ⟨tail, tailFinite, htail⟩ :=
          exists_pureMixture k finite (afterReveal profile) policy.2
          (configs.flatMap fun config =>
            (supportList (revealKernel profile (Config.view owner config)) (Set.toFinite _)).map
              (revealSuccessor published source config))
        refine ⟨tail.bind fun rest => PMF.pure (fun own => absurd own hown, rest),
          bind_support_finite tailFinite fun _ _ => by simp, fun config hconfig => ?_⟩
        have hmember : ∀ disclose ∈
            (revealKernel profile (Config.view owner config)).support,
            revealSuccessor published source config disclose ∈ configs.flatMap fun other =>
              (supportList (revealKernel profile (Config.view owner other)) (Set.toFinite _)).map
                (revealSuccessor published source other) := fun disclose hdisclose =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨disclose,
            mem_supportList _ hdisclose, rfl⟩⟩
        have hkernel : ∀ replacement : BehavioralPolicy who
              (.reveal published owner name fresh source unresolved k),
            revealKernel (Function.update profile who replacement) = revealKernel profile := by
          intro replacement
          simp [revealKernel, Function.update_of_ne hown]
        have hsnd : ∀ choice :
            PurePolicy who (.reveal published owner name fresh source unresolved k),
            (PurePolicy.toBehavioral
              (.reveal published owner name fresh source unresolved k) choice).2 =
              PurePolicy.toBehavioral k choice.2 := fun _ => rfl
        simp only [runFrom_reveal, hkernel, hsnd, afterReveal_update, PMF.bind_bind,
          PMF.pure_bind]
        rw [bind_congr_on_support _ fun disclose hdisclose => htail _ (hmember disclose hdisclose),
          PMF.bind_comm]

/-- One mixture of pure policies reproduces a behavioral policy's terminal state
law across a whole setup, against unchanged opponents. The draw precedes the
private initial law, which is what a deviation certificate needs. -/
theorem exists_pureMixture_run {who : Player} (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (initialFinite : setup.initialLaw.support.Finite)
    (profile : BehavioralProfile setup.program) (policy : BehavioralPolicy who setup.program) :
    ∃ mixture : PMF (PurePolicy who setup.program), mixture.support.Finite ∧
      setup.run (Function.update profile who policy) =
        mixture.bind fun choice =>
          setup.run (Function.update profile who
            (PurePolicy.toBehavioral setup.program choice)) := by
  obtain ⟨mixture, mixtureFinite, hmixture⟩ :=
    exists_pureMixture setup.program finite profile policy
    ((supportList setup.initialLaw initialFinite).map fun initial =>
      ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩)
  refine ⟨mixture, mixtureFinite, ?_⟩
  have hrun : ∀ initial ∈ setup.initialLaw.support,
      SourceProgram.run setup.program (Function.update profile who policy) initial =
        mixture.bind fun choice =>
          SourceProgram.run setup.program
            (Function.update profile who (PurePolicy.toBehavioral setup.program choice))
            initial := fun initial hinitial =>
    hmixture _ (List.mem_map.mpr ⟨initial, mem_supportList _ hinitial, rfl⟩)
  simp only [Setup.run]
  rw [bind_congr_on_support _ hrun, PMF.bind_comm]

/-- The public result law is a pushforward of that one, so the same mixture
serves it. -/
theorem exists_pureMixture_publicRun {who : Player} (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (initialFinite : setup.initialLaw.support.Finite)
    (profile : BehavioralProfile setup.program) (policy : BehavioralPolicy who setup.program) :
    ∃ mixture : PMF (PurePolicy who setup.program), mixture.support.Finite ∧
      setup.publicRun (Function.update profile who policy) =
        mixture.bind fun choice =>
          setup.publicRun (Function.update profile who
            (PurePolicy.toBehavioral setup.program choice)) := by
  obtain ⟨mixture, mixtureFinite, hmixture⟩ :=
    exists_pureMixture_run setup finite initialFinite profile policy
  exact ⟨mixture, mixtureFinite, by simp only [Setup.publicRun, hmixture, PMF.map_bind]⟩

/-! ## The pure-strategy game

The game a source program presents when a policy may not randomize. Only the
strategies change, so the two games are compared by the identity on outcomes. -/

/-- The behavioral policies underlying a pure profile. -/
def pureProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    {p : SourceProgram Player L Γ O} (profile : ∀ who, PurePolicy who p) :
    BehavioralProfile p := fun who => PurePolicy.toBehavioral p (profile who)

namespace Setup

/-- The pure-strategy game of a setup. Reducible for the same reason as
`Setup.valueBindingGame`: `sig.Strategy` has to reduce to `PurePolicy`. -/
@[reducible] def pureGame (setup : Setup (Player := Player) (L := L)) :
    GameForm Player where
  sig :=
    { Strategy := fun who => PurePolicy who setup.program
      Outcome := SourceProgram.PublicOutcome setup.program }
  play profile := setup.publicRun (pureProfile profile)

@[simp] theorem pureGame_play (setup : Setup (Player := Player) (L := L))
    (profile : Profile setup.pureGame.sig) :
    setup.pureGame.play profile = setup.publicRun (pureProfile profile) := rfl

/-- Replacing one strategy of a pure profile replaces one policy. -/
@[simp] theorem pureProfile_update (setup : Setup (Player := Player) (L := L))
    (profile : Profile setup.pureGame.sig) (who : Player)
    (replacement : setup.pureGame.sig.Strategy who) :
    pureProfile (Profile.update profile who replacement) =
      Function.update (pureProfile profile) who
        (PurePolicy.toBehavioral setup.program replacement) := by
  funext actor
  by_cases h : actor = who
  · subst h; simp [pureProfile]
  · simp [pureProfile, Profile.update_of_ne _ _ h, Function.update_of_ne h]

end Setup

end Vegas.SourceProgram
