/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup
import GameTheoryExtensions.Math.Probability.FinDist

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
points is needed. The draws at one point therefore come from a coupling with
prescribed marginals over the finitely many reachable configurations, which
`GameTheory.Math.Probability.FinDist.pointCoupling` builds by a fold and which
needs no product.

The induction runs over a list of configurations rather than one, so that a
single mixture serves every branch created before the point reached.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-! ## Every policy is a mixture of pure ones -/

/-- One mixture of pure policies reproduces a behavioral policy's law from every
configuration in a list, against unchanged opponents. The list is what lets a
single mixture serve every branch: the successors of a chance step, or of
another player's action, go into the list for the rest of the program. -/
theorem exists_pureMixture {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile p) → (policy : BehavioralPolicy who p) →
    (configs : List (Config Player L Γ)) →
    ∃ mixture : FinDist (PurePolicy who p), ∀ config ∈ configs,
      runFrom p (Function.update profile who policy) config =
        mixture.bind fun choice =>
          runFrom p (Function.update profile who (PurePolicy.toBehavioral p choice)) config
  | _, _, .ret _, _, _, _ =>
      ⟨FinDist.pure PUnit.unit, fun config _ => by simp [runFrom, runWith]⟩
  | Γ, _, .sample name (payload := payload) fresh law k, profile, policy, configs => by
      obtain ⟨mixture, hmixture⟩ := exists_pureMixture k (afterSample profile) policy
        (configs.flatMap fun config =>
          ((L.evalDist law (sourcePublicEnv config.state)).supportFinset.toList).map
            (sampleSuccessor name config))
      refine ⟨mixture, fun config hconfig => ?_⟩
      have member : ∀ value ∈ (L.evalDist law (sourcePublicEnv config.state)).support,
          sampleSuccessor name config value ∈ configs.flatMap fun other =>
            ((L.evalDist law (sourcePublicEnv other.state)).supportFinset.toList).map
              (sampleSuccessor name other) := fun value hvalue =>
        List.mem_flatMap.mpr ⟨config, hconfig,
          List.mem_map.mpr ⟨value, Finset.mem_toList.mpr
            (FinDist.mem_supportFinset.mpr hvalue), rfl⟩⟩
      simp only [runFrom_sample, afterSample_update]
      rw [FinDist.bind_congr fun value hvalue => hmixture _ (member value hvalue),
        FinDist.bind_comm]
      rfl
  | Γ, _, .commit (payload := payload) name owner fresh guard k, profile, policy, configs => by
      classical
      by_cases hown : owner = who
      · subst hown
        obtain ⟨tail, htail⟩ := exists_pureMixture k (afterCommit profile) policy.2
          (configs.flatMap fun config =>
            ((policy.1 rfl (Config.view owner config)).supportFinset.toList).map
              (commitSuccessor name guard config))
        refine ⟨(FinDist.pointCoupling (policy.1 rfl) (fun _ => .failure)
            (configs.map (Config.view owner))).bind fun assigned =>
          tail.bind fun rest => FinDist.pure (fun _ => assigned, rest),
          fun config hconfig => ?_⟩
        have hview : Config.view owner config ∈ configs.map (Config.view owner) :=
          List.mem_map.mpr ⟨config, hconfig, rfl⟩
        have hmember : ∀ choice ∈ (policy.1 rfl (Config.view owner config)).support,
            commitSuccessor name guard config choice ∈ configs.flatMap fun other =>
              ((policy.1 rfl (Config.view owner other)).supportFinset.toList).map
                (commitSuccessor name guard other) := fun choice hchoice =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨choice,
            Finset.mem_toList.mpr (FinDist.mem_supportFinset.mpr hchoice), rfl⟩⟩
        have hkernel : commitKernel (Function.update profile owner policy) = policy.1 rfl := by
          simp [commitKernel]
        have hpure : ∀ choice : PurePolicy owner (.commit name owner fresh guard k),
            commitKernel (Function.update profile owner (PurePolicy.toBehavioral _ choice)) =
              fun view => FinDist.pure (choice.1 rfl view) := by
          intro choice
          simp [commitKernel, PurePolicy.toBehavioral, Function.update_self]
        have hsnd : ∀ choice : PurePolicy owner (.commit name owner fresh guard k),
            (PurePolicy.toBehavioral (.commit name owner fresh guard k) choice).2 =
              PurePolicy.toBehavioral k choice.2 := fun _ => rfl
        simp only [runFrom_commit, hkernel, hpure, hsnd, afterCommit_update, FinDist.bind_bind,
          FinDist.pure_bind]
        rw [FinDist.pointCoupling_bind_apply (policy.1 rfl) (fun _ => PublicationResult.failure)
          (configs.map (Config.view owner)) (Config.view owner config) hview
          (fun choice => tail.bind fun rest =>
            runFrom k (Function.update (afterCommit profile) owner
              (PurePolicy.toBehavioral k rest)) (commitSuccessor name guard config choice))]
        exact FinDist.bind_congr fun choice hchoice => htail _ (hmember choice hchoice)
      · obtain ⟨tail, htail⟩ := exists_pureMixture k (afterCommit profile) policy.2
          (configs.flatMap fun config =>
            ((commitKernel profile (Config.view owner config)).supportFinset.toList).map
              (commitSuccessor name guard config))
        refine ⟨tail.bind fun rest => FinDist.pure (fun own => absurd own hown, rest),
          fun config hconfig => ?_⟩
        have hmember : ∀ choice ∈ (commitKernel profile (Config.view owner config)).support,
            commitSuccessor name guard config choice ∈ configs.flatMap fun other =>
              ((commitKernel profile (Config.view owner other)).supportFinset.toList).map
                (commitSuccessor name guard other) := fun choice hchoice =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨choice,
            Finset.mem_toList.mpr (FinDist.mem_supportFinset.mpr hchoice), rfl⟩⟩
        have hkernel : ∀ replacement : BehavioralPolicy who (.commit name owner fresh guard k),
            commitKernel (Function.update profile who replacement) = commitKernel profile := by
          intro replacement
          simp [commitKernel, Function.update_of_ne hown]
        have hsnd : ∀ choice : PurePolicy who (.commit name owner fresh guard k),
            (PurePolicy.toBehavioral (.commit name owner fresh guard k) choice).2 =
              PurePolicy.toBehavioral k choice.2 := fun _ => rfl
        simp only [runFrom_commit, hkernel, hsnd, afterCommit_update, FinDist.bind_bind,
          FinDist.pure_bind]
        rw [FinDist.bind_congr fun choice hchoice => htail _ (hmember choice hchoice),
          FinDist.bind_comm]
  | Γ, _, .reveal (payload := payload) published owner name fresh source unresolved k,
      profile, policy, configs => by
      classical
      by_cases hown : owner = who
      · subst hown
        obtain ⟨tail, htail⟩ := exists_pureMixture k (afterReveal profile) policy.2
          (configs.flatMap fun config =>
            ((policy.1 rfl (Config.view owner config)).supportFinset.toList).map
              (revealSuccessor published source config))
        refine ⟨(FinDist.pointCoupling (policy.1 rfl) (fun _ => false)
            (configs.map (Config.view owner))).bind fun assigned =>
          tail.bind fun rest => FinDist.pure (fun _ => assigned, rest),
          fun config hconfig => ?_⟩
        have hview : Config.view owner config ∈ configs.map (Config.view owner) :=
          List.mem_map.mpr ⟨config, hconfig, rfl⟩
        have hmember : ∀ disclose ∈ (policy.1 rfl (Config.view owner config)).support,
            revealSuccessor published source config disclose ∈ configs.flatMap fun other =>
              ((policy.1 rfl (Config.view owner other)).supportFinset.toList).map
                (revealSuccessor published source other) := fun disclose hdisclose =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨disclose,
            Finset.mem_toList.mpr (FinDist.mem_supportFinset.mpr hdisclose), rfl⟩⟩
        have hkernel : revealKernel (Function.update profile owner policy) = policy.1 rfl := by
          simp [revealKernel]
        have hpure : ∀ choice :
            PurePolicy owner (.reveal published owner name fresh source unresolved k),
            revealKernel (Function.update profile owner (PurePolicy.toBehavioral _ choice)) =
              fun view => FinDist.pure (choice.1 rfl view) := by
          intro choice
          simp [revealKernel, PurePolicy.toBehavioral, Function.update_self]
        have hsnd : ∀ choice :
            PurePolicy owner (.reveal published owner name fresh source unresolved k),
            (PurePolicy.toBehavioral
              (.reveal published owner name fresh source unresolved k) choice).2 =
              PurePolicy.toBehavioral k choice.2 := fun _ => rfl
        simp only [runFrom_reveal, hkernel, hpure, hsnd, afterReveal_update, FinDist.bind_bind,
          FinDist.pure_bind]
        rw [FinDist.pointCoupling_bind_apply (policy.1 rfl) (fun _ => false)
          (configs.map (Config.view owner)) (Config.view owner config) hview
          (fun disclose => tail.bind fun rest =>
            runFrom k (Function.update (afterReveal profile) owner
              (PurePolicy.toBehavioral k rest))
              (revealSuccessor published source config disclose))]
        exact FinDist.bind_congr fun disclose hdisclose => htail _ (hmember disclose hdisclose)
      · obtain ⟨tail, htail⟩ := exists_pureMixture k (afterReveal profile) policy.2
          (configs.flatMap fun config =>
            ((revealKernel profile (Config.view owner config)).supportFinset.toList).map
              (revealSuccessor published source config))
        refine ⟨tail.bind fun rest => FinDist.pure (fun own => absurd own hown, rest),
          fun config hconfig => ?_⟩
        have hmember : ∀ disclose ∈
            (revealKernel profile (Config.view owner config)).support,
            revealSuccessor published source config disclose ∈ configs.flatMap fun other =>
              ((revealKernel profile (Config.view owner other)).supportFinset.toList).map
                (revealSuccessor published source other) := fun disclose hdisclose =>
          List.mem_flatMap.mpr ⟨config, hconfig, List.mem_map.mpr ⟨disclose,
            Finset.mem_toList.mpr (FinDist.mem_supportFinset.mpr hdisclose), rfl⟩⟩
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
        simp only [runFrom_reveal, hkernel, hsnd, afterReveal_update, FinDist.bind_bind,
          FinDist.pure_bind]
        rw [FinDist.bind_congr fun disclose hdisclose => htail _ (hmember disclose hdisclose),
          FinDist.bind_comm]

/-- One mixture of pure policies reproduces a behavioral policy's terminal state
law across a whole setup, against unchanged opponents. The draw precedes the
private initial law, which is what a deviation certificate needs. -/
theorem exists_pureMixture_run {who : Player} (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (policy : BehavioralPolicy who setup.program) :
    ∃ mixture : FinDist (PurePolicy who setup.program),
      setup.run (Function.update profile who policy) =
        mixture.bind fun choice =>
          setup.run (Function.update profile who
            (PurePolicy.toBehavioral setup.program choice)) := by
  obtain ⟨mixture, hmixture⟩ := exists_pureMixture setup.program profile policy
    (setup.initialLaw.supportFinset.toList.map fun initial =>
      ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩)
  refine ⟨mixture, ?_⟩
  have hrun : ∀ initial ∈ setup.initialLaw.support,
      SourceProgram.run setup.program (Function.update profile who policy) initial =
        mixture.bind fun choice =>
          SourceProgram.run setup.program
            (Function.update profile who (PurePolicy.toBehavioral setup.program choice))
            initial := fun initial hinitial =>
    hmixture _ (List.mem_map.mpr ⟨initial,
      Finset.mem_toList.mpr (FinDist.mem_supportFinset.mpr hinitial), rfl⟩)
  simp only [Setup.run]
  rw [FinDist.bind_congr hrun, FinDist.bind_comm]

/-- The public result law is a pushforward of that one, so the same mixture
serves it. -/
theorem exists_pureMixture_publicRun {who : Player} (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (policy : BehavioralPolicy who setup.program) :
    ∃ mixture : FinDist (PurePolicy who setup.program),
      setup.publicRun (Function.update profile who policy) =
        mixture.bind fun choice =>
          setup.publicRun (Function.update profile who
            (PurePolicy.toBehavioral setup.program choice)) := by
  obtain ⟨mixture, hmixture⟩ := exists_pureMixture_run setup profile policy
  exact ⟨mixture, by simp only [Setup.publicRun, hmixture, FinDist.map_bind]⟩

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
