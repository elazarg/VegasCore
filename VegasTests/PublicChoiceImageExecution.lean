/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy
import Vegas.Compile.ApplicationOwnerPhase
import Vegas.Compile.PublicChoiceImageExecution
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.ApplicationImage

/-! # Generated public-choice phase execution

The first guarded choice in the mixed-type generated image is exercised by
the structurally lifted source profile and the real owner-local readout.  A
one-step service includes the controller's freshly submitted envelope through
the shared policy runner.
-/

noncomputable section

namespace VegasTests.PublicChoiceImageExecution

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationImage

def initialPolicyExecution : image.application.PolicyExecution :=
  PolicyExecution.initial image.application initialExecution

def includeFirst : image.application.EnvironmentPolicy := fun _ _ =>
  FinDist.pure (.include (0, 0))

def earlySecondPayload : image.application.Payload :=
  .choice secondAddress ⟨.option .bool, none⟩

def opponentTrafficPlayers (profile : SourceBehavioralProfile source.prog) :
    Fin 2 → image.application.PlayerPolicy := fun player =>
  if player = 1 then fun _ _ => FinDist.pure (.submit earlySecondPayload)
  else applicationPlan.liftProfile (fun _ => 0) profile player

def deliverOpponentTraffic : image.application.EnvironmentPolicy := fun _ _ =>
  FinDist.pure (.deliver 0 (1, 0))

def opponentTrafficLaw (profile : SourceBehavioralProfile source.prog) :=
  image.application.runPolicies (opponentTrafficPlayers profile) deliverOpponentTraffic
    [.player 1, .environment] initialPolicyExecution

def afterOpponentTraffic (profile : SourceBehavioralProfile source.prog) :
    image.application.PolicyExecution :=
  (opponentTrafficLaw profile).support_nonempty.choose

private theorem afterOpponentTraffic_mem (profile : SourceBehavioralProfile source.prog) :
    afterOpponentTraffic profile ∈ (opponentTrafficLaw profile).support :=
  (opponentTrafficLaw profile).support_nonempty.choose_spec

private theorem afterOpponentTraffic_properties
    (profile : SourceBehavioralProfile source.prog) :
    (afterOpponentTraffic profile).native.application = initialState ∧
      (afterOpponentTraffic profile).principalHistory 0 = [] ∧
      (afterOpponentTraffic profile).native.pool.inbox 0 =
        [⟨(1, 0), earlySecondPayload⟩] ∧
      (afterOpponentTraffic profile).native.pool.nextSerial 0 = 0 := by
  have hreached := afterOpponentTraffic_mem profile
  simp only [opponentTrafficLaw, MessageApplication.runPolicies,
    MessageApplication.invoke, opponentTrafficPlayers, if_pos,
    FinDist.pure_bind, deliverOpponentTraffic,
    FinDist.support_bind, Set.mem_iUnion] at hreached
  obtain ⟨submitted, hsubmitted, hdelivered⟩ := hreached
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at hsubmitted
  subst submitted
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at hdelivered
  obtain ⟨delivered, hdelivered, hfinal⟩ := hdelivered
  subst delivered
  rw [hfinal]
  exact ⟨rfl, by simp [initialPolicyExecution, PolicyExecution.initial], rfl, rfl⟩

private theorem initialReadout :
    ∃ reads : ReadEnv simpleExpr
        (firstSite.compiledGuard source.fresh compilerInitial).choiceReads,
      image.ownerReadout? 0
          (firstSite.compiledGuard source.fresh compilerInitial).choiceReads []
          (MessageApplication.State.observe image.application initialExecution 0) = some reads ∧
        ReadEnv.ofStore? compiled.graph.initialStore
          (firstSite.compiledGuard source.fresh compilerInitial).choiceReads = some reads := by
  let refs := (firstSite.compiledGuard source.fresh compilerInitial).choiceReads
  let available : ∀ ref, ref ∈ refs →
      ∃ value, Store.getAs compiled.graph.initialStore ref.field ref.ty = some value := by
    intro ref href
    have href' : ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr) := by
      change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
        Finset (FieldRef simpleExpr)) at href
      simpa using href
    subst ref
    exact ⟨true, rfl⟩
  let reads := ReadEnv.ofStore compiled.graph.initialStore refs available
  have hreads : ReadEnv.ofStore? compiled.graph.initialStore refs = some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos available]
  refine ⟨reads, ?_, hreads⟩
  unfold ApplicationImage.ownerReadout?
  rw [show (MessageApplication.State.observe image.application initialExecution 0).application =
      initialMemory by rfl]
  apply ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some
  apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
  intro ref href
  have href' : ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr) := by
    change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
      Finset (FieldRef simpleExpr)) at href
    simpa using href
  subst ref
  rfl

/-- The real lifted first choice has its exact source decision law through
submission and successful inclusion.  The equality retains complete native
state and policy histories rather than projecting only the chosen Boolean. -/
theorem first_publicChoice_phase_source_law
    (profile : SourceBehavioralProfile source.prog) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 0) profile)
        includeFirst [.player 0, .environment] initialPolicyExecution =
      (profile 0 firstSite.decision ((source.env.toView 0).eraseEnv)).bind fun chosen =>
        (image.application.playerStep 0 initialPolicyExecution
          (.submit ((ApplicationImage.choiceEncoding
            (P := VegasTests.ApplicationImage.Player) (L := simpleExpr)
            firstAddress BaseTy.bool).encode chosen.1))).bind
            fun submitted => image.application.environmentPolicyStep submitted
              (.include (0, 0)) := by
  obtain ⟨reads, hreadout, hreads⟩ := initialReadout
  have hagrees : (firstSite.siteState source.fresh compilerInitial).Agrees
      compiled.graph.initialStore source.env := by
    exact (compiledInitialCoupled source).current.agrees
  have hlaw := firstSite.publicChoice_phase_source_law source.fresh compilerInitial image
    (image.ownerReadout? 0 (firstSite.compiledGuard source.fresh compilerInitial).choiceReads)
    (profile 0 firstSite.decision) (fun _ _ => false)
    (applicationPlan.liftProfile (fun _ => 0) profile) includeFirst initialPolicyExecution
    compiled.graph.initialStore source.env reads
    (by rfl) (by intro chosen hchosen submitted hsubmitted; rfl) (by rfl)
    first_publicly_validatable hagrees
    (ApplicationImage.State.initial_refines compiled.graph).memory.publicFields
    image_lookup_first (by rfl) (by rfl) hreadout hreads
  exact hlaw.1

/-- The unchanged first owner retains the exact source kernel after the other
player has submitted a future-endpoint packet and delivered it to the owner's
inbox.  The prefix uses the real runner, a non-reference opponent policy, and
ordinary message delivery; its raw packet remains present when the phase
starts. -/
theorem first_publicChoice_after_opponent_traffic
    (profile : SourceBehavioralProfile source.prog) :
    image.application.runPolicies (opponentTrafficPlayers profile)
        includeFirst [.player 0, .environment] (afterOpponentTraffic profile) =
      (profile 0 firstSite.decision ((source.env.toView 0).eraseEnv)).bind fun chosen =>
        (image.application.playerStep 0 (afterOpponentTraffic profile)
          (.submit ((ApplicationImage.choiceEncoding
            (P := VegasTests.ApplicationImage.Player) (L := simpleExpr)
            firstAddress BaseTy.bool).encode chosen.1))).bind
              fun submitted => image.application.environmentPolicyStep submitted
                (.include (0, 0)) := by
  have hproperties := afterOpponentTraffic_properties profile
  have howner : opponentTrafficPlayers profile 0 =
      applicationPlan.liftProfile (fun _ => 0) profile 0 := by
    simp [opponentTrafficPlayers]
  have hinitial : compiled.InitialReadsPublic
      (eventGuardOf compilerInitial (0 : Fin 2) firstGuard).choiceReads := by
    apply (compiled.allInitialFieldsPublic_of_owners ?_).reads
    intro initial hinitial
    change initial ∈ [⟨BaseTy.bool, none, true⟩] at hinitial
    rw [List.mem_singleton] at hinitial
    subst initial
    rfl
  have hrefines : (afterOpponentTraffic profile).native.application.Refines
      (compiledInitialCoupled source).current.graph.1 := by
    rw [hproperties.1]
    exact ApplicationImage.State.initial_refines compiled.graph
  have hcache : ChoiceEncoding.cachedValue image.application
      ((ApplicationImage.choiceEncoding (P := Fin 2) firstAddress BaseTy.bool).submission
        image.application) ((afterOpponentTraffic profile).principalHistory 0) = none := by
    rw [hproperties.2.1]
    rfl
  have hlaw := ApplicationPlan.ProfileContinuation.publicChoice_phase_of_unchanged_owner
    (root := applicationPlan) (rootProfile := profile) (.refl) (fun _ => 0)
    (opponentTrafficPlayers profile) howner deliverOpponentTraffic
    [.player 1, .environment] (afterOpponentTraffic profile)
    (afterOpponentTraffic_mem profile) (compiledInitialCoupled source) hrefines hinitial hcache
    includeFirst (by
      intro chosen hchosen submitted hsubmitted
      rw [hproperties.2.2.2]
      rfl)
  have hphase := hlaw.1
  dsimp only at hphase
  rw [hproperties.2.2.2] at hphase
  exact hphase

end VegasTests.PublicChoiceImageExecution

/-- info: 'VegasTests.PublicChoiceImageExecution.first_publicChoice_phase_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.PublicChoiceImageExecution.first_publicChoice_phase_source_law

/-- info: 'VegasTests.PublicChoiceImageExecution.first_publicChoice_after_opponent_traffic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.PublicChoiceImageExecution.first_publicChoice_after_opponent_traffic
