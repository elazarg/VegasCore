/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.ConditionalPhaseExecution
import VegasTests.ConditionalDefaultPolicy
import VegasTests.ConditionalSourceCoupling

/-! # Conditional execution after an actual binding fallback

The binding prefix below ends with the real permissionless expiry packet from
`ConditionalDefaultApplication`.  The following owner and environment
invocations realize an arbitrary legal source kernel using the strict
public-default codec.  No opaque handle or frozen opening is assumed.
-/

noncomputable section

namespace VegasTests.ConditionalDefaultPhase

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalDefaultApplication
open VegasTests.ConditionalDefaultPolicy
open VegasTests.ConditionalSourceCoupling

abbrev Player := ConditionalApplicationImage.Player

def expiryPending : timedImage.application.State :=
  { MessageApplication.State.initial timedImage.application
      ((initialNative.register 0 0 ⟨.bool, true⟩).advance 11) with
    pool := ((MessagePool.empty Player Payload).submit 1
      (.expireBinding timedBindingCode.node)).2 }

/-- The actual expiry inclusion supplies the source checkpoint whose sealed
value is the generated public fallback, independently of the private cache. -/
theorem expired_source_successor :
    ∃ current : CoupledAt compiled.graph boundBuild,
      current.current.source = source.env.cons false ∧
        defaultIncluded.application.Refines current.current.graph.1 := by
  have hrefines : expiryPending.application.Refines checkpoint.current.graph.1 :=
    ((ApplicationImage.State.initial_refines compiled.graph).register
      0 0 ⟨.bool, true⟩).advance 11
  have hresult := SourceDecisionSite.PublicFallback.expiry_include_source_coupling
    (P := Player) (L := simpleExpr) (Γ := []) (name := 0) (who := 0) (ty := .bool)
    (.constBool true) _ fallback source.fresh compilerInitial 10 checkpoint
    timedImage expiryPending hrefines (by decide) timedBindingCode.node timed_lookup
    (1, 0) (by rfl)
  obtain ⟨current, hsource, hnext, _⟩ := hresult
  refine ⟨current, hsource, ?_⟩
  change defaultIncluded.application.Refines current.current.graph.1 at hnext
  exact hnext

def players
    (sourcePolicy :
      (visible : Env simpleExpr.Val
        (eraseVCtx (viewVCtx (0 : Player) OpeningContext))) →
      FinDist { value : Option Bool // evalGuard openingGuard value visible = true }) :
    Player → timedImage.application.PlayerPolicy :=
  fun who => if who = 0 then
    conditionalSite.imagePolicy source.fresh compilerInitial 0 10 timedImage
      (timedImage.ownerReadout? 0
        (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads)
      sourcePolicy (fun _ _ => false)
  else fun _ _ => FinDist.pure .wait

def includeConditional : timedImage.application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (0, 0))

/-- After the real binding expiry, the generated dynamic policy and the shared
runner implement the exact source continuation law for every randomized legal
source policy. -/
theorem expired_conditional_phase
    (sourcePolicy :
      (visible : Env simpleExpr.Val
        (eraseVCtx (viewVCtx (0 : Player) OpeningContext))) →
      FinDist { value : Option Bool // evalGuard openingGuard value visible = true }) :
    ∃ current : CoupledAt compiled.graph boundBuild,
      current.current.source = source.env.cons false ∧
      let code := conditionalCode 10
      let execution := ConditionalDefaultPolicy.execution
      let disposition : BindingDisposition (CommitmentHandle Player Nat) Bool :=
        .publicDefault false
      let id := ((0 : Player), execution.native.pool.nextSerial 0)
      timedImage.application.runPolicies (players sourcePolicy) includeConditional
          [.player 0, .environment] execution =
        (sourcePolicy ((current.current.source.toView 0).eraseEnv)).bind fun chosen =>
          (timedImage.application.playerStep 0 execution
            (.submit (.conditional code.endpoint.publicationNode
              (conditionalSite.sourceRequestPayload source.fresh compilerInitial 0 10
                disposition (specification.encoding chosen.1))))).bind fun submitted =>
          timedImage.application.environmentPolicyStep submitted (.include id) := by
  obtain ⟨current, hsource, hrefines⟩ := expired_source_successor
  let view := MessageApplication.State.observe timedImage.application
    ConditionalDefaultPolicy.execution.native 0
  have hsome : (timedImage.ownerReadout? 0
      (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads
      (ConditionalDefaultPolicy.execution.principalHistory 0) view).isSome := by
    decide
  obtain ⟨reads, hreadout⟩ := Option.isSome_iff_exists.mp hsome
  have hreads := conditionalSite.choice.decision.ownerReadout?_graph_reads source.fresh
    compilerInitial timedImage (ConditionalDefaultPolicy.execution.principalHistory 0) view
    ConditionalDefaultPolicy.execution.native.application rfl current.current.graph.1 hrefines
    (by
      intro field value _ haccepted _
      have habsent :
          (ConditionalDefaultPolicy.execution.native.application.memory.accepted field).bind
          BindingDisposition.opaqueHandle? = none := by
        cases field <;> rfl
      rw [haccepted] at habsent
      cases habsent)
    reads hreadout
  have hphase := ConditionalPublicationSite.conditional_phase_source_law
    (P := Player) (L := simpleExpr) (Γ := OpeningContext)
    (name := 1) (publicName := 2) (who := 0) (ty := .option .bool)
    openingGuard tail specification source.fresh.2 boundBuild 0 10 current timedImage
    sourcePolicy (players sourcePolicy) includeConditional
    ConditionalDefaultPolicy.execution hrefines opening_publicly_validatable
    (.publicDefault false) (by rfl) (by intro handle h; cases h)
    (by rfl) reads
    (by intro history; simp only [players]; rfl)
    (by intro chosen hchosen submitted hsubmitted; rfl)
    (by rfl) (by rfl) hreadout hreads
    (by intro chosen hchosen handle value h; cases h)
  refine ⟨current, hsource, ?_⟩
  convert hphase.1 using 1
  apply FinDist.bind_congr
  intro chosen _
  cases specification.encoding chosen.1 <;>
    simp only [ConditionalPublicationSite.sourceRequestPayload] <;> rfl

end VegasTests.ConditionalDefaultPhase

/--
info: 'VegasTests.ConditionalDefaultPhase.expired_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDefaultPhase.expired_source_successor

/--
info: 'VegasTests.ConditionalDefaultPhase.expired_conditional_phase' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDefaultPhase.expired_conditional_phase
