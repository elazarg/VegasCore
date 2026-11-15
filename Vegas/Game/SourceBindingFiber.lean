module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.BindingSourceObservation
public import Vegas.Pending.ReactiveBindingLikelihood
public import Vegas.Source.ObservationRecall
public import GameTheoryExtensions.Math.Probability.ObservedChoice

@[expose] public section

/-! # A source binding fiber with latent honest choices

The existing observed-choice factorization applies to one active source binding
while keeping an arbitrary correlated source-and-latent prior. Native traffic
coupling supplies the observation channel. Supported source checkpoints and
historical pre-binding paths derive its visible successor, even when the actual
binding completed before the phase or later events have already advanced.
These are compositional probability adapters, not equilibrium hypotheses.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- One active binding has an observation-local source kernel while retaining every
latent honest choice jointly. The existing traffic coupling and supported historical
checkpoints determine the successor fiber, including omissions and admitted failure. -/
theorem binding_source_fiber
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (who : Player) {Γ : SourceCtx Player L} {name : VarId} {payload : L.Ty}
    (guard : SourceGuard L Γ who name payload)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (event : (serviceGraph setup deps).EventId)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (owned : (serviceGraph setup deps).actor? event = some who)
    (notPublication : ¬ ((serviceGraph setup deps).outputLayout event).IsPublication)
    {Seed Latent : Type}
    (prior : PMF Seed)
    (source : Seed → {config : Config Player L Γ // who ∉ config.defaulted} × Latent)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks who (execution seed))) =
      (prior.map source).bind fun hidden => (noise (hidden.1.1.view who)).map
        (fun traffic => (hidden, traffic)))
    (phase : Seed → PMF (serviceApplication setup deps duration leaks).Execution)
    (coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks who (execution left) =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks who (execution right) →
      (phase left).map ((bindingTraffic (serviceTimeouts setup deps duration)) leaks who) =
        (phase right).map ((bindingTraffic (serviceTimeouts setup deps duration)) leaks who))
    (ghost : Seed → setup.informationGraph.Config)
    (checkpoint : ∀ seed ∈ prior.support,
      SourceCheckpoint setup (source seed).1.1 refs event.val (ghost seed))
    (ghostReach : ∀ seed ∈ prior.support, ∃ inputs, (ghost seed).Reachable inputs)
    (ghostClean : ∀ seed ∈ prior.support, (ghost seed).NoBindingDefaults)
    (frame : ∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
      ∃ before : (serviceGraph setup deps).Config,
        before.cut.Ready event ∧
        Relation.ReflTransGen EventGraph.Config.Step before final.application.config ∧
        (serviceGraph setup deps).prefixObservation who event
            ((serviceGraph setup deps).playerObserve who before) =
          setup.informationGraph.prefixObservation who event
            (setup.informationGraph.playerObserve who (ghost seed))) :
    let readChoice := fun final : (serviceApplication setup deps duration leaks).Execution =>
      OwnAction.binding who name payload
        (decodeActionAt setup.program event final.application.config.history)
    ∃ kernel : DecisionView who Γ → PMF (Option (PublicationResult (L.Val payload))),
      ∃ nextNoise : DecisionView who ((name, .commitment who payload) :: Γ) → PMF _,
        (prior.bind fun seed => (phase seed).map fun final =>
          ((commitSuccessor name guard (source seed).1.1 (readChoice final), (source seed).2),
            (bindingTraffic (serviceTimeouts setup deps duration)) leaks who final)) =
        ((prior.map source).bind fun hidden =>
          (kernel (hidden.1.1.view who)).map fun action =>
            (commitSuccessor name guard hidden.1.1 action, hidden.2)).bind fun hidden =>
          (nextNoise (hidden.1.view who)).map fun traffic => (hidden, traffic) := by
  intro readChoice
  have visible : ∀ left ∈ prior.support, ∀ leftFinal ∈ (phase left).support,
      ∀ right ∈ prior.support, ∀ rightFinal ∈ (phase right).support,
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks who leftFinal =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks who rightFinal →
      (commitSuccessor name guard (source left).1.1 (readChoice leftFinal)).view who =
        (commitSuccessor name guard (source right).1.1 (readChoice rightFinal)).view who := by
    intro left leftSupported leftFinal leftReached right rightSupported rightFinal rightReached same
    obtain ⟨leftBefore, leftReady, leftPath, leftMatch⟩ := frame left leftSupported leftFinal
      leftReached
    obtain ⟨rightBefore, rightReady, rightPath, rightMatch⟩ :=
      frame right rightSupported rightFinal rightReached
    obtain ⟨leftInputs, leftReach⟩ := ghostReach left leftSupported
    obtain ⟨rightInputs, rightReach⟩ := ghostReach right rightSupported
    have nativeViews := congrArg (fun traffic => traffic.2.2.2.2.1) same
    have observations : (serviceGraph setup deps).playerObserve who leftFinal.application.config =
        (serviceGraph setup deps).playerObserve who rightFinal.application.config := by
      apply EventPlayerObservation.ext
      · exact congrArg (fun view => view.observation.completionOrder) nativeViews
      · exact congrArg (fun view => view.observation.store) nativeViews
      · exact congrArg (fun view => view.observation.ownActions) nativeViews
      · exact congrArg (fun view => view.observation.defaults) nativeViews
    exact source_commit_view_eq_of_playerObserve relaxed guard refs event owned notPublication
      (source left).1.1 (source right).1.1 (source left).1.2 (source right).1.2
      (ghost left) (ghost right) (checkpoint left leftSupported) (checkpoint right rightSupported)
      leftReach rightReach (ghostClean left leftSupported) (ghostClean right rightSupported)
      leftBefore rightBefore leftReady rightReady leftFinal.application.config
      rightFinal.application.config leftPath rightPath leftMatch rightMatch observations
  let advance := fun (hidden : {config : Config Player L Γ // who ∉ config.defaulted} × Latent)
      (action : Option (PublicationResult (L.Val payload))) =>
    (commitSuccessor name guard hidden.1.1 action, hidden.2)
  let view := fun (hidden : {config : Config Player L Γ // who ∉ config.defaulted} × Latent) =>
    hidden.1.1.view who
  let nextView := fun (hidden : Config Player L ((name, .commitment who payload) :: Γ) × Latent) =>
    hidden.1.view who
  let decode := fun seed final => advance (source seed) (readChoice final)
  have remembered (config : Config Player L Γ) (active : who ∉ config.defaulted)
      (action : Option (PublicationResult (L.Val payload))) :
      OwnAction.binding who name payload ((commitSuccessor name guard config action).view
        who).history.getLast? = action := by
    simp only [Config.view, commitSuccessor, active, ite_false, Function.update_self,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, OwnAction.binding_commit]
  obtain ⟨kernel, _supported, nextNoise, law⟩ := exists_observed_choice_factorization prior source
    (fun seed => (bindingTraffic (serviceTimeouts setup deps duration)) leaks who (execution seed))
    view noise factor phase ((bindingTraffic (serviceTimeouts setup deps duration)) leaks who)
    coupled advance nextView decode id (fun seed _ final _ => ⟨readChoice final, rfl⟩)
    (fun left leftSupport leftFinal leftReached right rightSupport rightFinal rightReached
      leftChoice rightChoice leftEq rightEq same => by
      have leftView := congrArg nextView leftEq
      have rightView := congrArg nextView rightEq
      exact leftView.symm.trans ((visible left leftSupport leftFinal leftReached right rightSupport
        rightFinal rightReached same).trans rightView))
    (fun left leftChoice right rightChoice same => by
      change (commitSuccessor name guard left.1.1 leftChoice).view who =
        (commitSuccessor name guard right.1.1 rightChoice).view who at same
      have backed := congrArg (DecisionView.back true) same
      have back (config : Config Player L Γ) (action) :
          ((commitSuccessor name guard config action).view who).back true = config.view who := by
        simpa only [decide_true] using back_commit_view who name guard config action
      have priorView : left.1.1.view who = right.1.1.view who := by
        rw [back left.1.1 leftChoice, back right.1.1 rightChoice] at backed
        exact backed
      have chosen := congrArg (fun current => OwnAction.binding who name payload
        (DecisionView.history current).getLast?) same
      rw [remembered left.1.1 left.1.2 leftChoice,
        remembered right.1.1 right.1.2 rightChoice] at chosen
      exact ⟨priorView, chosen⟩)
    (fun _ => PMF.pure none)
  exact ⟨kernel, nextNoise, law⟩

end Vegas
