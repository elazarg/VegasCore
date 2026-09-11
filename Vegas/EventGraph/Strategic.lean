/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheoryExtensions.Core.MixtureSimulation
import GameTheory.Protocol.Strategic
import Vegas.EventGraph.KernelBehavioral
import Vegas.EventGraph.PolicyRoundtrip

/-! # Strategic forms for the declared-read graph kernel

The graph has two presentations of the same strategic execution.  The
behavioral presentation lets a player randomize at its information states;
the canonical presentation samples one declared-read law at each graph node
and executes nodes in the certified order.  Under information locality and a
single ready node per player, arbitrary behavioral graph policies are exactly
backtranslated to canonical policies.  This is a game-form theorem, not a
runtime assumption: a later message application can use it only after proving
that its own policies implement this graph presentation.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.GameForm GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-! ## The two graph game forms -/

def policySignature (G : Graph Player L) : GameSignature Player where
  Strategy := CommitPolicy G
  Outcome := ReachableConfig G

def policyGame (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    GameForm Player where
  sig := policySignature G
  play profile :=
    runPolicyNodes hwf hguards profile
      ⟨Config.initial G, .initial⟩ G.nodeOrder

def behavioralGame (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    GameForm Player :=
  (toInformationModel G hwf hguards).toBehavioralGameForm G.nodeCount

/-! The observation maps are written as local definitions below, where the
proof arguments to the information model are explicit. -/

namespace Strategic

variable (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)

abbrev graphModel := toInformationModel G hwf hguards

def policyObserve : (policySignature G).Outcome → ReachableConfig G := id

def behavioralObserve : (graphModel G hwf hguards).strategicSignature.Outcome →
    ReachableConfig G := fun history => history.state

private theorem runBehavioralFrom_update_localized_eq
    (hlocal : CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : Config G) who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second)
    (profile : Profile (graphModel G hwf hguards).behavioralSignature)
    (who : Player) (replacement : CommitPolicy G who)
    (fuel : Nat) (history : (toExecutionProtocol G hwf hguards).History) :
    (graphModel G hwf hguards).runBehavioralFrom
        (fun player =>
          (Profile.update (sig := policySignature G)
            (fun player => CommitPolicy.fromBehavioral hwf hguards player
              (profile player)) who replacement player).behavioral hwf hguards)
        fuel history =
      (graphModel G hwf hguards).runBehavioralFrom
        (fun player =>
          (CommitPolicy.fromBehavioral hwf hguards player
            ((Profile.update (sig := (graphModel G hwf hguards).behavioralSignature)
              profile who (CommitPolicy.behavioral hwf hguards replacement)) player)).behavioral
            hwf hguards)
        fuel history := by
  apply (graphModel G hwf hguards).runBehavioralFrom_congr
  intro later _ hterm player
  by_cases hplayer : player = who
  · subst player
    have htarget :
        (Profile.update (sig := policySignature G)
          (fun player => CommitPolicy.fromBehavioral hwf hguards player
            (profile player)) who replacement) who = replacement :=
      Profile.update_same _ _ _
    have hsource :
        (Profile.update (sig := (graphModel G hwf hguards).behavioralSignature)
          profile who (CommitPolicy.behavioral hwf hguards replacement)) who =
          CommitPolicy.behavioral hwf hguards replacement :=
      Profile.update_same _ _ _
    rw [htarget, hsource]
    exact
      (CommitPolicy.behavioral_fromBehavioral hwf hguards hlocal who
        (CommitPolicy.behavioral hwf hguards replacement) later.trace
        (fun first second => hsingle later.state.1 who first second)).symm
  · have htarget :
        (Profile.update (sig := policySignature G)
          (fun player => CommitPolicy.fromBehavioral hwf hguards player
            (profile player)) who replacement) player =
          CommitPolicy.fromBehavioral hwf hguards player (profile player) :=
      Profile.update_of_ne _ _ hplayer
    have hsource :
        (Profile.update (sig := (graphModel G hwf hguards).behavioralSignature)
          profile who (CommitPolicy.behavioral hwf hguards replacement)) player =
          profile player :=
      Profile.update_of_ne _ _ hplayer
    rw [htarget, hsource]

private theorem policyRun_eq_behavioralRun
    (hlocal : CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : Config G) who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second)
    (profile : Profile (graphModel G hwf hguards).behavioralSignature) :
    (policyGame G hwf hguards).play
        (fun who => CommitPolicy.fromBehavioral hwf hguards who (profile who)) =
      ((graphModel G hwf hguards).runBehavioral profile G.nodeCount).map
        (fun history => history.state) := by
  change runPolicyNodes hwf hguards
      (fun who => CommitPolicy.fromBehavioral hwf hguards who (profile who))
        ⟨Config.initial G, .initial⟩ G.nodeOrder = _
  rw [← runBehavioral_eq_nodeOrder hwf hguards
    (fun who => CommitPolicy.fromBehavioral hwf hguards who (profile who)) hsingle]
  change
    ((graphModel G hwf hguards).runBehavioral
      (fun who => (CommitPolicy.fromBehavioral hwf hguards who
        (profile who)).behavioral hwf hguards) G.nodeCount).map
        (fun history => history.state) = _
  change
    ((graphModel G hwf hguards).runBehavioralFrom
      (fun who => (CommitPolicy.fromBehavioral hwf hguards who
        (profile who)).behavioral hwf hguards) G.nodeCount
      (toExecutionProtocol G hwf hguards).initHistory).map
        (fun history => history.state) =
      ((graphModel G hwf hguards).runBehavioralFrom profile G.nodeCount
        (toExecutionProtocol G hwf hguards).initHistory).map
        (fun history => history.state)
  rw [runBehavioralFrom_localized hwf hguards hlocal hsingle profile]

/-! ## Exact unilateral deviations -/

/- The generic simulation interface records a finite mixture because that is
the compositional contract needed by arbitrary runtime edges.  This graph
edge is sharper: its canonical policy replacement is exactly one behavioral
graph replacement.  Keep the sharper law here so clients need not unpack the
implementation of `simulation`. -/

theorem deviation_law
    (hlocal : CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : Config G) who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second)
    (profile : Profile (graphModel G hwf hguards).behavioralSignature)
    (who : Player) (replacement : CommitPolicy G who) :
    ∃ sourceReplacement : (graphModel G hwf hguards).behavioralSignature.Strategy who,
      ((policyGame G hwf hguards).play
          (Profile.update (fun player => CommitPolicy.fromBehavioral hwf hguards player
            (profile player)) who replacement)).map (policyObserve G) =
        ((behavioralGame G hwf hguards).play
          (Profile.update profile who sourceReplacement)).map
            (behavioralObserve G hwf hguards) := by
  refine ⟨CommitPolicy.behavioral hwf hguards replacement, ?_⟩
  let updated := Profile.update (sig := (graphModel G hwf hguards).behavioralSignature)
    profile who (CommitPolicy.behavioral hwf hguards replacement)
  have hreplace := runBehavioralFrom_update_localized_eq G hwf hguards
    hlocal hsingle profile who replacement G.nodeCount
    (toExecutionProtocol G hwf hguards).initHistory
  have hlocalized := runBehavioralFrom_localized hwf hguards
    hlocal hsingle updated G.nodeCount
    (toExecutionProtocol G hwf hguards).initHistory
  have hbehavioral :
      ((graphModel G hwf hguards).runBehavioral
          (fun player =>
            (Profile.update (sig := policySignature G)
              (fun player => CommitPolicy.fromBehavioral hwf hguards player
                (profile player)) who replacement player).behavioral hwf hguards)
          G.nodeCount).map (fun history => history.state) =
        ((graphModel G hwf hguards).runBehavioral updated G.nodeCount).map
          (fun history => history.state) := by
    change
      ((graphModel G hwf hguards).runBehavioralFrom
          (fun player =>
            (Profile.update (sig := policySignature G)
              (fun player => CommitPolicy.fromBehavioral hwf hguards player
                (profile player)) who replacement player).behavioral hwf hguards)
          G.nodeCount (toExecutionProtocol G hwf hguards).initHistory).map
            (fun history => history.state) =
        ((graphModel G hwf hguards).runBehavioralFrom updated G.nodeCount
          (toExecutionProtocol G hwf hguards).initHistory).map
            (fun history => history.state)
    rw [hreplace, hlocalized]
  change
    (runPolicyNodes hwf hguards
        (Profile.update (sig := policySignature G)
          (fun player => CommitPolicy.fromBehavioral hwf hguards player
            (profile player)) who replacement)
        ⟨Config.initial G, .initial⟩ G.nodeOrder).map (policyObserve G) = _
  have hnode := runBehavioral_eq_nodeOrder hwf hguards
    (Profile.update (sig := policySignature G)
      (fun player => CommitPolicy.fromBehavioral hwf hguards player
        (profile player)) who replacement) hsingle
  rw [← hnode]
  change FinDist.map id
      (((graphModel G hwf hguards).runBehavioral
        (fun player =>
          (Profile.update (sig := policySignature G)
            (fun player => CommitPolicy.fromBehavioral hwf hguards player
              (profile player)) who replacement player).behavioral hwf hguards)
        G.nodeCount).map (fun history => history.state)) = _
  rw [FinDist.map_id]
  change
    ((graphModel G hwf hguards).runBehavioral
      (fun player =>
        (Profile.update (sig := policySignature G)
          (fun player => CommitPolicy.fromBehavioral hwf hguards player
            (profile player)) who replacement player).behavioral hwf hguards)
      G.nodeCount).map (fun history => history.state) =
    ((graphModel G hwf hguards).runBehavioral updated G.nodeCount).map
      (fun history => history.state)
  exact hbehavioral

/-- A target canonical policy game has the same observed law as the graph's
behavioral game after compiling every behavioral policy by declared-read
localization. -/
def simulation
    (hlocal : CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : Config G) who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second) :
    MixtureSimulationOn
      (behavioralGame G hwf hguards)
      (policyGame G hwf hguards)
      (behavioralObserve G hwf hguards)
      (policyObserve G)
      (fun _ _ => True) where
  compileStrategy who policy :=
    CommitPolicy.fromBehavioral hwf hguards who policy
  honest_law profile := by
    change
      ((policyGame G hwf hguards).play
          (fun who => CommitPolicy.fromBehavioral hwf hguards who (profile who))).map id =
        ((graphModel G hwf hguards).runBehavioral profile G.nodeCount).map
          (fun history => history.state)
    rw [FinDist.map_id]
    exact policyRun_eq_behavioralRun G hwf hguards hlocal hsingle profile
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    let updated := Profile.update (sig := (graphModel G hwf hguards).behavioralSignature)
      profile who (CommitPolicy.behavioral hwf hguards replacement)
    refine ⟨FinDist.pure (CommitPolicy.behavioral hwf hguards replacement), ?_⟩
    have hbind :
        (FinDist.pure (CommitPolicy.behavioral hwf hguards replacement)).bind
            (fun alternative =>
              ((behavioralGame G hwf hguards).play
                (Profile.update (sig := (graphModel G hwf hguards).behavioralSignature)
                  profile who alternative)).map
                (behavioralObserve G hwf hguards)) =
          ((behavioralGame G hwf hguards).play updated).map
            (behavioralObserve G hwf hguards) :=
      FinDist.pure_bind _ _
    apply Eq.trans ?_ hbind.symm
    change
          FinDist.map (policyObserve G)
            ((policyGame G hwf hguards).play
            (Profile.update
              (fun player => CommitPolicy.fromBehavioral hwf hguards player
                (profile player)) who
              replacement)) =
          ((behavioralGame G hwf hguards).play
            (Profile.update (sig := (graphModel G hwf hguards).behavioralSignature)
              profile who (CommitPolicy.behavioral hwf hguards replacement))).map
            (behavioralObserve G hwf hguards)
    change
          ((policyGame G hwf hguards).play
          (Profile.update
            (fun player => CommitPolicy.fromBehavioral hwf hguards player
              (profile player)) who
            replacement)).map
          (policyObserve G) =
        ((behavioralGame G hwf hguards).play updated).map
          (behavioralObserve G hwf hguards)
    change
      FinDist.map id
        ((policyGame G hwf hguards).play
          (Profile.update
            (fun player => CommitPolicy.fromBehavioral hwf hguards player
              (profile player)) who replacement)) = _
    rw [FinDist.map_id]
    change
      runPolicyNodes hwf hguards
          (Profile.update
            (fun player => CommitPolicy.fromBehavioral hwf hguards player
              (profile player)) who
            replacement)
          ⟨Config.initial G, .initial⟩ G.nodeOrder = _
    have hnode := runBehavioral_eq_nodeOrder hwf hguards
      (Profile.update (sig := policySignature G)
        (fun player => CommitPolicy.fromBehavioral hwf hguards player
          (profile player)) who replacement) hsingle
    have hreplace := runBehavioralFrom_update_localized_eq G hwf hguards
      hlocal hsingle profile who replacement G.nodeCount
      (toExecutionProtocol G hwf hguards).initHistory
    have hlocalized := runBehavioralFrom_localized hwf hguards
      hlocal hsingle updated G.nodeCount
      (toExecutionProtocol G hwf hguards).initHistory
    have hbehavioral :
        ((graphModel G hwf hguards).runBehavioral
          (fun player =>
            (Profile.update (sig := policySignature G)
              (fun player => CommitPolicy.fromBehavioral hwf hguards player
                (profile player)) who replacement player).behavioral hwf hguards)
          G.nodeCount).map (fun history => history.state) =
        ((graphModel G hwf hguards).runBehavioral updated G.nodeCount).map
          (fun history => history.state) := by
      change
        ((graphModel G hwf hguards).runBehavioralFrom
          (fun player =>
            (Profile.update (sig := policySignature G)
              (fun player => CommitPolicy.fromBehavioral hwf hguards player
                (profile player)) who replacement player).behavioral hwf hguards)
          G.nodeCount (toExecutionProtocol G hwf hguards).initHistory).map
            (fun history => history.state) =
          ((graphModel G hwf hguards).runBehavioralFrom updated G.nodeCount
            (toExecutionProtocol G hwf hguards).initHistory).map
            (fun history => history.state)
      rw [hreplace, hlocalized]
    have hresult := hnode.symm
    rw [hbehavioral] at hresult
    change
      runPolicyNodes hwf hguards
          (Profile.update
            (fun player => CommitPolicy.fromBehavioral hwf hguards player
              (profile player)) who replacement)
          ⟨Config.initial G, .initial⟩ G.nodeOrder =
        ((graphModel G hwf hguards).runBehavioral updated G.nodeCount).map
          (fun history => history.state)
    exact hresult

/-! ## Equilibrium consequence -/

theorem isεNash_compileProfile_iff
    (hlocal : CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : Config G) who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second)
    (value : ReachableConfig G → Player → ℝ) (ε : ℝ)
    (profile : Profile (graphModel G hwf hguards).behavioralSignature) :
    IsεNash (policyGame G hwf hguards)
      (fun outcome who => value (policyObserve G outcome) who) ε
      ((simulation G hwf hguards hlocal hsingle).compileProfile profile) ↔
      IsεNash (behavioralGame G hwf hguards)
        (fun outcome who => value (behavioralObserve G hwf hguards outcome) who) ε profile :=
  (simulation G hwf hguards hlocal hsingle).isεNash_compileProfile_iff value ε profile
    (fun _ _ => trivial)

end Strategic

end Vegas.EventGraph

/- Guard the strategic bridge independently of the paper audit surface. -/
/-- info: 'Vegas.EventGraph.Strategic.simulation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Strategic.simulation

/-- info: 'Vegas.EventGraph.Strategic.isεNash_compileProfile_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Strategic.isεNash_compileProfile_iff
