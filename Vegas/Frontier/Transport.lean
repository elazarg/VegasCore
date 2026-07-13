import Vegas.Frontier.Games
import GameTheory.Concepts.Foundations.GameMorphism

/-!
# Frontier game transport

Program-level EU-preserving maps between compiled frontier games.

The compiler exposes game semantics through frontier kernel games. Transport
therefore lives at that level: a morphism maps each player's strategy carrier
and preserves expected utility under the mapped profile.
-/

namespace Vegas

open GameTheory

namespace Machine
namespace RoundView

variable {Player : Type} {M : Machine Player}

/-- Embed one legal pure strategy as the degenerate behavioral strategy that
plays the chosen move with probability one at every information state. -/
noncomputable def legalPureStrategyToBehavioral
    (view : M.RoundView) (horizon : Nat) (player : Player)
    (strategy : view.BoundedPureStrategy horizon player) :
    view.BoundedBehavioralStrategy horizon player :=
  ⟨fun info => PMF.pure (strategy.1 info), by
    intro history move hmove
    rw [PMF.support_pure, Set.mem_singleton_iff] at hmove
    subst move
    exact strategy.2 history⟩

@[simp] theorem legalPureStrategyToBehavioral_apply
    (view : M.RoundView) (horizon : Nat) (player : Player)
    (strategy : view.BoundedPureStrategy horizon player)
    (info : view.ReachableInfoState horizon player) :
    (view.legalPureStrategyToBehavioral horizon player strategy).1 info =
      PMF.pure (strategy.1 info) := rfl

theorem legalPureToBehavioral_eq_strategyMap
    (view : M.RoundView) (horizon : Nat)
    (profile : view.BoundedPureProfile horizon) :
    view.legalPureToBehavioral horizon profile =
      fun player =>
        view.legalPureStrategyToBehavioral horizon player
          (profile player) := by
  funext player
  apply Subtype.ext
  funext info
  rfl

end RoundView
end Machine

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P]
variable {L L₁ L₂ : IExpr}

/-! ## Same-program pure-to-behavioral embedding -/

/-- Pure frontier strategies embedded as degenerate behavioral frontier
strategies. -/
noncomputable def pureFrontierStrategyToBehavioral
    (program : WFProgram P L) [FiniteDomains program] (player : P)
    (strategy : program.PureFrontierStrategy player) :
    program.BehavioralFrontierStrategy player :=
  (program.frontierSemantics.behavioral.view)
    |>.legalPureStrategyToBehavioral program.frontierSemantics.horizon
      player strategy

@[simp] theorem pureFrontierStrategyToBehavioral_apply
    (program : WFProgram P L) [FiniteDomains program] (player : P)
    (strategy : program.PureFrontierStrategy player)
    (info :
      (program.frontierSemantics.behavioral.view).ReachableInfoState
        program.frontierSemantics.horizon player) :
    (program.pureFrontierStrategyToBehavioral player strategy).1 info =
      PMF.pure (strategy.1 info) := rfl

theorem pureFrontierProfileToBehavioral_eq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    (fun player =>
        program.pureFrontierStrategyToBehavioral player
          (profile player)) =
      (program.frontierSemantics.behavioral.view).legalPureToBehavioral
        program.frontierSemantics.horizon profile := by
  rw [Machine.RoundView.legalPureToBehavioral_eq_strategyMap]
  rfl

/-- The pure-to-behavioral embedding is an EU-preserving morphism from the
completed pure frontier game to the completed behavioral frontier game. -/
noncomputable def pureToBehavioralFrontierMorphism
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.EUMorphism
      program.pureFrontierGame program.behavioralFrontierGame where
  stratMap := fun player =>
    program.pureFrontierStrategyToBehavioral player
  udist_preserved := by
    intro profile
    have hprofile := program.pureFrontierProfileToBehavioral_eq profile
    rw [hprofile]
    exact program.pureToBehavioralFrontierUdist profile
  eu_preserved := by
    intro profile player
    have hprofile := program.pureFrontierProfileToBehavioral_eq profile
    rw [hprofile]
    change
      Math.Probability.expect
          (program.behavioralFrontierGame.outcomeKernel
            ((program.frontierSemantics.behavioral.view)
              |>.legalPureToBehavioral
                program.frontierSemantics.horizon profile))
          (fun outcome =>
            program.behavioralFrontierGame.utility outcome player) =
        Math.Probability.expect
          (program.pureFrontierGame.outcomeKernel profile)
          (fun outcome =>
            program.pureFrontierGame.utility outcome player)
    rw [program.pureToBehavioralFrontierOutcomeKernel profile]
    rfl

/-- If the pure profile's degenerate behavioral embedding is Nash, then the
pure profile is Nash. -/
theorem pureFrontier_nash_of_behavioral_embedding_nash
    (program : WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash :
      program.BehavioralFrontierNash
        (fun player =>
          program.pureFrontierStrategyToBehavioral player
            (profile player))) :
    program.PureFrontierNash profile := by
  simpa [pureToBehavioralFrontierMorphism, PureFrontierNash,
    BehavioralFrontierNash] using
    (program.pureToBehavioralFrontierMorphism).nash_of_nash hNash

/-! ## Program-to-program transport -/

/-- EU-preserving morphism between completed pure frontier games. -/
abbrev PureFrontierMorphism
    (source : WFProgram P L₁) [FiniteDomains source]
    (target : WFProgram P L₂) [FiniteDomains target] : Type :=
  KernelGame.EUMorphism
    source.pureFrontierGame target.pureFrontierGame

namespace PureFrontierMorphism

variable {source : WFProgram P L₁} [FiniteDomains source]
variable {target : WFProgram P L₂} [FiniteDomains target]

/-- Map a pure frontier profile along an EU-preserving morphism. -/
def mapProfile
    (F : PureFrontierMorphism source target)
    (profile : source.PureFrontierProfile) :
    target.PureFrontierProfile :=
  fun player => F.stratMap player (profile player)

@[simp] theorem mapProfile_apply
    (F : PureFrontierMorphism source target)
    (profile : source.PureFrontierProfile) (player : P) :
    F.mapProfile profile player =
      F.stratMap player (profile player) := rfl

/-- Mapped pure frontier profiles preserve expected utility. -/
theorem mapProfile_eu_eq
    (F : PureFrontierMorphism source target)
    (profile : source.PureFrontierProfile) (player : P) :
    target.pureFrontierEU (F.mapProfile profile) player =
      source.pureFrontierEU profile player :=
  F.eu_preserved profile player

/-- Nash pulls back along an EU-preserving pure frontier morphism. -/
theorem source_nash_of_target_mapped_nash
    (F : PureFrontierMorphism source target)
    {profile : source.PureFrontierProfile}
    (hNash : target.PureFrontierNash (F.mapProfile profile)) :
    source.PureFrontierNash profile := by
  simpa [PureFrontierNash, mapProfile] using
    F.nash_of_nash hNash

end PureFrontierMorphism

/-- EU-preserving morphism between completed behavioral frontier games. -/
abbrev BehavioralFrontierMorphism
    (source : WFProgram P L₁) [FiniteDomains source]
    (target : WFProgram P L₂) [FiniteDomains target] : Type :=
  KernelGame.EUMorphism
    source.behavioralFrontierGame target.behavioralFrontierGame

namespace BehavioralFrontierMorphism

variable {source : WFProgram P L₁} [FiniteDomains source]
variable {target : WFProgram P L₂} [FiniteDomains target]

/-- Map a behavioral frontier profile along an EU-preserving morphism. -/
def mapProfile
    (F : BehavioralFrontierMorphism source target)
    (profile : source.BehavioralFrontierProfile) :
    target.BehavioralFrontierProfile :=
  fun player => F.stratMap player (profile player)

@[simp] theorem mapProfile_apply
    (F : BehavioralFrontierMorphism source target)
    (profile : source.BehavioralFrontierProfile) (player : P) :
    F.mapProfile profile player =
      F.stratMap player (profile player) := rfl

/-- Mapped behavioral frontier profiles preserve expected utility. -/
theorem mapProfile_eu_eq
    (F : BehavioralFrontierMorphism source target)
    (profile : source.BehavioralFrontierProfile) (player : P) :
    target.behavioralFrontierEU (F.mapProfile profile) player =
      source.behavioralFrontierEU profile player :=
  F.eu_preserved profile player

/-- Nash pulls back along an EU-preserving behavioral frontier morphism. -/
theorem source_nash_of_target_mapped_nash
    (F : BehavioralFrontierMorphism source target)
    {profile : source.BehavioralFrontierProfile}
    (hNash :
      target.BehavioralFrontierNash (F.mapProfile profile)) :
    source.BehavioralFrontierNash profile := by
  simpa [BehavioralFrontierNash, mapProfile] using
    F.nash_of_nash hNash

end BehavioralFrontierMorphism

/-- EU-preserving isomorphism between completed pure frontier games. -/
abbrev PureFrontierIsomorphism
    (left : WFProgram P L₁) [FiniteDomains left]
    (right : WFProgram P L₂) [FiniteDomains right] : Type :=
  KernelGame.EUGameIsomorphism
    left.pureFrontierGame right.pureFrontierGame

namespace PureFrontierIsomorphism

variable {left : WFProgram P L₁} [FiniteDomains left]
variable {right : WFProgram P L₂} [FiniteDomains right]

/-- Map a pure frontier profile along an EU-preserving isomorphism. -/
def mapProfile
    (F : PureFrontierIsomorphism left right)
    (profile : left.PureFrontierProfile) :
    right.PureFrontierProfile :=
  fun player => F.stratEquiv player (profile player)

@[simp] theorem mapProfile_apply
    (F : PureFrontierIsomorphism left right)
    (profile : left.PureFrontierProfile) (player : P) :
    F.mapProfile profile player =
      F.stratEquiv player (profile player) := rfl

/-- Pure frontier Nash is invariant under an EU-preserving isomorphism. -/
theorem nash_iff
    (F : PureFrontierIsomorphism left right)
    (profile : left.PureFrontierProfile) :
    left.PureFrontierNash profile ↔
      right.PureFrontierNash (F.mapProfile profile) := by
  exact
    GameTheory.KernelGame.EUGameIsomorphism.nash_iff F profile

end PureFrontierIsomorphism

/-- EU-preserving isomorphism between completed behavioral frontier games. -/
abbrev BehavioralFrontierIsomorphism
    (left : WFProgram P L₁) [FiniteDomains left]
    (right : WFProgram P L₂) [FiniteDomains right] : Type :=
  KernelGame.EUGameIsomorphism
    left.behavioralFrontierGame right.behavioralFrontierGame

namespace BehavioralFrontierIsomorphism

variable {left : WFProgram P L₁} [FiniteDomains left]
variable {right : WFProgram P L₂} [FiniteDomains right]

/-- Map a behavioral frontier profile along an EU-preserving isomorphism. -/
def mapProfile
    (F : BehavioralFrontierIsomorphism left right)
    (profile : left.BehavioralFrontierProfile) :
    right.BehavioralFrontierProfile :=
  fun player => F.stratEquiv player (profile player)

@[simp] theorem mapProfile_apply
    (F : BehavioralFrontierIsomorphism left right)
    (profile : left.BehavioralFrontierProfile) (player : P) :
    F.mapProfile profile player =
      F.stratEquiv player (profile player) := rfl

/-- Behavioral frontier Nash is invariant under an EU-preserving isomorphism. -/
theorem nash_iff
    (F : BehavioralFrontierIsomorphism left right)
    (profile : left.BehavioralFrontierProfile) :
    left.BehavioralFrontierNash profile ↔
      right.BehavioralFrontierNash (F.mapProfile profile) := by
  exact
    GameTheory.KernelGame.EUGameIsomorphism.nash_iff F profile

end BehavioralFrontierIsomorphism

end WFProgram

end Vegas
