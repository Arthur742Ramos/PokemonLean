-- PokemonLean: Formal verification of the Pokémon Trading Card Game
-- This module serves as the root of the `PokemonLean` library.
-- Import modules here that should be built as part of the library.

-- Core modules
import PokemonLean.Core.Types
import PokemonLean.Core.Card

-- Top-level modules
import PokemonLean.Basic
import PokemonLean.Cards
import PokemonLean.CardEffects
import PokemonLean.Corpus
import PokemonLean.Solver
import PokemonLean.GameTheory
import PokemonLean.Semantics
import PokemonLean.SemanticsDeep
import PokemonLean.BoardState
import PokemonLean.DamageCounters
import PokemonLean.Matchup
import PokemonLean.TrainerSystem
import PokemonLean.DeckBuilding
import PokemonLean.ACESpec
import PokemonLean.Win
import PokemonLean.Planner
import PokemonLean.Switching
import PokemonLean.Rotation
import PokemonLean.Format
import PokemonLean.Abilities
import PokemonLean.Decks
import PokemonLean.Prizes
import PokemonLean.StatusEffects
import PokemonLean.TypeChart
import PokemonLean.EnergyManagement
import PokemonLean.EnergyAcceleration
import PokemonLean.Replay
import PokemonLean.Stadium
import PokemonLean.LostZone
import PokemonLean.LostZoneThresholds
import PokemonLean.LostZoneBox
import PokemonLean.LostZoneCombos
import PokemonLean.TournamentRules
import PokemonLean.HandManagement
import PokemonLean.Archetypes
import PokemonLean.ArchetypeMatchups
import PokemonLean.RetreatMechanics
import PokemonLean.HandDisruption
import PokemonLean.PrizeDenial
import PokemonLean.TurnStructure
import PokemonLean.DeckConstraints
import PokemonLean.GXAttacks
import PokemonLean.Probability
import PokemonLean.AbilitySystem
import PokemonLean.AncientTrait
import PokemonLean.CardPool
import PokemonLean.Evolution
import PokemonLean.MixedStrategy
import PokemonLean.Mulligan
import PokemonLean.PrizeCards
import PokemonLean.SpecialConditions
import PokemonLean.TrainerCards
import PokemonLean.VSTAR
import PokemonLean.Deck
import PokemonLean.Tournament
