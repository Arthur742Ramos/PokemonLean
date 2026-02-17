-- PokemonLean: Formal verification of the Pokémon Trading Card Game
-- Core foundation modules
import PokemonLean.Core.Types
import PokemonLean.Core.Card
import PokemonLean.Core.GameState
import PokemonLean.Core.DamageCalc
import PokemonLean.Core.Evolution
import PokemonLean.Core.SpecialConditions
import PokemonLean.Core.WinCondition
import PokemonLean.Core.RuleBox
import PokemonLean.Core.Trainers
import PokemonLean.Core.EnergySystem
import PokemonLean.Core.Retreat
import PokemonLean.Core.Setup
import PokemonLean.Core.TurnLoop
import PokemonLean.Core.AttackResolution
import PokemonLean.Core.GameLoop
import PokemonLean.Core.Solver
import PokemonLean.Core.DeckChecker
import PokemonLean.Core.PrizeTrade
import PokemonLean.Core.Interaction
import PokemonLean.Core.BattleStyles
import PokemonLean.Core.Paradox
import PokemonLean.Core.CoinFlip
import PokemonLean.Core.AbilityTiming
import PokemonLean.Core.Tournament
import PokemonLean.Core.FormatChecker
import PokemonLean.Core.CardDatabase
-- Consolidated modules (Armada 531)
import PokemonLean.Core.Abilities
import PokemonLean.Core.SpecialMechanics
import PokemonLean.Core.Strategy
-- Digital variants (Armada 535)
import PokemonLean.Core.Pocket
import PokemonLean.Core.PocketBattle
import PokemonLean.Core.LiveFormat
-- Competitive analysis layer (Armada 536)
import PokemonLean.Core.Metagame
import PokemonLean.Core.SideDeck
import PokemonLean.Core.HistoricalFormats
import PokemonLean.Core.LostZoneDeck
import PokemonLean.Core.CharizardDeck
import PokemonLean.Core.ControlDeck
-- SV era, rulings, deep energy (Armada 543)
import PokemonLean.Core.ScarletViolet
import PokemonLean.Core.RulingEdgeCases
import PokemonLean.Core.EnergySystemDeep
-- Deep game systems (Armada 546)
import PokemonLean.Core.AbilityInteraction
import PokemonLean.Core.ItemAndTool
import PokemonLean.Core.BenchMechanics
-- Matchup/resource/turn deep analysis (Armada 551)
import PokemonLean.Core.MatchupAnalysis
import PokemonLean.Core.ResourceManagement
import PokemonLean.Core.TurnStructure
-- Stadium, Supporters, Prizes (Armada 547)
import PokemonLean.Core.StadiumCards
import PokemonLean.Core.SupporterCards
import PokemonLean.Core.PrizeMapping
