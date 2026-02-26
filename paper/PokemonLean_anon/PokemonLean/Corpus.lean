import PokemonLean.Cards

namespace PokemonLean.Corpus

open PokemonLean

def cardWellFormed (card : Card) : Prop :=
  card.hp > 0 ∧ card.attacks.length > 0

def corpusWellFormed : Prop :=
  ∀ card ∈ PokemonLean.Cards.corpus, cardWellFormed card

theorem corpusWellFormed_trivial : corpusWellFormed := by
  intro card hIn
  simp [PokemonLean.Cards.corpus] at hIn
  rcases hIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [PokemonLean.Cards.scatterbug, cardWellFormed]
  · simp [PokemonLean.Cards.pineco, cardWellFormed]
  · simp [PokemonLean.Cards.cacturne, cardWellFormed]
  · simp [PokemonLean.Cards.gogoat, cardWellFormed]
  · simp [PokemonLean.Cards.sprigatito, cardWellFormed]
  · simp [PokemonLean.Cards.meowscarada, cardWellFormed]
  · simp [PokemonLean.Cards.tarountula, cardWellFormed]
  · simp [PokemonLean.Cards.tarountula2, cardWellFormed]
  · simp [PokemonLean.Cards.smoliv, cardWellFormed]
  · simp [PokemonLean.Cards.smoliv2, cardWellFormed]

end PokemonLean.Corpus
