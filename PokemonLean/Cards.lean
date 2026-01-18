-- Auto-generated from Pokémon TCG API
-- Do not edit manually

import PokemonLean.Basic

namespace PokemonLean.Cards

def scatterbug : Card :=
  { name := "Scatterbug"
  , hp := 30
  , energyType := .grass
  , attacks := [{ name := "Tackle", baseDamage := 20, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def pineco : Card :=
  { name := "Pineco"
  , hp := 60
  , energyType := .grass
  , attacks := [{ name := "Guard Press", baseDamage := 10, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def cacturne : Card :=
  { name := "Cacturne"
  , hp := 130
  , energyType := .grass
  , attacks := [{ name := "Spike Shot", baseDamage := 110, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def gogoat : Card :=
  { name := "Gogoat"
  , hp := 130
  , energyType := .grass
  , attacks := [{ name := "Rising Lunge", baseDamage := 30, effects := [] }, { name := "Solar Beam", baseDamage := 110, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def sprigatito : Card :=
  { name := "Sprigatito"
  , hp := 70
  , energyType := .grass
  , attacks := [{ name := "Scratch", baseDamage := 10, effects := [] }, { name := "Leafage", baseDamage := 20, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def meowscarada : Card :=
  { name := "Meowscarada"
  , hp := 160
  , energyType := .grass
  , attacks := [{ name := "Trick Cape", baseDamage := 40, effects := [] }, { name := "Flower Blast", baseDamage := 130, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def tarountula : Card :=
  { name := "Tarountula"
  , hp := 40
  , energyType := .grass
  , attacks := [{ name := "String Haul", baseDamage := 0, effects := [] }, { name := "Bug Bite", baseDamage := 10, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def tarountula2 : Card :=
  { name := "Tarountula"
  , hp := 60
  , energyType := .grass
  , attacks := [{ name := "Surprise Attack", baseDamage := 30, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def smoliv : Card :=
  { name := "Smoliv"
  , hp := 50
  , energyType := .grass
  , attacks := [{ name := "Tackle", baseDamage := 30, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

def smoliv2 : Card :=
  { name := "Smoliv"
  , hp := 60
  , energyType := .grass
  , attacks := [{ name := "Nutrients", baseDamage := 0, effects := [] }, { name := "Spray Fluid", baseDamage := 20, effects := [] }]
  , weakness := some { energyType := .fire }
  , resistance := none }

end PokemonLean.Cards
