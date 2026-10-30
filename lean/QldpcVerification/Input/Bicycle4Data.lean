import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin

/-! Generated from 4-2-2.json. Input SHA256: f33485dfd3c2d3782d358b5050fba2b476d78f0e0b1d38dc0582622102b9ed71 -/

namespace QldpcVerification.Bicycle4Data

def nq : Nat := 4
def cyclicLength : Nat := 2
def target : Nat := 2

def hx : List (Finset (Fin 4)) := [
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩},
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩}]

def wx : Nat := 9

def detx : Nat := 5

def hz : List (Finset (Fin 4)) := [
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩},
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩}]

def wz : Nat := 9

def detz : Nat := 5

end QldpcVerification.Bicycle4Data
