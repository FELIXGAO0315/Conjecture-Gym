import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C28 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≤ 0) (hn2 : (G.cliqueNum : ℤ) ≥ 3) :
    (G.cliqueNum : ℤ) ≥ -2 * (G.indepNum : ℤ) + 7 := by
  have s1 : (G.cliqueNum : ℤ) ≥ 3 := by linarith [hn2]
  have s2 : -(G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 2 := by have hr := s3; omega
  have s5 : (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s1, s4]
  linarith [s5]
