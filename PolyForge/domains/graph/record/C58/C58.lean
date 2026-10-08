import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C58 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : -(G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0) (hn2 : (G.minDegree : ℤ) ≥ 3) :
    2 * (G.maxDegree : ℤ) - (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by
  have s1 : (G.minDegree : ℤ) ≥ 3 := by linarith [hn2]
  have s2 : -(G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 2 := by have hr := s3; omega
  have s5 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s6 : 2 * (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 3 := by linarith [s5, s1]
  have s7 : 2 * (G.maxDegree : ℤ) - (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s4, s6]
  linarith [s7]
