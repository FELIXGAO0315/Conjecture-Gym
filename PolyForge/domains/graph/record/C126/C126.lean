import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C126 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.girth : ℤ) ≤ 4) (hn2 : -2 * (G.minDegree : ℤ) + (G.girth : ℤ) ≥ 0) :
    -(G.minDegree : ℤ) + 2 * (G.girth : ℤ) ≥ 5 := by
  have s1 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    linarith [hw]
  have s2 : -2 * (G.minDegree : ℤ) + (G.girth : ℤ) ≥ 0 := by linarith [hn2]
  have s3 : -2 * (G.minDegree : ℤ) + 4 * (G.girth : ℤ) ≥ 9 := by linarith [s1, s2]
  have s4 : -(G.minDegree : ℤ) + 2 * (G.girth : ℤ) ≥ 5 := by have hr := s3; omega
  linarith [s4]
