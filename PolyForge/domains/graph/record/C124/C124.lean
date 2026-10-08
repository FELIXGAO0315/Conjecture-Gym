import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C124 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 3) (hn2 : (G.maxDegree : ℤ) ≥ 4) :
    (G.maxDegree : ℤ) + (G.radius.toNat : ℤ) ≥ 6 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) ≥ 4 := by linarith [hn2]
  have s3 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
  have s4 : 2 * (G.maxDegree : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 11 := by linarith [s1, s2, s3]
  have s5 : (G.maxDegree : ℤ) + (G.radius.toNat : ℤ) ≥ 6 := by have hr := s4; omega
  linarith [s5]
