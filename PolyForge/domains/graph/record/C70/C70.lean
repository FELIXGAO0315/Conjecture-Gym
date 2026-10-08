import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C70 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : 2 * (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 9 := by
  have s1 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    linarith [hw]
  have s2 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp2 hp1
    linarith [hw]
  have s3 : (G.diam : ℤ) ≥ 1 := by linarith [s2, s1]
  have s4 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s5 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s4, s2, s1]
  have s6 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s5; omega
  have s7 : (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 9 := by linarith [s1, s3, s6]
  linarith [s7]
