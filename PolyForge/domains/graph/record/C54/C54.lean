import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C54 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 0) (hn2 : (G.indepNum : ℤ) ≤ 5) :
    -(G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) ≤ 4 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s3 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(G.indepNum : ℤ) ≥ -5 := by linarith [hn2]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s6 : 2 * (G.edgeFinset.card : ℤ) - 4 * (G.indepNum : ℤ) ≥ -15 := by linarith [s1, s2, s3, s4, s5]
  have s7 : (G.edgeFinset.card : ℤ) - 2 * (G.indepNum : ℤ) ≥ -7 := by have hr := s6; omega
  have s8 : 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) - 6 * (G.indepNum : ℤ) ≥ -14 := by linarith [s1, s2, s3, s7, s5]
  have s9 : (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) - 2 * (G.indepNum : ℤ) ≥ -4 := by have hr := s8; omega
  linarith [s9]
