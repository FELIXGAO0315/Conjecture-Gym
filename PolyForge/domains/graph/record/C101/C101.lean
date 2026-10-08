import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C101 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.IsBipartite) (hn1 : -2 * (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ 0) :
    -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≤ -1 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -2 * (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s8 : -2 * (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [s5, s6, s7, s2]
  have s9 : -(G.vertexCoverNum.toNat : ℤ) ≥ 0 := by have hr := s8; omega
  have s10 : (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s4, s9]
  linarith [s10]
