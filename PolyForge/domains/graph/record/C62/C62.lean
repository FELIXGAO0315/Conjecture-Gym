import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C62 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hp2 : G.IsAcyclic) (hn1 : (Fintype.card V : ℤ) ≥ 2) (hn2 : (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≤ 0) :
    (Fintype.card V : ℤ) ≥ -2 * (G.vertexCoverNum.toNat : ℤ) + 4 := by
  have s1 : (Fintype.card V : ℤ) ≥ 2 := by linarith [hn1]
  have s2 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s3 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s1, s5]
  linarith [s6]
