import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C63 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.IsAcyclic) (hn1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≤ 0) (hn2 : (G.maxDegree : ℤ) ≥ 6) :
    2 * (G.edgeFinset.card : ℤ) ≥ -(G.maxDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) + 20 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) ≥ 6 := by linarith [hn2]
  have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 7 := by linarith [s1, s2, s3]
  have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s5, s6]
  have s8 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s7; omega
  have s9 : 2 * (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 20 := by linarith [s4, s2, s8, s3]
  linarith [s9]
