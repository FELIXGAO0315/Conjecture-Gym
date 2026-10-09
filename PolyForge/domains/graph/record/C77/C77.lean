import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C77 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsTree) (hn1 : (Fintype.card V : ℤ) ≤ 6) (hn2 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≤ 0) :
    2 * (G.maxDegree : ℤ) ≤ 2 * (Fintype.card V : ℤ) + (G.vertexCoverNum.toNat : ℤ) - 3 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G (isTree_connected G hp2) hp1
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s2, s1, s3, s4]
  have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s7 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s8 : 4 * (Fintype.card V : ℤ) - 4 * (G.maxDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by linarith [s1, s6, s7, s4]
  have s9 : 2 * (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hr := s8; omega
  linarith [s9]
