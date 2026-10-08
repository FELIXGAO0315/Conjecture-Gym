import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C10 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsTree) (hn1 : -(G.minDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    2 * (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp2)
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s4 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G (isTree_connected G hp2) hp1
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s2, s3, s4, s5]
  have s7 : -(G.minDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s8 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s4, s7]
  have s9 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s8; omega
  have s10 : 2 * (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s1, s6, s9]
  linarith [s10]
