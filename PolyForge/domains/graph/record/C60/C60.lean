import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C60 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hp2 : G.IsTree) (hn1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≤ 0) :
    (G.radius.toNat : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) + (G.diam : ℤ) - 2 := by
  have s1 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := radius_le_diam_int G (isTree_connected G hp2)
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int G (by omega)
    linarith [hw]
  have s8 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s6, s7]
  have s9 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s8; omega
  have s10 : 2 * (G.edgeFinset.card : ℤ) + (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 2 := by linarith [s1, s9, s3]
  linarith [s10]
