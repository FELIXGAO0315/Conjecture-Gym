import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C17 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.minDegree : ℤ) ≤ 3) (hn2 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≤ 0) :
    (G.vertexCoverNum.toNat : ℤ) ≥ -2 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 7 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s5 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s6 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int G (by omega)
    linarith [hw]
  have s7 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s4, s5, s6]
  have s8 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s7; omega
  have s9 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s4, s5]
  have s10 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s9; omega
  have s11 : 2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s8, s10, s2]
  linarith [s11]
