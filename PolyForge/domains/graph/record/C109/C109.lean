import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C109 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : -(G.indepNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0) :
    (G.indepNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s5 : -(G.indepNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int G (by omega)
    linarith [hw]
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s8 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s5, s6, s7]
  have s9 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s8; omega
  have s10 : (G.indepNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s4, s9]
  linarith [s10]
