import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C261 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    3 * (Fintype.card V : ℤ) ≥ 2 * (G.indepNum : ℤ) + 10 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) = 3 := by
    have hw := regular_max_int' G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : 3 * (Fintype.card V : ℤ) + 6 * (G.vertexCoverNum.toNat : ℤ) ≥ 28 := by linarith [s1, s2, s3, s4]
  have s6 : (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 10 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s6, heq_gallai, heq_rege, heq_regx, heq_regn]
