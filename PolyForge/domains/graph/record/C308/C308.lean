import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C308 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (G.indepNum : ℤ) ≥ 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : (G.maxDegree : ℤ) = 2 := by
    have hw := regular_max_int' G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (G.minDegree : ℤ) = 2 := by
    have hw := regular_min_int' G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s1, s2, s3, s4]
  have s6 : (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 4 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s6, heq_gallai, heq_rege, heq_regx, heq_regn]
