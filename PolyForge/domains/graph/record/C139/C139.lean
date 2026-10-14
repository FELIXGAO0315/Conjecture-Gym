import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C139 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.cliqueNum : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ 2 * (G.diam : ℤ) - 3 * (G.radius.toNat : ℤ) + 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
    have hw := connected_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G hp1
    try push_cast at hw
    linarith [hw]
  have s6 : 2 * (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : 4 * (G.edgeFinset.card : ℤ) - 8 * (G.diam : ℤ) + 12 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5, s6]
  have s8 : (G.edgeFinset.card : ℤ) - 2 * (G.diam : ℤ) + 3 * (G.radius.toNat : ℤ) ≥ 1 := by have hr := s7; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]
