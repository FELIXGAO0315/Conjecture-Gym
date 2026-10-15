import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C208 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.maxDegree : ℤ) ≥ 3) :
    (Fintype.card V : ℤ) ≥ 2 * (G.diam : ℤ) - 3 * (G.radius.toNat : ℤ) + 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) ≥ 3 := by linarith [hn1]
  have s5 : 2 * (Fintype.card V : ℤ) - 4 * (G.diam : ℤ) + 6 * (G.radius.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3, s4]
  have s6 : (Fintype.card V : ℤ) - 2 * (G.diam : ℤ) + 3 * (G.radius.toNat : ℤ) ≥ 3 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
