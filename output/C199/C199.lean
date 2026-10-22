import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C199 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.cliqueNum : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (Fintype.card V : ℤ) ≥ 2 * (G.diam : ℤ) - 3 * (G.radius.toNat : ℤ) + 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
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
  have s4 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : 4 * (Fintype.card V : ℤ) - 8 * (G.diam : ℤ) + 12 * (G.radius.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3, s4, s5]
  have s7 : (Fintype.card V : ℤ) - 2 * (G.diam : ℤ) + 3 * (G.radius.toNat : ℤ) ≥ 2 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
