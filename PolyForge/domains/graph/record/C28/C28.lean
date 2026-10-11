import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C28 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := radius_le_diam_int G hp1
    try push_cast at hw
    linarith [hw]
  have s7 : (G.radius.toNat : ℤ) ≥ 1 := by
    have hw := radius_ge_one_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G hp1
    try push_cast at hw
    linarith [hw]
  have s9 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s6, s7, s8]
  have s10 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s9]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : -(Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by linarith [s1, s4, s5, s10]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]
