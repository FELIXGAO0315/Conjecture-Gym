import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C23 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 2 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s3 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := radius_le_diam_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (G.radius.toNat : ℤ) ≥ 1 := by
    have hw := radius_ge_one_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G hp1
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s3, s4, s5]
  have s7 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s6]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : -(Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -2 := by linarith [s1, s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]
