import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C27 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsEdgeConnected 1) (hn1 : (G.indepNum : ℤ) ≤ 1) :
    (G.minDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) - 5 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := edge_conn_min_deg_int G hp2 hp1
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.indepNum : ℤ) ≥ -1 := by linarith [hn1]
  have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s5]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3, s4, s5, s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]
