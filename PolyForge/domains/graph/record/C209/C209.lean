import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C209 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    (Fintype.card V : ℤ) ≤ 6 * (G.indepNum : ℤ) - 2 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
  have s4 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s1]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
    have hw := regular_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s6 : 2 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 6 * (G.indepNum : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5]
  have s7 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) ≥ 1 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s7, heq_gallai, heq_rege, heq_regx, heq_regn]
