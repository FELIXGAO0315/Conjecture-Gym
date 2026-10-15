import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C193 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (Fintype.card V : ℤ) ≤ 6) :
    (G.indepNum : ℤ) ≥ 3 * (G.edgeFinset.card : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) - 20 := by
  have s1 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := bipartite_four_mul_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn1]
  have s5 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (6 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -(G.edgeFinset.card : ℤ) ≥ -9 := by linarith [s1, s4, s5]
  have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s11 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s13 : -(G.indepNum : ℤ) ≥ -6 := by linarith [s11, s4, s12]
  have s14 : 6 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ (6 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s13]) (by linarith [s10])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s15 : -33 * (G.edgeFinset.card : ℤ) + 22 * (G.chromaticNumber.toNat : ℤ) + 11 * (G.indepNum : ℤ) ≥ -229 := by linarith [s1, s2, s5, s8, s9, s14]
  have s16 : -3 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ -20 := by have hr := s15; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s16, heq_gallai]
