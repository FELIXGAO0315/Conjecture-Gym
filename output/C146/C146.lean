import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C146 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (G.cliqueNum : ℤ) ≥ (G.indepNum : ℤ)) :
    (Fintype.card V : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 6 := by
  have s1 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : (G.maxDegree : ℤ) = 2 := by
    have hw := regular_max_int' G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.indepNum : ℤ) ≥ -3 := by linarith [s2, s3, s4]
  have s6 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s7, s4]
  have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s10 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hmul : (0 : ℤ) ≤ (3 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s5]) (by linarith [s9])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s6, s8, s1, s3, s10]
  have s12 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s11; omega
  have s13 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ (3 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
      mul_nonneg (by linarith [s5]) (by linarith [s12])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s15 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 6 := by linarith [s1, s13, s14]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s15, heq_gallai, heq_rege, heq_regx, heq_regn]
