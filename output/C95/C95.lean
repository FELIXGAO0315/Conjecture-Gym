import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C95 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.indepNum : ℤ)) (hn2 : (G.indepNum : ℤ) ≤ 2) :
    (Fintype.card V : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 4 := by
  have s1 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.indepNum : ℤ) ≥ -2 := by linarith [hn2]
  have s3 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s2]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s3, s1, s4, s6]
  have s8 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s7; omega
  have s9 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
      mul_nonneg (by linarith [s2]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s11 : (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s1, s9, s10]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]
