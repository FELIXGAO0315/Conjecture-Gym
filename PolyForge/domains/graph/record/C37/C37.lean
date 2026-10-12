import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C37 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 5) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 2) :
    (Fintype.card V : ℤ) ≥ 3 * (G.edgeFinset.card : ℤ) - 13 := by
  have s1 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
  have s2 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s3 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s2]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s4 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [hn2]
  have s6 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s4, s5]
  have s7 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := turan_r2_int G (by linarith [s6])
    try push_cast at hw
    linarith [hw]
  have s8 : 4 * (Fintype.card V : ℤ) - 12 * (G.edgeFinset.card : ℤ) ≥ -55 := by linarith [s1, s3, s7]
  have s9 : (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) ≥ -13 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]
