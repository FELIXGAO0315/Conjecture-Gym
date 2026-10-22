import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C142 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.chromaticNumber.toNat : ℤ)) (hn2 : (Fintype.card V : ℤ) ≤ 5) :
    (Fintype.card V : ℤ) ≥ (G.edgeFinset.card : ℤ) - 1 := by
  have s1 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn2]
  have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -2 * (G.cliqueNum : ℤ) ≥ -5 := by linarith [s2, s3, s1]
  have s5 : -(G.cliqueNum : ℤ) ≥ -2 := by have hr := s4; omega
  have s6 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := turan_r2_int G (by linarith [s5])
    try push_cast at hw
    linarith [hw]
  have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s7, s3]
  have s9 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 10 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (5 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s8]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : 4 * (Fintype.card V : ℤ) - 4 * (G.edgeFinset.card : ℤ) ≥ -5 := by linarith [s1, s6, s9]
  have s11 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ -1 := by have hr := s10; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]
