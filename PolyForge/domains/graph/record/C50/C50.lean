import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C50 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.diam : ℤ) ≤ 2) :
    (G.radius.toNat : ℤ) ≤ -(G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - 1 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := radius_le_diam_int G hp2
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G hp2
    try push_cast at hw
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.diam : ℤ) ≥ -2 := by linarith [hn1]
  have s7 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s7]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -2 * (G.maxDegree : ℤ) + 6 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5, s6, s8]
  have s10 : -(G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 1 := by have hr := s9; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]
