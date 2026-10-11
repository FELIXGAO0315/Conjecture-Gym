import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C12 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ (G.minDegree : ℤ)) (hn2 : (G.maxDegree : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    2 * (G.maxDegree : ℤ) ≥ -2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + 2 := by
  have s1 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
  have s7 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [s4, s5, s6]
  have s8 : 4 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 2 := by linarith [s1, s2, s8]
  linarith [s9]
