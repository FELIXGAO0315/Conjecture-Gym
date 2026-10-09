import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C70 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 3) (hn2 : (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) ≤ 0) :
    2 * (G.vertexCoverNum.toNat : ℤ) ≤ 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - 4 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s1, s2, s3]
  have s5 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s4; omega
  have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2]
  have s7 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s9 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s5, s7, s8]
  linarith [s9]
