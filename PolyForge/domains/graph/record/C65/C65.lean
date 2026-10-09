import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C65 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 1) (hn2 : -2 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≤ 0) :
    2 * (G.edgeFinset.card : ℤ) ≥ -(G.indepNum : ℤ) + 3 := by
  have s1 : (G.indepNum : ℤ) ≥ 0 := by positivity
  have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s6 : 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s7 : 2 * (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s5, s6]
  have s8 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hr := s7; omega
  have s9 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s10 : 2 * (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ 3 := by linarith [s8, s9]
  linarith [s10]
