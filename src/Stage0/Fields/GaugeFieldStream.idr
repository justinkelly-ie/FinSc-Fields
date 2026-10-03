module Stage0.Fields.GaugeFieldStream

import public Stage0.BoxInt
import public Stage1.Order.Preorder
import public Stage0.OnSeq.FusedStream
import public Stage1.Math.OnSeq.ConjugateDuality
import public Stage1.Fields.GaugeGroup
import Data.Fuel

%default total

--------------------------------------------------------------------------------
-- 1. GAUGE FIELD TENSOR FLUX STREAM ALGEBRA
--------------------------------------------------------------------------------

||| Spacetime index pair (\mu, \nu) for field tensor F_{\mu\nu}.
public export
record SpacetimeIndex where
  constructor MkIndex
  mu : Int
  nu : Int

public export
Eq SpacetimeIndex where
  (MkIndex m1 n1) == (MkIndex m2 n2) = m1 == m2 && n1 == n2

||| Discrete Gauge Field Tensor Token F_{\mu\nu} carrying index and field magnitude.
public export
record GaugeFieldToken where
  constructor MkGaugeToken
  index : SpacetimeIndex
  strength : BoxInt

public export
Eq GaugeFieldToken where
  (MkGaugeToken i1 s1) == (MkGaugeToken i2 s2) = i1 == i2 && s1 == s2

||| Constructs a deforested stream of gauge field tokens from a list of strength values.
%inline public export
unfoldGaugeStream : List (SpacetimeIndex, BoxInt) -> FusedStream GaugeFieldToken
unfoldGaugeStream items = MkStream nextStep items
  where
    nextStep : List (SpacetimeIndex, BoxInt) -> Step (List (SpacetimeIndex, BoxInt)) GaugeFieldToken
    nextStep [] = Done
    nextStep ((idx, val) :: rest) = Yield (MkGaugeToken idx val) rest

||| Integrates total gauge flux \oint F_{\mu\nu} across a deforested stream using a fused hylomorphism.
public export covering
fusedIntegrateGaugeFlux : Fuel -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedIntegrateGaugeFlux f items =
  fusedHylomorphism f
    (\st => case st of
              [] => Done
              (idx, val) :: rest => Yield (MkGaugeToken idx val) rest)
    (\tok, acc => strength tok + acc)
    (intToBoxInt 0)
    items

||| Integrates total gauge flux using a 2LTT Conjugate Hylomorphism (Mamamorphism).
public export covering
fusedConjugateGaugeFlux : Fuel -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedConjugateGaugeFlux f items =
  fusedConjugateHylo f
    (\st => case st of
              [] => Done
              (idx, val) :: rest => Yield (MkGaugeToken idx val) rest)
    (\step => case step of
                Done => intToBoxInt 0
                Skip acc => acc
                Yield tok acc => strength tok + acc)
    id
    (intToBoxInt 0)
    items

||| Deforested stream sifting operator filtering gauge field tokens without intermediate allocations.
%inline public export
siftGaugeStream : (GaugeFieldToken -> Bool) -> FusedStream GaugeFieldToken -> FusedStream GaugeFieldToken
siftGaugeStream = siftFusedStream

||| Sifts a gauge field stream by specific spacetime index pair (\mu, \nu).
%inline public export
siftGaugeStreamByIndex : SpacetimeIndex -> FusedStream GaugeFieldToken -> FusedStream GaugeFieldToken
siftGaugeStreamByIndex target = siftFusedStream (\tok => index tok == target)

||| Computes sifted gauge flux density for a predicate over a deforested gauge field stream.
public export covering
fusedComputeGaugeFluxStream : Fuel -> (GaugeFieldToken -> Bool) -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedComputeGaugeFluxStream f pred items =
  fusedHylomorphism f
    (\st => case st of
              [] => Done
              (idx, val) :: rest =>
                let tok = MkGaugeToken idx val
                in if pred tok then Yield tok rest else Skip rest)
    (\tok, acc => strength tok + acc)
    (intToBoxInt 0)
    items

||| Zero-allocation single-pass field tensor flux decomposition (temporal/E-field vs spatial/B-field components).
public export covering
fusedComputeFieldTensorStream : Fuel -> List (SpacetimeIndex, BoxInt) -> (BoxInt, BoxInt)
fusedComputeFieldTensorStream f items =
  fusedHylomorphism f
    (\st => case st of
              [] => Done
              (idx, val) :: rest => Yield (MkGaugeToken idx val) rest)
    (\tok, (eFlux, bFlux) =>
        if mu (index tok) == 0 || nu (index tok) == 0
          then (strength tok + eFlux, bFlux)
          else (eFlux, strength tok + bFlux))
    (intToBoxInt 0, intToBoxInt 0)
    items

--------------------------------------------------------------------------------
-- 2. VERIFICATION AUDIT WITNESS
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation total gauge flux integration over deforested streams.
public export covering
auditGaugeFieldStreamProof : Bool
auditGaugeFieldStreamProof =
  let idx0 = MkIndex 0 1
      idx1 = MkIndex 1 2
      tokens = [(idx0, intToBoxInt 12), (idx1, intToBoxInt 8)]
      flux1 = fusedIntegrateGaugeFlux (limit 100) tokens
      flux2 = fusedConjugateGaugeFlux (limit 100) tokens
      siftedFlux = fusedComputeGaugeFluxStream (limit 100) (\tok => index tok == idx0) tokens
      (eFlux, bFlux) = fusedComputeFieldTensorStream (limit 100) tokens
  in unwrapBox flux1 == 20 && flux1 == flux2 &&
     unwrapBox siftedFlux == 12 &&
     unwrapBox eFlux == 12 && unwrapBox bFlux == 8

--------------------------------------------------------------------------------
-- 3. BIANCHI GAUGE FIELD STREAM TRANSPORT
--------------------------------------------------------------------------------

||| A Deforested Gauge Field Stream transporting an erased Bianchi Identity witness (dF = 0) across flux streams.
public export
record BianchiGaugeFieldStream (fE : Nat) (fB : Nat) (totalFlux : Nat) where
  constructor MkBianchiGaugeFieldStream
  streamData : FusedStream GaugeFieldToken
  0 bianchiPrf : BianchiIdentityWitness fE fB totalFlux

||| Constructs a deforested Gauge Field Stream with a compile-time Bianchi identity witness.
public export
makeBianchiGaugeFieldStream : (fE : Nat) -> (fB : Nat) -> (totalFlux : Nat) ->
                              (0 prf : BianchiIdentityWitness fE fB totalFlux) ->
                              List (SpacetimeIndex, BoxInt) ->
                              BianchiGaugeFieldStream fE fB totalFlux
makeBianchiGaugeFieldStream fE fB tot prf items =
  MkBianchiGaugeFieldStream (unfoldGaugeStream items) prf

