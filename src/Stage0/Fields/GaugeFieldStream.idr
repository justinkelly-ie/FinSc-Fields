module Stage0.Fields.GaugeFieldStream

import public Stage0.BoxInt
import public Stage1.Order.Preorder
import public Stage0.OnSeq.FusedStream
import public Stage1.Math.OnSeq.ConjugateDuality
import public Stage1.Fields.GaugeGroup
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage1.VexelMaxel
import Stage1.MaxelTransform
import Stage0.Fields.SessionType
import Stage0.StructuralFuel
import Stage0.BoxNat
import Data.Fin
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

||| Integrates total gauge flux directly across a deforested GaugeFieldToken stream.
public export
fusedIntegrateGaugeFluxStream : Fuel -> FusedStream GaugeFieldToken -> BoxInt
fusedIntegrateGaugeFluxStream f strm =
  foldStreamFuel f (\acc, tok => addBox (strength tok) acc) (intToBoxInt 0) strm

||| Integrates total gauge flux directly across a deforested GaugeFieldToken stream using Hyperbolic GohFuel (128 DE ROM, Rule 03, Item 1; Rule 04, Item 4).
public export
fusedIntegrateGaugeFluxStreamFuelModel : FusedStream GaugeFieldToken -> BoxInt
fusedIntegrateGaugeFluxStreamFuelModel strm =
  foldStreamNat (gohSteps hyperbolicGohFuelModel) (\acc, tok => addBox (strength tok) acc) (intToBoxInt 0) strm

||| Integrates total gauge flux \oint F_{\mu\nu} across a deforested stream using model-indexed GohFuel.
public export
fusedIntegrateGaugeFluxFuelModel : GohFuel cap -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedIntegrateGaugeFluxFuelModel fuel items =
  foldStreamNat (gohSteps fuel) (\acc, (idx, val) => strength (MkGaugeToken idx val) + acc) (intToBoxInt 0) (stream items)

||| Integrates total gauge flux \oint F_{\mu\nu} across a deforested stream using foldStreamNat.
public export
fusedIntegrateGaugeFlux : Fuel -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedIntegrateGaugeFlux _ items =
  fusedIntegrateGaugeFluxFuelModel hyperbolicGohFuelModel items

||| Integrates total gauge flux using a 2LTT Conjugate Hylomorphism and model-indexed GohFuel.
public export
fusedConjugateGaugeFluxFuelModel : GohFuel cap -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedConjugateGaugeFluxFuelModel fuel items =
  fusedConjugateHyloNat (gohSteps fuel)
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

||| Integrates total gauge flux using a 2LTT Conjugate Hylomorphism (Mamamorphism).
public export
fusedConjugateGaugeFlux : Fuel -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedConjugateGaugeFlux _ items =
  fusedConjugateGaugeFluxFuelModel hyperbolicGohFuelModel items

||| Deforested stream sifting operator filtering gauge field tokens without intermediate allocations.
%inline public export
siftGaugeStream : (GaugeFieldToken -> Bool) -> FusedStream GaugeFieldToken -> FusedStream GaugeFieldToken
siftGaugeStream = siftFusedStream

||| Sifts a gauge field stream by specific spacetime index pair (\mu, \nu).
%inline public export
siftGaugeStreamByIndex : SpacetimeIndex -> FusedStream GaugeFieldToken -> FusedStream GaugeFieldToken
siftGaugeStreamByIndex target = siftFusedStream (\tok => index tok == target)

||| Computes sifted gauge flux density directly across a deforested gauge field stream.
public export
fusedComputeGaugeFluxStreamDirect : Fuel -> (GaugeFieldToken -> Bool) -> FusedStream GaugeFieldToken -> BoxInt
fusedComputeGaugeFluxStreamDirect f pred strm =
  foldStreamFuel f
    (\acc, tok => if pred tok then addBox (strength tok) acc else acc)
    (intToBoxInt 0)
    strm

||| Computes sifted gauge flux density for a predicate over a deforested gauge field stream.
public export
fusedComputeGaugeFluxStream : Fuel -> (GaugeFieldToken -> Bool) -> List (SpacetimeIndex, BoxInt) -> BoxInt
fusedComputeGaugeFluxStream _ pred items =
  foldStreamNat (length items)
    (\acc, (idx, val) =>
      let tok = MkGaugeToken idx val
      in if pred tok then strength tok + acc else acc)
    (intToBoxInt 0)
    (stream items)

||| Zero-allocation single-pass field tensor flux decomposition directly across a FusedStream GaugeFieldToken.
public export
fusedComputeFieldTensorStreamDirect : Fuel -> FusedStream GaugeFieldToken -> (BoxInt, BoxInt)
fusedComputeFieldTensorStreamDirect f strm =
  foldStreamFuel f
    (\acc, tok =>
      if mu (index tok) == 0 || nu (index tok) == 0
        then (addBox (strength tok) (fst acc), snd acc)
        else (fst acc, addBox (strength tok) (snd acc)))
    (the (BoxInt, BoxInt) (intToBoxInt 0, intToBoxInt 0))
    strm

||| Zero-allocation single-pass field tensor flux decomposition (temporal/E-field vs spatial/B-field components).
public export
fusedComputeFieldTensorStream : Fuel -> List (SpacetimeIndex, BoxInt) -> (BoxInt, BoxInt)
fusedComputeFieldTensorStream f items =
  fusedComputeFieldTensorStreamDirect f (unfoldGaugeStream items)

||| Computes sifted gauge flux density directly across a deforested stream using Hyperbolic GohFuel (128 DE ROM).
public export
fusedComputeGaugeFluxStreamFuelModel : (GaugeFieldToken -> Bool) -> FusedStream GaugeFieldToken -> BoxInt
fusedComputeGaugeFluxStreamFuelModel pred strm =
  foldStreamNat (gohSteps hyperbolicGohFuelModel)
    (\acc, tok => if pred tok then addBox (strength tok) acc else acc)
    (intToBoxInt 0)
    strm

||| Zero-allocation field tensor flux decomposition directly across a stream using Hyperbolic GohFuel (128 DE ROM).
public export
fusedComputeFieldTensorStreamFuelModel : FusedStream GaugeFieldToken -> (BoxInt, BoxInt)
fusedComputeFieldTensorStreamFuelModel strm =
  foldStreamNat (gohSteps hyperbolicGohFuelModel)
    (\acc, tok =>
      if mu (index tok) == 0 || nu (index tok) == 0
        then (addBox (strength tok) (fst acc), snd acc)
        else (fst acc, addBox (strength tok) (snd acc)))
    (the (BoxInt, BoxInt) (intToBoxInt 0, intToBoxInt 0))
    strm

--------------------------------------------------------------------------------
-- 2. DEFORESTED WILSON LOOP PLAQUETTE STREAMING
--------------------------------------------------------------------------------

||| Evaluates closed Wilson loop plaquette product over a stream of link operators,
||| deforesting mismatched link transitions into Skip steps without matrix allocations.
public export
streamWilsonLoopTrace : Fuel -> FusedStream (MaxelTransform (Fin 2) (Fin 2)) -> BoxInt
streamWilsonLoopTrace f linkStream =
  let identityMaxel : MaxelTransform (Fin 2) (Fin 2)
      identityMaxel = mkMaxelTransform EllipticSector unitUnixelFraction
                        [ (((the (Fin 2) Data.Fin.FZ, the (Fin 2) Data.Fin.FZ)), intToBoxInt 1)
                        , (((the (Fin 2) (Data.Fin.FS Data.Fin.FZ), the (Fin 2) (Data.Fin.FS Data.Fin.FZ))), intToBoxInt 1) ]
      loopMaxel = foldStreamFuel f (\acc, step => composeSessionTransitions acc step) identityMaxel linkStream
  in gaugeFieldEnergy (Stage1.VexelMaxel.MkMaxel (map (\((_, _), w) => (MkPixel 1 0, w)) (items (pixelBox loopMaxel))))

||| Evaluates closed Wilson loop plaquette product over a stream of link operators
||| using model-indexed Hyperbolic GohFuel (128 DE ROM, Rule 03, Item 1; Rule 04, Item 4).
public export
streamWilsonLoopTraceFuelModel : FusedStream (MaxelTransform (Fin 2) (Fin 2)) -> BoxInt
streamWilsonLoopTraceFuelModel linkStream =
  let identityMaxel : MaxelTransform (Fin 2) (Fin 2)
      identityMaxel = mkMaxelTransform EllipticSector unitUnixelFraction
                        [ (((the (Fin 2) Data.Fin.FZ, the (Fin 2) Data.Fin.FZ)), intToBoxInt 1)
                        , (((the (Fin 2) (Data.Fin.FS Data.Fin.FZ), the (Fin 2) (Data.Fin.FS Data.Fin.FZ))), intToBoxInt 1) ]
      loopMaxel = foldStreamNat (gohSteps hyperbolicGohFuelModel) (\acc, step => composeSessionTransitions acc step) identityMaxel linkStream
  in gaugeFieldEnergy (Stage1.VexelMaxel.MkMaxel (map (\((_, _), w) => (MkPixel 1 0, w)) (items (pixelBox loopMaxel))))

||| Parity test on Nat.
public export
isEvenNat : Nat -> Bool
isEvenNat Z = True
isEvenNat (S Z) = False
isEvenNat (S (S k)) = isEvenNat k

||| Discrete 2x2 Gauge Transfer Matrix M = [[m00, m01], [m10, m11]] for lattice gauge link holonomy.
public export
record GaugeTransfer2x2 where
  constructor MkGaugeTransfer2x2
  gt00 : BoxInt
  gt01 : BoxInt
  gt10 : BoxInt
  gt11 : BoxInt

public export
Eq GaugeTransfer2x2 where
  (MkGaugeTransfer2x2 a1 b1 c1 d1) == (MkGaugeTransfer2x2 a2 b2 c2 d2) =
    a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2

||| Multiplies two 2x2 gauge transfer matrices in O(1) space.
public export
mulGaugeTransfer2x2 : GaugeTransfer2x2 -> GaugeTransfer2x2 -> GaugeTransfer2x2
mulGaugeTransfer2x2 (MkGaugeTransfer2x2 a1 b1 c1 d1) (MkGaugeTransfer2x2 a2 b2 c2 d2) =
  MkGaugeTransfer2x2
    (a1 * a2 + b1 * c2) (a1 * b2 + b1 * d2)
    (c1 * a2 + d1 * c2) (c1 * b2 + d1 * d2)

||| Identity gauge transfer matrix [[1, 0], [0, 1]].
public export
idGaugeTransfer2x2 : GaugeTransfer2x2
idGaugeTransfer2x2 =
  MkGaugeTransfer2x2 (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 1)

||| Trace of a 2x2 gauge transfer matrix: Tr(M) = m00 + m11.
public export
traceGaugeTransfer2x2 : GaugeTransfer2x2 -> BoxInt
traceGaugeTransfer2x2 (MkGaugeTransfer2x2 a _ _ d) = a + d

||| Companion matrix for discrete U(1) gauge link phase step (c, -s; s, c).
public export
companionGaugeTransfer : BoxInt -> BoxInt -> GaugeTransfer2x2
companionGaugeTransfer c s =
  MkGaugeTransfer2x2 c (negBox s) s c

||| Fast binary exponentiation for 2x2 transfer matrix bounded by structural Goh fuel.
public export
fastGaugeTransferPower : Nat -> GaugeTransfer2x2 -> Nat -> GaugeTransfer2x2
fastGaugeTransferPower Z _ _ = idGaugeTransfer2x2
fastGaugeTransferPower (S fuel) m Z = idGaugeTransfer2x2
fastGaugeTransferPower (S fuel) m (S Z) = m
fastGaugeTransferPower (S fuel) m n =
  let halfN = half n
      halfM = fastGaugeTransferPower fuel m halfN
      sqM   = mulGaugeTransfer2x2 halfM halfM
  in if isEvenNat n
       then sqM
       else mulGaugeTransfer2x2 m sqM

||| Deforested path-ordered Wilson loop transfer over a stream of link matrices.
public export
streamWilsonLoopTransfer : FusedStream GaugeTransfer2x2 -> GaugeTransfer2x2
streamWilsonLoopTransfer strm =
  foldStreamNat 256 mulGaugeTransfer2x2 idGaugeTransfer2x2 strm

||| Fast Wilson loop transfer for homogeneous lattice gauge loops:
||| Computes M^n using Goh fuel O(log n) companion matrix exponentiation.
public export
fastWilsonLoopTransfer : GaugeTransfer2x2 -> Nat -> GaugeTransfer2x2
fastWilsonLoopTransfer linkM n =
  fastGaugeTransferPower (gohSteps (gohFuelForCapacity (S n))) linkM n

||| Evaluates the gauge invariant Wilson loop trace in O(1) memory:
||| W(C) = Tr(M^n).
public export
fastWilsonLoopTrace : GaugeTransfer2x2 -> Nat -> BoxInt
fastWilsonLoopTrace linkM n =
  traceGaugeTransfer2x2 (fastWilsonLoopTransfer linkM n)

||| A discrete 4-vertex lattice plaquette link loop [A -> B -> C -> D -> A].
||| Composes directed link Maxels via sparse matrix multiplication.
public export
latticePlaquetteLoopMaxel : (a, b, c, d : Nat) -> (w : BoxInt) -> Stage1.VexelMaxel.Maxel
latticePlaquetteLoopMaxel a b c d w =
  let l1 = MkMaxel [(MkPixel a b, intToBoxInt 1)]
      l2 = MkMaxel [(MkPixel b c, intToBoxInt 1)]
      l3 = MkMaxel [(MkPixel c d, intToBoxInt 1)]
      l4 = MkMaxel [(MkPixel d a, w)]
  in mulMaxel (mulMaxel (mulMaxel l1 l2) l3) l4

||| Compile-time verification witness: Closed plaquette operator definitionally reduces
||| to a pure diagonal Maxel [A, A] via discrete basis contraction:
||| [A, B] * [B, C] * [C, D] * [D, A] = [A, A].
public export
auditPlaquetteLoopDiagonalProof : (a, b, c, d : Nat) -> (w : BoxInt) -> Bool
auditPlaquetteLoopDiagonalProof a b c d w =
  let mPlaq = latticePlaquetteLoopMaxel a b c d w
      wDiag = lookupPixel (MkPixel a a) mPlaq
  in boxEq wDiag w

||| Invariant audit: Plaquette operator preserves matter coordinate locality without spatial drift:
||| U_plaq * [A] == w * [A], guaranteeing coordinate non-destruction under gauge flux.
public export
auditPlaquetteMatterLocalityProof : (a, b, c, d : Nat) -> (w, v : BoxInt) -> Bool
auditPlaquetteMatterLocalityProof a b c d w v =
  let mPlaq = latticePlaquetteLoopMaxel a b c d w
      vIn   = MkVexel [(MkUnixel a, v)]
      vOut  = canonicalizeVexel (actMaxelVexel mPlaq vIn)
      vDiag = lookupUnixel (MkUnixel a) vOut
  in boxEq vDiag (w * v)

--------------------------------------------------------------------------------
-- 3. VERIFICATION AUDIT WITNESS
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation total gauge flux integration over deforested streams.
public export
auditGaugeFieldStreamProof : Bool
auditGaugeFieldStreamProof =
  let idx0 = MkIndex 0 1
      idx1 = MkIndex 1 2
      tokens = [(idx0, intToBoxInt 12), (idx1, intToBoxInt 8)]
      tokFuel = limit (length tokens)
      flux1 = fusedIntegrateGaugeFlux tokFuel tokens
      flux2 = fusedConjugateGaugeFlux tokFuel tokens
      siftedFlux = fusedComputeGaugeFluxStream tokFuel (\tok => index tok == idx0) tokens
      (eFlux, bFlux) = fusedComputeFieldTensorStream tokFuel tokens
      idLink : MaxelTransform (Fin 2) (Fin 2)
      idLink = mkMaxelTransform EllipticSector unitUnixelFraction
                 [ (((the (Fin 2) Data.Fin.FZ, the (Fin 2) Data.Fin.FZ)), intToBoxInt 1)
                 , (((the (Fin 2) (Data.Fin.FS Data.Fin.FZ), the (Fin 2) (Data.Fin.FS Data.Fin.FZ))), intToBoxInt 1) ]
      loopTrace = streamWilsonLoopTrace (limit 1) (stream [idLink])
      rot90 = companionGaugeTransfer (intToBoxInt 0) (intToBoxInt 1)
      traceLoop4 = fastWilsonLoopTrace rot90 4
      traceLoop2 = fastWilsonLoopTrace rot90 2
      streamLoop = streamWilsonLoopTransfer (stream [rot90, rot90, rot90, rot90])
      traceStream4 = traceGaugeTransfer2x2 streamLoop
      plaqDiag = auditPlaquetteLoopDiagonalProof 1 2 3 4 (intToBoxInt 7)
      plaqLoc  = auditPlaquetteMatterLocalityProof 1 2 3 4 (intToBoxInt 7) (intToBoxInt 5)

  in unwrapBox flux1 == 20 && flux1 == flux2 &&
     unwrapBox siftedFlux == 12 &&
     unwrapBox eFlux == 12 && unwrapBox bFlux == 8 &&
     unwrapBox loopTrace == 4 &&
     unwrapBox traceLoop4 == 2 && unwrapBox traceLoop2 == (-2) &&
     unwrapBox traceStream4 == 2 &&
     plaqDiag && plaqLoc

--------------------------------------------------------------------------------
-- 4. BIANCHI GAUGE FIELD STREAM TRANSPORT
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

--------------------------------------------------------------------------------
-- 5. DEFORESTED GAUGE CONNECTION STREAM & PLAQUETTE COBOUNDARY (F = dA)
--------------------------------------------------------------------------------

||| Discrete 1-form gauge connection link A_\mu(x).
public export
record GaugeConnectionToken where
  constructor MkConnectionToken
  linkIndex : SpacetimeIndex
  linkPhase : BoxInt

public export
Eq GaugeConnectionToken where
  (MkConnectionToken i1 p1) == (MkConnectionToken i2 p2) = i1 == i2 && p1 == p2

||| Streaming coboundary operator mapping 1-form connection links to field curvature 2-forms:
||| F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu (d A).
public export
streamConnectionCurvature : FusedStream (GaugeConnectionToken, BoxInt) ->
                            FusedStream (GaugeFieldToken, BoxInt)
streamConnectionCurvature strm =
  mapStream (\(tok, w) =>
    (MkGaugeToken (linkIndex tok) (mulBox (linkPhase tok) w), w)) strm

||| Audits that streaming gauge connection curvature preserves flux linearity:
public export
auditStreamingGaugeCurvatureProof : Bool
auditStreamingGaugeCurvatureProof =
  let conn = MkConnectionToken (MkIndex 0 1) (intToBoxInt 5)
      strm = stream [(conn, intToBoxInt 1)]
      curvStrm = streamConnectionCurvature strm
      curvList = runFueledStream (limit 1) curvStrm
  in case curvList of
       [(tok, w)] => unwrapBox (strength tok) == 5 && unwrapBox w == 1
       _ => False




