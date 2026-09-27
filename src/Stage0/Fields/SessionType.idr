module Stage0.Fields.SessionType

import Stage0.Applicative
import Stage1.MetricalBounds

%default total

--------------------------------------------------------------------------------
-- 1. LINEAR SESSION TYPES FOR GAUGE FIELD PROTOCOLS
--------------------------------------------------------------------------------

||| Session Protocol state AST defining linear gauge field communication channels
public export
data SessionProto : Type where
  Send  : Type -> SessionProto -> SessionProto
  Recv  : Type -> SessionProto -> SessionProto
  Close : SessionProto

||| Dual of a Session Protocol: turns Send into Recv and Recv into Send
public export
dualProto : SessionProto -> SessionProto
dualProto (Send a p) = Recv a (dualProto p)
dualProto (Recv a p) = Send a (dualProto p)
dualProto Close      = Close

--------------------------------------------------------------------------------
-- 2. LINEAR SESSION CHANNEL & STATE TRANSITION
--------------------------------------------------------------------------------

||| Linear Session Channel parameterised by protocol state `p`
public export
data Channel : SessionProto -> Type where
  MkChan : (id : Nat) -> Channel p

||| Linearly sends a gauge charge token across session protocol `Send a p`
public export
sendGaugeToken : (1 chan : Channel (Send a p)) -> a -> Channel p
sendGaugeToken (MkChan id) val = MkChan id

||| Linearly receives a gauge charge token across session protocol `Recv a p`
public export
recvGaugeToken : (1 chan : Channel (Recv a p)) -> (val : a) -> (a, Channel p)
recvGaugeToken (MkChan id) val = (val, MkChan id)

||| Linearly terminates a completed session channel
public export
closeGaugeChannel : (1 chan : Channel Close) -> ()
closeGaugeChannel (MkChan id) = ()

||| A metrically synchronized linear gauge session channel carrying field tensors
public export
data GaugeSyncChannel : (dim : Nat) -> (color : MetricColor) -> SessionProto -> Type where
  MkGaugeSync : (0 space : VexelSpace dim color) -> Channel p -> GaugeSyncChannel dim color p

||| Linearly transmits a metrically bounded gauge field tensor across a sync channel
public export
sendMetricalGaugeTensor : {dim : Nat} -> {color : MetricColor} -> {a : Type} ->
                          (1 chan : GaugeSyncChannel dim color (Send a p)) -> 
                          MetricalEnvelope dim color a -> 
                          GaugeSyncChannel dim color p
sendMetricalGaugeTensor (MkGaugeSync space (MkChan id)) (BoxSpace _ payload) =
  MkGaugeSync space (MkChan id)

||| Linearly receives a metrically bounded gauge field tensor across a sync channel
public export
recvMetricalGaugeTensor : {dim : Nat} -> {color : MetricColor} -> {a : Type} ->
                          (1 chan : GaugeSyncChannel dim color (Recv a p)) -> 
                          MetricalEnvelope dim color a ->
                          (MetricalEnvelope dim color a, GaugeSyncChannel dim color p)
recvMetricalGaugeTensor (MkGaugeSync space (MkChan id)) env =
  (env, MkGaugeSync space (MkChan id))

||| Linearly terminates a completed metrically synchronized session channel
public export
closeGaugeSyncChannel : {dim : Nat} -> {color : MetricColor} ->
                        (1 chan : GaugeSyncChannel dim color Close) -> ()
closeGaugeSyncChannel (MkGaugeSync space (MkChan id)) = ()

--------------------------------------------------------------------------------
-- 3. COMPILE-TIME SESSION DUALITY INVARIANT PROOF
--------------------------------------------------------------------------------

||| Static compiler proof witness verifying that double dualization is the identity.
public export
0 verifySessionDuality : (p : SessionProto) -> dualProto (dualProto p) = p
verifySessionDuality (Send a p) = cong (Send a) (verifySessionDuality p)
verifySessionDuality (Recv a p) = cong (Recv a) (verifySessionDuality p)
verifySessionDuality Close      = Refl
