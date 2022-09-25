{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

import           Control.Monad        hiding (fmap)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.List.NonEmpty   (NonEmpty (..))
import           Data.Map             as Map
import           Data.Text            (pack, Text)
import           GHC.Generics         (Generic)
import           Ledger               hiding (singleton)
import qualified Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Value         as Value
import           Ledger.Ada           as Ada
import           Playground.Contract  (IO, ensureKnownCurrencies, printSchemas, stage, printJson)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Plutus.Contract
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (unless)
import qualified Prelude              as P
import           Schema               (ToSchema)
import           Text.Printf          (printf)

{-
-- GAME EXPLANATION --
A game where 2 player do bid alternately until target bid-amount is reached.
Player that makes the last bid is the winner and will get the reward.
For example:
   Game has target bid-amount = 10 & reward = 10 ADA.
   Turn 1: Player1 bid 5, total player's bid = 5
   Turn 2: Player2 bid 4, total player's bid = 9
   Turn 3: Player1 bid 2, total player's bid = 11
   Game ended since target bid-amount reached and Player1 win the game and will receive 100 ADA.

-- ACTORS --
This game has 3 actors:
   1. Host which define game properties, like:
      - player1     : PaymentPubKeyHash of the first player
      - player2     : PaymentPubKeyHash of the second player
      - deadline    : limit time for players to finish this game.
                      if game is not finished after deadline reached, game can be closed
      - max bid     : max amount player can bid on their turn
      - target bid  : target amount of total bid players need to reach
      - reward      : reward of this game, in lovelace
      Host can start the game using "start" endpoint.
      Host can also reclaim the reward if game is not finished after deadline using "close" endpoint
   2. Players (Player1 & Player2)
      Either Player1 / Player2 can make the first bid.
      But for the second bid onward, player needs to bid alternately.
      For example:
         If player2 make the first bid, then second bid must be done by player1,
         third bid must be done by player2, fourth bid must be done by player1, etc...
      
-- TESTING SCENARIOS --
   GAME PROPERTIES
      Host (Wallet1)        = a2c20c77887ace1cd986193e4e75babd8993cfd56995cd5cfce609c2
      Player1 (Wallet2)     = 80a4f45b56b88d1139da23bc4c3c75ec6d32943c087f250b86193ca7
      Player2 (Wallet3)     = 2e0ad60c3207248cecd47dbde3d752e0aad141d6b8f81ac2c6eca27c
      Deadline (+50 slot)   = 1596059141000
      Max bid               = 5
      Target bid            = 10
      Reward                = 10000000

   SCENARIO 1: Player1 win
      1. Host call "start" endpoint with game properties specified above.
      2. Wait for 3 slot
      3. Player1 call "bid" endpoint with amount = 5
      4. Wait for 3 slot
      5. Player2 call "bid" endpoint with amount = 4
      6. Wait for 3 slot
      7. Player2 call "bid" endpoint with amount = 2
      8. Wait for 3 slot
      9. Evaluate the scenario
      Notice that player1 will win the game and it's balances will increase because of reward.

   SCENARIO 2: Host reclaim
      1. Host call "start" endpoint with game properties specified above.
      2. Wait for 100 slot
      3. Host call "close" endpoint, use wallet 1 pubkeyhash as input (a2c20c77887ace1cd986193e4e75babd8993cfd56995cd5cfce609c2)
      4. wait for 3 slot
      Notice that game is closed and host balance will be returned.
-}

-- Datum
data Game = Game
    { gHost         :: !PaymentPubKeyHash
    , gPlayer1      :: !PaymentPubKeyHash
    , gPlayer2      :: !PaymentPubKeyHash
    , gDeadline     :: !POSIXTime
    , gMaxBid       :: !Integer
    , gTargetBid    :: !Integer
    , gReward       :: !Integer
    } deriving (P.Show, Generic, ToJSON, FromJSON, ToSchema)

instance Eq Game where
    {-# INLINABLE (==) #-}
    a == b = (gHost a == gHost b)           &&
             (gPlayer1 a == gPlayer1 b)     &&
             (gPlayer2 a == gPlayer2 b)     &&
             (gDeadline a == gDeadline b)   &&
             (gMaxBid a == gMaxBid b)       &&
             (gTargetBid a == gTargetBid b) &&
             (gReward a == gReward b)

isHostOnGame :: PaymentPubKeyHash -> Game -> Bool
isHostOnGame pkh g = gHost g == pkh

isPlayerOnGame :: PaymentPubKeyHash -> Game  -> Bool
isPlayerOnGame pkh g = gPlayer1 g == pkh || gPlayer2 g == pkh

isBidAmountValid :: Integer -> Game -> Bool
isBidAmountValid amount g@Game{..} = amount > 0 && amount <= gMaxBid

PlutusTx.unstableMakeIsData ''Game
PlutusTx.makeLift ''Game

data AccBid = AccBid
    { abBidder      :: !PaymentPubKeyHash
    , abBidAmount   :: !Integer
    , abTotalBid    :: !Integer
    } deriving P.Show

isPlayerCanBid :: PaymentPubKeyHash -> Maybe AccBid -> Bool
isPlayerCanBid pkh maybeAccBid = case maybeAccBid of
        Just ab@AccBid{..}  -> abBidder /= pkh
        Nothing             -> True

instance Eq AccBid where
    {-# INLINABLE (==) #-}
    b == c = (abBidder b == abBidder c)         &&
             (abBidAmount b == abBidAmount c)   &&
             (abTotalBid b == abTotalBid c)

PlutusTx.unstableMakeIsData ''AccBid
PlutusTx.makeLift ''AccBid

data GameDatum = GameDatum
    { gdGame    :: !Game
    , gdAccBid  :: !(Maybe AccBid)
    } deriving P.Show

isGameDatumTargetReached :: GameDatum -> Bool
isGameDatumTargetReached gd = case gdAccBid gd of
        Just ab@AccBid{..}  -> abTotalBid >= gTargetBid (gdGame gd)
        Nothing             -> False

PlutusTx.unstableMakeIsData ''GameDatum
PlutusTx.makeLift ''GameDatum

-- Redeemer
data GameAction = MkBid AccBid | Close
    deriving P.Show

PlutusTx.unstableMakeIsData ''GameAction
PlutusTx.makeLift ''GameAction

data Gaming
instance Scripts.ValidatorTypes Gaming where
    type instance DatumType Gaming = GameDatum
    type instance RedeemerType Gaming = GameAction

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: GameDatum -> GameAction -> ScriptContext -> Bool
mkGameValidator gd redeemer ctx = case redeemer of
        MkBid ab@AccBid{..} ->
            traceIfFalse "player not in game"   (isPlayerOnGame abBidder game)          &&
            traceIfFalse "player cannot bid"    (isPlayerCanBid abBidder (gdAccBid gd)) &&
            traceIfFalse "invalid bid amount"   (isBidAmountValid abBidAmount game)     &&
            traceIfFalse "too late"             correctBidSlotRange                     &&
            if abTotalBid >=  gTargetBid game
                then
                    traceIfFalse "expected player to get reward" (getsValue abBidder $ Ada.lovelaceValueOf (gReward game))
                else
                    traceIfFalse "wrong output datum"   (correctBidOutputDatum ab)  &&
                    traceIfFalse "wrong output value"   correctBidOutputValue
        Close               ->
            traceIfFalse "too early" correctCloseSlotRange &&
            traceIfFalse "expected host to get reward" (getsValue (gHost game) $ Ada.lovelaceValueOf (gReward game))
    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        game :: Game
        game = gdGame gd

        ownOutput   :: TxOut
        outputDatum :: GameDatum
        (ownOutput, outputDatum) = case getContinuingOutputs ctx of
            [o] -> case txOutDatumHash o of
                Nothing   -> traceError "wrong output type"
                Just h -> case findDatum h info of
                    Nothing        -> traceError "datum not found"
                    Just (Datum d) ->  case PlutusTx.fromBuiltinData d of
                        Just gd' -> (o, gd')
                        Nothing  -> traceError "error decoding data"
            _   -> traceError "expected exactly one continuing output"

        correctBidOutputDatum :: AccBid -> Bool
        correctBidOutputDatum ab = (gdGame outputDatum == game)   &&
                                   (gdAccBid outputDatum == Just ab)

        correctBidOutputValue :: Bool
        correctBidOutputValue = txOutValue ownOutput == Ada.lovelaceValueOf (gReward game)

        correctBidSlotRange :: Bool
        correctBidSlotRange = to (gDeadline game) `contains` txInfoValidRange info

        correctCloseSlotRange :: Bool
        correctCloseSlotRange = from (gDeadline game) `contains` txInfoValidRange info

        getsValue :: PaymentPubKeyHash -> Value -> Bool
        getsValue h v =
            let
                [o] = [ o'
                    | o' <- txInfoOutputs info
                    , txOutValue o' == v
                    ]
            in
                txOutAddress o == pubKeyHashAddress h Nothing


typedGameValidator :: Scripts.TypedValidator Gaming
typedGameValidator = Scripts.mkTypedValidator @Gaming
    $$(PlutusTx.compile [|| mkGameValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameAction

gameValidator :: Validator
gameValidator = Scripts.validatorScript typedGameValidator

gameHash :: Ledger.ValidatorHash
gameHash = Scripts.validatorHash typedGameValidator

gameAddress :: Ledger.Address
gameAddress = scriptHashAddress gameHash

data StartParams = StartParams
    { spPlayer1     :: !PaymentPubKeyHash
    , spPlayer2     :: !PaymentPubKeyHash
    , spDeadline    :: !POSIXTime
    , spMaxBid      :: !Integer
    , spTargetBid   :: !Integer
    , spReward      :: !Integer
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

data CloseParams = CloseParams
    { cpHost        :: !PaymentPubKeyHash
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type GameSchema =
        Endpoint "start" StartParams
    .\/ Endpoint "bid"   Integer
    .\/ Endpoint "close" CloseParams

start :: AsContractError e => StartParams -> Contract w s e ()
start StartParams{..} = do
    pkh <- ownPaymentPubKeyHash
    let g = Game
                { gHost         = pkh
                , gPlayer1      = spPlayer1
                , gPlayer2      = spPlayer2
                , gDeadline     = spDeadline
                , gMaxBid       = spMaxBid
                , gTargetBid    = spTargetBid
                , gReward       = spReward
                }
        d = GameDatum
                { gdGame = g
                , gdAccBid  = Nothing
                }
        v = Ada.lovelaceValueOf spReward
        tx = Constraints.mustPayToTheScript d v
    ledgerTx <- submitTxConstraints typedGameValidator tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @P.String $ printf "started game %s" (P.show g)

bid :: forall w s. Integer -> Contract w s Text ()
bid bidAmount = do
    pkh <- ownPaymentPubKeyHash
    (oref, o, d@GameDatum{..}) <- findFirstPlayerGame pkh
    logInfo @P.String $ printf "found game utxo with datum %s" (P.show d)

    when (isGameDatumTargetReached d) $
        throwError $ pack $ printf "bid target reached"

    unless (isBidAmountValid bidAmount gdGame) $
        throwError $ pack $ printf "bid amount invalid"

    unless (isPlayerCanBid pkh gdAccBid) $
        throwError $ pack $ printf "player cannot bid!"

    let ab = case gdAccBid of
                Nothing -> AccBid {abBidder = pkh, abBidAmount = bidAmount, abTotalBid = bidAmount}
                Just AccBid{..} -> AccBid {abBidder = pkh, abBidAmount = bidAmount, abTotalBid = abTotalBid + bidAmount}
        d' = d {gdAccBid = Just ab}
        r  = Redeemer $ PlutusTx.toBuiltinData $ MkBid ab

        lookups = Constraints.typedValidatorLookups typedGameValidator P.<>
                  Constraints.otherScript gameValidator                P.<>
                  Constraints.unspentOutputs (Map.singleton oref o)
        tx      = if abTotalBid ab >= gTargetBid gdGame
                    then
                        Constraints.mustValidateIn (to $ gDeadline gdGame)                          <>
                        Constraints.mustPayToPubKey pkh (Ada.lovelaceValueOf (gReward gdGame))      <>
                        Constraints.mustSpendScriptOutput oref r
                    else
                        Constraints.mustValidateIn (to $ gDeadline gdGame)                          <>
                        Constraints.mustPayToTheScript d' (Ada.lovelaceValueOf (gReward gdGame))    <>
                        Constraints.mustSpendScriptOutput oref r
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @P.String $ printf "made bid and update datum to %s" (P.show d')


close :: forall w s e. CloseParams -> Contract w s Text ()
close cp@CloseParams{..} = do
    (oref, o, d@GameDatum{..}) <- findFirstHostGame cpHost
    logInfo @P.String $ printf "found game utxo with datum %s" (P.show d)

    let r = Redeemer $ PlutusTx.toBuiltinData Close
        lookups = Constraints.typedValidatorLookups typedGameValidator P.<>
                  Constraints.otherScript gameValidator                P.<>
                  Constraints.unspentOutputs (Map.singleton oref o)
        tx      = Constraints.mustPayToPubKey cpHost (Ada.lovelaceValueOf (gReward gdGame)) <>
                  Constraints.mustValidateIn (from $ gDeadline gdGame)                      <>
                  Constraints.mustSpendScriptOutput oref r
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @P.String $ printf "closed game with datum %s" (P.show d)

findFirstPlayerGame :: PaymentPubKeyHash -> Contract w s Text (TxOutRef, ChainIndexTxOut, GameDatum)
findFirstPlayerGame pkh = do
    utxos <- utxosAt gameAddress
    let xs = [ (oref, o)
             | (oref, o) <- Map.toList utxos
             ]
    case xs of
        [(oref, o)] -> case _ciTxOutDatum o of
            Left _          -> throwError "datum missing"
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> throwError "datum has wrong type"
                Just d@GameDatum{..}
                    | isPlayerOnGame pkh gdGame -> return (oref, o, d)
                    | otherwise                 -> throwError "game utxo not found"
        _           -> throwError "game utxo not found"

findFirstHostGame :: PaymentPubKeyHash -> Contract w s Text (TxOutRef, ChainIndexTxOut, GameDatum)
findFirstHostGame pkh = do
    utxos <- utxosAt gameAddress
    let xs = [ (oref, o)
             | (oref, o) <- Map.toList utxos
             ]
    case xs of
        [(oref, o)] -> case _ciTxOutDatum o of
            Left _          -> traceError "datum missing"
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> throwError "datum has wrong type"
                Just d@GameDatum{..}
                    | isHostOnGame pkh gdGame   -> return (oref, o, d)
                    | otherwise                 -> throwError "game utxo not found"
        _           -> throwError "game utxo not found"

endpoints :: Contract () GameSchema Text ()
endpoints = awaitPromise (start' `select` bid' `select` close') >> endpoints
  where
    start' = endpoint @"start" start
    bid'   = endpoint @"bid"   bid
    close' = endpoint @"close" close

mkSchemaDefinitions ''GameSchema

mkKnownCurrencies []