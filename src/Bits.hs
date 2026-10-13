{- | A tiny bit writer for hand-built inputs. It is deliberately separate from
the package's own writer: the edge cases here have to include bytes that
writer would never produce, such as padded numbers and odd chunkings.
-}
module Bits (
  Bits,
  bits,
  natPadded,
  filler,
  chunks,
  toBytes,
) where

import Data.Bits (shiftR, testBit, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Word (Word8)
import Numeric.Natural (Natural)

type Bits = [Bool]

-- | The low @w@ bits of @n@, most significant first.
bits :: Int -> Integer -> Bits
bits w n = [testBit n i | i <- [w - 1, w - 2 .. 0]]

-- | A natural in seven-bit groups, least significant first, followed by
-- @extra@ groups of zero payload, as a lenient writer might produce.
natPadded :: Int -> Natural -> Bits
natPadded extra n0 = concatMap byte (withContinuation (groups n0 ++ replicate extra 0))
  where
    groups n
      | n < 128 = [fromIntegral n]
      | otherwise = fromIntegral (n .&. 0x7f) : groups (n `shiftR` 7)
    withContinuation gs = zipWith mark [1 :: Int ..] gs
      where
        mark i g = if i < length gs then g .|. 0x80 else g
    byte :: Word8 -> Bits
    byte = bits 8 . fromIntegral

-- | Padding from the current length: @extraZeroBytes@ whole bytes of 0s more
-- than the minimum, then the closing 1.
filler :: Int -> Bits -> Bits
filler extraZeroBytes acc =
  let k = 8 - length acc `mod` 8
   in acc ++ replicate (k - 1 + 8 * extraZeroBytes) False ++ [True]

-- | Byte-string chunks as given, each after its length byte, then the zero
-- byte. The caller has already padded to a byte boundary.
chunks :: [ByteString] -> Bits
chunks cs = concatMap one cs ++ bits 8 0
  where
    one c = bits 8 (fromIntegral (BS.length c)) ++ concatMap (bits 8 . fromIntegral) (BS.unpack c)

-- | Pack to bytes. A partial last byte is padded with 0s, which a test can
-- use on purpose to build malformed input.
toBytes :: Bits -> ByteString
toBytes = BS.pack . go
  where
    go [] = []
    go bs =
      let (b, rest) = splitAt 8 bs
          b' = b ++ replicate (8 - length b) False
       in foldl (\acc x -> acc * 2 + (if x then 1 else 0)) 0 b' : go rest
