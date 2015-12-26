{-# LANGUAGE ScopedTypeVariables #-}
module Game.Bucephalus.Haste 
  ( BucephalusInfo(..)
  , execBucephalus
  ) where
import Haste
import Haste.Graphics.Canvas 
import Game.Bucephalus
import Control.Monad

data BucephalusInfo a i s b = BucephalusInfo
  { canvasId :: String
  , initState :: s
  , initializeFrame :: BucephalusFrame a i s
  , bucephalusFrame :: BucephalusFrame a i s
  , imageDeliver :: i -> IO b
  }

-- TODO : DrawText
instance ImageBuffer () where
  draw = undefined
  drawClipped = undefined
  drawScaled = undefined

execBucephalus :: (Ord a, ImageBuffer b) => BucephalusInfo a i s b -> IO ()
execBucephalus (BucephalusInfo id initSt initialize frame deliver) = do
  c <- getCanvasById id
  case c of
    Just canvas -> do
      loop canvas (initialize $ makeInitData initSt) frame deliver
    Nothing -> do
      alert "bucephalus-haste error : canvas not found."

loop :: ImageBuffer b 
  => Canvas -> (BucephalusStateData a i s, PaintInfo i) -> BucephalusFrame a i s -> (i -> IO b) -> IO ()
loop canvas (state, paintInfo) frame deliver = do
  makePicture canvas paintInfo deliver
  setTimer (Once 33) $ loop canvas (frame state) frame deliver
  return ()

makePicture :: forall i b. ImageBuffer b => Canvas -> PaintInfo i -> (i -> IO b) -> IO ()
makePicture canvas (PaintInfo ds) deliver = do
    res <- mapM execPaint ds
    render canvas $ sequence_ res

execPaint :: DrawInfo i -> IO (Picture ())
--execPaint DrawImageInfo = putStrLn "DrawImageInfo" >> return (return ())
execPaint (DrawFigure f o) = return $ drawFigure f o
--execPaint (DrawImageInfo (Default (Point p) i)) = deliver i >>= return . flip draw p 
execPaint _ = return (return ())

drawFigure :: Figure -> DrawOption -> Picture ()
drawFigure (FigureRectangle (Rectangle (Point p1, Point p2))) o = execDraw (rect p1 p2) o
drawFigure _ _ = return ()

execDraw :: Shape () -> DrawOption -> Picture ()
execDraw s o = do
  case fillColor o of
    Just (BuceRGB r g b) -> color (RGB r g b) $ fill s
    Just (BuceRGBA r g b a) -> color (RGBA r g b a) $ fill s
    _ -> return ()
  case borderColor o of
    Just (BuceRGB r g b) -> color (RGB r g b) . lineWidth (drawLineWidth o) $ stroke s
    Just (BuceRGBA r g b a) -> color (RGBA r g b a) . lineWidth (drawLineWidth o) $ stroke s
    _ -> return ()
