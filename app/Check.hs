module Main where
import Game.Bucephalus
import Game.Bucephalus.Haste 
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad
import qualified Data.Map as M
import Haste
import qualified Haste.Graphics.Canvas as C

main :: IO ()
main = do
  execBucephalus makeInfo

---------

makeInfo :: BucephalusInfo Int () () C.Bitmap
makeInfo = BucephalusInfo
  { canvasId = "canvas"
  , initState = ()
  , initializeFrame = initialize1
  , bucephalusFrame = frame1
  , imageDeliver = const $ C.loadBitmap "http://sozai.7gates.net/img/illustration/ribbon08/ribbon08-001.png"
  }

initialize1 :: BucephalusFrame Int () ()
initialize1 = toBucephalusFrame $ do
    insertObject 10 obj1
    forM_ [0..9] $ \i -> do
      insertObject i obj0
  where
    obj0 :: Object () 
    obj0 = Object
      { objDrawInfos = 
          [ DrawFigure (rectangle (-260,-260) (260,260)) drawOption
              { drawLineWidth = 3
              , borderColor = Just $ BuceRGB 0 0 255 
              }
          , DrawFigure (rectangle (-250,-250) (250,250)) drawOption
              { fillColor = Just $ BuceRGBA 0 0 255 0.2
              , borderColor = Nothing
              }
          ]
      , objCollisionFrame = []
      , objPosition = Point (0, 0)
      }

    obj1 :: Object () 
    obj1 = Object
      { objDrawInfos = 
          [ DrawImageInfo -- (DrawDefault $ Point (0, 0)) 
          ]
      , objCollisionFrame = []
      , objPosition = Point (0, 0)
      }

frame1 :: BucephalusFrame Int () () 
frame1 = toBucephalusFrame $ do
    forM_ [0..9] $ \i -> do
      modifyObject i $ moveObj (fromIntegral $ 10 - i)
  where
    moveObj :: Double -> Object () -> Object ()
    moveObj y obj = let 
        Point (x, _) = objPosition obj
      in if x < 750
        then move (Vector2D (y, y)) obj
        else obj { objPosition = Point (-250, -250) }
    
