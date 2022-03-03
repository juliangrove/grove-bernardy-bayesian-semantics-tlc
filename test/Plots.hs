import Examples.HRSA
import qualified Examples.GoodLass 
import qualified Examples.Guy
main :: IO ()
main = do
  plotData exampleLassGood
  plotData (exampleCookies 1)
  plotData (exampleCookies 4)
  plotData (exampleCookies 10)
  Examples.GoodLass.saltPaperSetup
  Examples.GoodLass.moreUtterances
  Examples.Guy.plotData
