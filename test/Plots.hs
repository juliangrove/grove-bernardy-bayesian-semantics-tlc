import Examples.HRSA

main :: IO ()
main = do
  plotData (exampleCookies 1)
  plotData (exampleCookies 4)
  plotData (exampleCookies 10)
