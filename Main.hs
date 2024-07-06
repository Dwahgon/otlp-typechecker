import LambdaParser
import LambdaTypeInference
import Tests

main = do putStr "Lambda:"
          s <- getLine
          case parseExpr s of
               Left er -> print er
               Right e -> print e >> print (infer e)

runTests = do test1
              test2
              test3
              test4
              test5
              test6
              test7
              test8
              test9
              test10
              test11