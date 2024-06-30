module Tests where

import LambdaParser ( parseExpr )
import LambdaTypeInference

testTemplate s et = do case parseExpr s of
                           Left er -> print er
                           Right e -> print (fst (infer e) == et)
-- testTemplateErr s = do case parseExpr s of
--                            Left er -> print er
--                            Right e -> False

-- \x.let f = (\y.(x,y)) in (f True, f 1): t2 -> ((t2, Bool), (t2, Int))
-- (\x.let f = (\y.(x,y)) in (f True, f 1)) 2: ((Int, Bool), (Int, Int))
-- case 1 of {1 -> True; 2 -> False}: Bool
-- case 1 of {1 -> True; 2 -> 2}: CAN'T UNIFY
-- case 1 of {True -> 1; False -> 2}: CAN'T UNIFY
-- case 1 of {1 -> 1; False -> 2}: CAN'T UNIFY
-- (\x.let f = (\y.(x,y)) in (case f True of {(z, True) -> z})) 3: Int
-- let f = (\y.(True, y)) in (case f False of {(True, True) -> True; (False, False) -> False}): Bool
-- \x.let f = (\y.(x,y)) in (case f True of {(z, True) -> z}): t2 -> t2
-- \x.let f = (\y.(x,y)) in (case f True of {(z, True) -> z; (a, b) -> b}): Bool -> Bool
-- (\x.let f = (\y.(x,y)) in (case f True of {(z, True) -> z; (a, b) -> b})) True: Bool
-- (\x.let f = (\y.(x,y)) in (case f True of {(z, True) -> z; (a, b) -> b})) False: Bool
-- (\x.let f = (\y.(x,y)) in (case f True of {(z, True) -> z; (a, b) -> b})) 123: CAN'T UNIFY

test1 = testTemplate "\\x.let f = (\\y.(x,y)) in (f True, f 1)" (TVar "t2" --> ((TVar "t2" |<>| TCon "Bool") |<>| (TVar "t2" |<>| TCon "Int")))
test2 = testTemplate "(\\x.let f = (\\y.(x,y)) in (f True, f 1)) 2" ((TCon "Int" |<>| TCon "Bool") |<>| (TCon "Int" |<>| TCon "Int"))
test3 = testTemplate "case 1 of {1 -> True; 2 -> False}" (TCon "Bool")
-- test4 = testTemplateErr "case 1 of {1 -> True; 2 -> 2}"
-- test5 = testTemplateErr "case 1 of {True -> 1; False -> 2}"
-- test6 = testTemplateErr "case 1 of {1 -> 1; False -> 2}"
test4 = testTemplate "(\\x.let f = (\\y.(x,y)) in (case f True of {(z, True) -> z})) 3" (TCon "Int")
test5 = testTemplate "let f = (\\y.(True, y)) in (case f False of {(True, True) -> True; (False, False) -> False})" (TCon "Bool")
test6 = testTemplate "\\x.let f = (\\y.(x,y)) in (case f True of {(z, True) -> z})" (TVar "t2" --> TVar "t2")
test7 = testTemplate "\\x.let f = (\\y.(x,y)) in (case f True of {(z, True) -> z; (a, b) -> b})" (TCon "Bool" --> TCon "Bool")
test8 = testTemplate "(\\x.let f = (\\y.(x,y)) in (case f True of {(z, True) -> z; (a, b) -> b})) True" (TCon "Bool")