(set-option :print-success false)
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-fun x ( ) Int)
(declare-fun y ( ) Int)
(declare-fun a ( ) Bool)
(assert (<= (+ x y) 0))
(assert (= x 0))
(assert (or (not a) (= x 1) (>= y 0)))
(assert (not (= (+ y 1) 0)))
(assert (not (= (+ y 2) 0))) 
(check-sat)
(get-value (x y))
(exit)
