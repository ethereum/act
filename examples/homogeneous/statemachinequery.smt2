(declare-rel state (Int))
(declare-rel error ())

(define-fun f ((x_pre Int) (x_post Int)) Bool (= x_post (ite (= x_pre 0) 1 x_pre)))
(define-fun g ((x_pre Int) (x_post Int)) Bool (= x_post (ite (= x_pre 1) 2 x_pre)))
(define-fun h ((x_pre Int) (x_post Int)) Bool (= x_post (ite (= x_pre 3) 7 x_pre)))
(define-fun invariant ((x Int)) Bool (and (>= x 0) (<= x 2)))

(declare-var x_pre Int)
(declare-var x_post Int)

(rule (state 0))

(rule
(=>
    (and
        (state x_pre)
        (or
            (f x_pre x_post)
            (g x_pre x_post)
            (h x_pre x_post)
        )
    )
    (state x_post)
))

(rule
(=>
    (and
        (state x_pre)
        (not (invariant x_pre))
    )
    error
))

(query error :print-certificate true)

