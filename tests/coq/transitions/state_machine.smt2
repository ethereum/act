(define-fun f ((x_pre Int) (x_post Int)) Bool
	(= x_post (ite (= x_pre 0) 1 x_pre))
)
(define-fun g ((x_pre Int) (x_post Int)) Bool
	(= x_post (ite (= x_pre 1) 2 x_pre))
)
(define-fun h ((x_pre Int) (x_post Int)) Bool
	(= x_post (ite (= x_pre 2) 0 x_pre))
)

(define-fun init ((x Int)) Bool (= x 0))
(define-fun inv ((x Int)) Bool (<= x 2))

(declare-const x_pre Int)
(declare-const x_post Int)

(assert (and
	(or
		(and
			(init x_pre)
			(not (inv x_pre))
		)
		(and
			(<= 0 x_pre)
			(inv x_pre)
			(or
				(f x_pre x_post)
				(g x_pre x_post)
				(h x_pre x_post)
			)
			(not (inv x_post))
		)
	)
))

(check-sat)
