(define-fun f ((x_pre Int) (y_pre Int) (z_pre Int) (scalar Int) (x_post Int) (y_post Int) (z_post Int)) Bool
	(and
		(>= scalar 1)
		(= x_post (* x_pre scalar))
		(= z_post (* z_pre scalar))
		(= y_pre y_post)
	)
)

(define-fun g ((x_pre Int) (y_pre Int) (z_pre Int) (scalar Int) (x_post Int) (y_post Int) (z_post Int)) Bool
	(and
		(>= scalar 1)
		(= y_post (* y_pre scalar))
		(= z_post (* z_pre scalar))
		(= x_pre x_post)
	)
)

(define-fun init ((x Int) (y Int) (z Int)) Bool (and (= x 3) (= y 5) (= z 15)))

(define-fun invariant ((x Int) (y Int) (z Int)) Bool (= z (* x y)))

(declare-const x_pre Int)
(declare-const y_pre Int)
(declare-const z_pre Int)
(declare-const x_post Int)
(declare-const y_post Int)
(declare-const z_post Int)
(declare-const scalar Int)

(assert (and
	(or
		(and
			(init x_pre y_pre z_pre)
			(not (invariant x_pre y_pre z_pre))
		)
		(and
			(<= 0 x_pre)
			(<= 0 y_pre)
			(<= 0 z_pre)
			(<= 0 scalar)
			(invariant x_pre y_pre z_pre)
			(or
				(f x_pre y_pre z_pre scalar x_post y_post z_post)
				(g x_pre y_pre z_pre scalar x_post y_post z_post)
			)
			(not (invariant x_post y_post z_post))
		)
	)
))

(check-sat)
