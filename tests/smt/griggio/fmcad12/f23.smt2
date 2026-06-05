(set-info :total-time 76.02)
; Start decls (2)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
; End decls
; Start constraints (7)
(assert (fp.leq (fp.mul roundNearestTiesToEven
                (fp #b0 #x80 #b10000000000000000000000)
                (fp.mul roundNearestTiesToEven x y))
        (fp.add roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven
                        x
                        (fp.mul roundNearestTiesToEven x x))
                (fp.mul roundNearestTiesToEven
                        y
                        (fp.mul roundNearestTiesToEven y y)))))
(assert (fp.leq (fp #b0 #x7b #b10011001100110011001101)
        (fp.add roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven x x)
                (fp.mul roundNearestTiesToEven y y))))
(assert (let ((a!1 (fp.mul roundNearestTiesToEven
                   (fp.add roundNearestTiesToEven
                           (fp.mul roundNearestTiesToEven x x)
                           (fp.mul roundNearestTiesToEven y y))
                   (fp.add roundNearestTiesToEven
                           (fp.mul roundNearestTiesToEven y y)
                           (fp.mul roundNearestTiesToEven
                                   x
                                   (fp.add roundNearestTiesToEven
                                           x
                                           (fp #b0 #x7f #b00000000000000000000000)))))))
  (fp.leq a!1
          (fp.mul roundNearestTiesToEven
                  (fp.mul roundNearestTiesToEven x y)
                  (fp #b0 #x81 #b00000000000000000000000)))))
(assert (fp.leq x (fp #b0 #x80 #b10000000000000000000000)))
(assert (fp.leq (fp #b1 #x80 #b10000000000000000000000) x))
(assert (fp.leq y (fp #b0 #x80 #b10000000000000000000000)))
(assert (fp.leq (fp #b1 #x80 #b10000000000000000000000) y))
; End constraints
(check-sat)
