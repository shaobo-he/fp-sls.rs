(set-info :total-time 4.72)
; Start decls (2)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
; End decls
; Start constraints (9)
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isNaN y)))
(assert (not (fp.isInfinite y)))
(assert (fp.leq (_ +zero 8 24) x))
(assert (fp.leq (_ +zero 8 24) y))
(assert (not (fp.eq y (_ +zero 8 24))))
(assert (not (fp.lt y
            (fp.div roundNearestTiesToEven
                    x
                    (fp #b0 #xfe #b11111111111111111111111)))))
(assert (or (fp.isNaN (fp.div roundNearestTiesToEven x y))
    (fp.isInfinite (fp.div roundNearestTiesToEven x y))))
; End constraints
(check-sat)
