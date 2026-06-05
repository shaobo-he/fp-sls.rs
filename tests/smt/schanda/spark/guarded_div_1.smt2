(set-info :total-time 4.53)
; Start decls (2)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
; End decls
; Start constraints (6)
(assert (or (fp.isNormal x) (fp.isSubnormal x) (fp.isZero x)))
(assert (fp.leq (_ +zero 8 24) x))
(assert (fp.lt (fp #b0 #x7b #b10011001100110011001101) y))
(assert (fp.lt y (fp #b0 #x7f #b00000000000000000000000)))
(assert (fp.leq (fp.div roundNearestTiesToEven
                x
                (fp #b0 #x88 #b11110100000000000000000))
        y))
(assert (not (fp.lt (fp.div roundNearestTiesToEven x y)
            (fp #b0 #x88 #b11110100000000000000000))))
; End constraints
(check-sat)
