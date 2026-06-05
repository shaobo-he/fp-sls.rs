(set-info :total-time 4.05)
; Start decls (3)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun n () (_ FloatingPoint 8 24))
; End decls
; Start constraints (3)
(assert (fp.lt a (fp.mul roundNearestTiesToEven n b)))
(assert (fp.lt (_ +zero 8 24) b))
(assert (not (fp.leq (fp.div roundNearestTiesToEven a b) n)))
; End constraints
(check-sat)
