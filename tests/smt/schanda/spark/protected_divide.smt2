(set-info :total-time 5.34)
; Start decls (2)
(declare-fun left () (_ FloatingPoint 8 24))
(declare-fun right () (_ FloatingPoint 8 24))
; End decls
; Start constraints (7)
(assert (or (fp.isNormal left) (fp.isSubnormal left) (fp.isZero left)))
(assert (or (fp.isNormal right) (fp.isSubnormal right) (fp.isZero right)))
(assert (fp.leq (_ +zero 8 24) left))
(assert (fp.leq (_ +zero 8 24) right))
(assert (let ((a!1 (ite (fp.eq right (_ +zero 8 24))
                (fp #b0 #xfe #b11111111111111111111111)
                (ite (fp.lt right
                            (fp.div roundNearestTiesToEven
                                    left
                                    (fp #b0 #xfe #b11111111111111111111111)))
                     (fp #b0 #xfe #b11111111111111111111111)
                     (fp.div roundNearestTiesToEven left right)))))
  (not (fp.isNormal (ite (fp.lt right (fp #b0 #x7f #b00000000000000000000000))
                         a!1
                         (fp.div roundNearestTiesToEven left right))))))
(assert (let ((a!1 (ite (fp.eq right (_ +zero 8 24))
                (fp #b0 #xfe #b11111111111111111111111)
                (ite (fp.lt right
                            (fp.div roundNearestTiesToEven
                                    left
                                    (fp #b0 #xfe #b11111111111111111111111)))
                     (fp #b0 #xfe #b11111111111111111111111)
                     (fp.div roundNearestTiesToEven left right)))))
  (not (fp.isSubnormal (ite (fp.lt right
                                   (fp #b0 #x7f #b00000000000000000000000))
                            a!1
                            (fp.div roundNearestTiesToEven left right))))))
(assert (let ((a!1 (ite (fp.eq right (_ +zero 8 24))
                (fp #b0 #xfe #b11111111111111111111111)
                (ite (fp.lt right
                            (fp.div roundNearestTiesToEven
                                    left
                                    (fp #b0 #xfe #b11111111111111111111111)))
                     (fp #b0 #xfe #b11111111111111111111111)
                     (fp.div roundNearestTiesToEven left right)))))
  (not (fp.isZero (ite (fp.lt right (fp #b0 #x7f #b00000000000000000000000))
                       a!1
                       (fp.div roundNearestTiesToEven left right))))))
; End constraints
(check-sat)
