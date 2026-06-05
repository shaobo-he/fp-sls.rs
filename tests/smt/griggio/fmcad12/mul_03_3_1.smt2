(set-info :total-time 64.79)
; Start decls (3)
(declare-fun |c::main::1::a!0@1#1| () (_ FloatingPoint 8 24))
(declare-fun |c::main::1::b!0@1#1| () (_ FloatingPoint 8 24))
(declare-fun |c::main::1::c!0@1#1| () (_ FloatingPoint 8 24))
; End decls
; Start constraints (19)
(assert (fp.lt ((_ to_fp 11 53) roundNearestTiesToEven |c::main::1::a!0@1#1|)
       (fp #b0 #b10000001000 #xf400000000000)))
(assert (fp.lt (fp #b1 #b10000001000 #xf400000000000)
       ((_ to_fp 11 53) roundNearestTiesToEven |c::main::1::a!0@1#1|)))
(assert (fp.lt ((_ to_fp 11 53) roundNearestTiesToEven |c::main::1::b!0@1#1|)
       (fp #b0 #b10000001000 #xf400000000000)))
(assert (fp.lt (fp #b1 #b10000001000 #xf400000000000)
       ((_ to_fp 11 53) roundNearestTiesToEven |c::main::1::b!0@1#1|)))
(assert (fp.lt ((_ to_fp 11 53) roundNearestTiesToEven |c::main::1::c!0@1#1|)
       (fp #b0 #b10000001000 #xf400000000000)))
(assert (fp.lt (fp #b1 #b10000001000 #xf400000000000)
       ((_ to_fp 11 53) roundNearestTiesToEven |c::main::1::c!0@1#1|)))
(assert (fp.leq |c::main::1::b!0@1#1| |c::main::1::a!0@1#1|))
(assert (fp.leq |c::main::1::c!0@1#1| |c::main::1::b!0@1#1|))
(assert (fp.leq (fp.add roundNearestTiesToEven
                |c::main::1::a!0@1#1|
                (fp.neg |c::main::1::b!0@1#1|))
        (fp #b0 #x7d #b00110011001100110011001)))
(assert (fp.leq (fp.add roundNearestTiesToEven
                |c::main::1::a!0@1#1|
                (fp.neg |c::main::1::c!0@1#1|))
        (fp #b0 #x7d #b00110011001100110011001)))
(assert (fp.leq (fp.add roundNearestTiesToEven
                |c::main::1::b!0@1#1|
                (fp.neg |c::main::1::c!0@1#1|))
        (fp #b0 #x7d #b00110011001100110011001)))
(assert (let ((a!1 (= ((_ to_fp 11 53)
                roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven
                        |c::main::1::c!0@1#1|
                        (fp.mul roundNearestTiesToEven
                                |c::main::1::a!0@1#1|
                                |c::main::1::b!0@1#1|)))
              (_ +oo 11 53))))
  (not a!1)))
(assert (let ((a!1 (= ((_ to_fp 11 53)
                roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven
                        |c::main::1::c!0@1#1|
                        (fp.mul roundNearestTiesToEven
                                |c::main::1::a!0@1#1|
                                |c::main::1::b!0@1#1|)))
              (_ NaN 11 53))))
  (not a!1)))
(assert (let ((a!1 (= ((_ to_fp 11 53)
                roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven
                        |c::main::1::c!0@1#1|
                        (fp.mul roundNearestTiesToEven
                                |c::main::1::a!0@1#1|
                                |c::main::1::b!0@1#1|)))
              (_ -oo 11 53))))
  (not a!1)))
(assert (let ((a!1 (= ((_ to_fp 11 53)
                roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven
                        |c::main::1::a!0@1#1|
                        (fp.mul roundNearestTiesToEven
                                |c::main::1::b!0@1#1|
                                |c::main::1::c!0@1#1|)))
              (_ +oo 11 53))))
  (not a!1)))
(assert (let ((a!1 (= ((_ to_fp 11 53)
                roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven
                        |c::main::1::a!0@1#1|
                        (fp.mul roundNearestTiesToEven
                                |c::main::1::b!0@1#1|
                                |c::main::1::c!0@1#1|)))
              (_ NaN 11 53))))
  (not a!1)))
(assert (let ((a!1 (= ((_ to_fp 11 53)
                roundNearestTiesToEven
                (fp.mul roundNearestTiesToEven
                        |c::main::1::a!0@1#1|
                        (fp.mul roundNearestTiesToEven
                                |c::main::1::b!0@1#1|
                                |c::main::1::c!0@1#1|)))
              (_ -oo 11 53))))
  (not a!1)))
(assert (fp.leq (fp.mul roundNearestTiesToEven
                |c::main::1::a!0@1#1|
                (fp.mul roundNearestTiesToEven
                        |c::main::1::b!0@1#1|
                        |c::main::1::c!0@1#1|))
        (fp.mul roundNearestTiesToEven
                |c::main::1::c!0@1#1|
                (fp.mul roundNearestTiesToEven
                        |c::main::1::a!0@1#1|
                        |c::main::1::b!0@1#1|))))
(assert (let ((a!1 (fp.add roundNearestTiesToEven
                   (fp.neg (fp.mul roundNearestTiesToEven
                                   |c::main::1::a!0@1#1|
                                   (fp.mul roundNearestTiesToEven
                                           |c::main::1::b!0@1#1|
                                           |c::main::1::c!0@1#1|)))
                   (fp.mul roundNearestTiesToEven
                           |c::main::1::c!0@1#1|
                           (fp.mul roundNearestTiesToEven
                                   |c::main::1::a!0@1#1|
                                   |c::main::1::b!0@1#1|)))))
  (not (fp.leq a!1 (fp #b0 #x80 #b10000000000000000000000)))))
; End constraints
(check-sat)
