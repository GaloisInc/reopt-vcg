def vfnmsub231sd1 : instruction :=
  definst "vfnmsub231sd" $ do
    pattern fun (v_3465 : reg (bv 128)) (v_3466 : reg (bv 128)) (v_3467 : reg (bv 128)) => do
      v_12851 <- getRegister v_3467;
      v_12853 <- getRegister v_3466;
      v_12854 <- eval (extract v_12853 32 64);
      v_12856 <- eval (extract v_12853 96 128);
      v_12865 <- eval (extract v_12853 64 128);
      v_12876 <- getRegister v_3465;
      v_12877 <- eval (extract v_12876 64 128);
      v_12886 <- eval (extract v_12851 64 128);
      setRegister (lhs.of_reg v_3467) (concat (extract v_12851 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_12854) (concat (expression.bv_nat 32 0) v_12856)) (expression.bv_nat 1 1)) v_12854 v_12856)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_12854) (concat (expression.bv_nat 32 0) v_12856)) (expression.bv_nat 1 1)) v_12854 v_12856)) 53 11))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12865 0 1)) (uvalueMInt (extract v_12865 1 12)) (uvalueMInt (extract v_12865 12 64)))) 64) 53 11) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12877 0 1)) (uvalueMInt (extract v_12877 1 12)) (uvalueMInt (extract v_12877 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12886 0 1)) (uvalueMInt (extract v_12886 1 12)) (uvalueMInt (extract v_12886 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3462 : Mem) (v_3460 : reg (bv 128)) (v_3461 : reg (bv 128)) => do
      v_23402 <- getRegister v_3461;
      v_23404 <- getRegister v_3460;
      v_23405 <- eval (extract v_23404 32 64);
      v_23407 <- eval (extract v_23404 96 128);
      v_23416 <- eval (extract v_23404 64 128);
      v_23427 <- evaluateAddress v_3462;
      v_23428 <- load v_23427 8;
      v_23437 <- eval (extract v_23402 64 128);
      setRegister (lhs.of_reg v_3461) (concat (extract v_23402 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_23405) (concat (expression.bv_nat 32 0) v_23407)) (expression.bv_nat 1 1)) v_23405 v_23407)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_23405) (concat (expression.bv_nat 32 0) v_23407)) (expression.bv_nat 1 1)) v_23405 v_23407)) 53 11))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23416 0 1)) (uvalueMInt (extract v_23416 1 12)) (uvalueMInt (extract v_23416 12 64)))) 64) 53 11) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23428 0 1)) (uvalueMInt (extract v_23428 1 12)) (uvalueMInt (extract v_23428 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23437 0 1)) (uvalueMInt (extract v_23437 1 12)) (uvalueMInt (extract v_23437 12 64)))) 64));
      pure ()
    pat_end
