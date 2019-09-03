def vdppd1 : instruction :=
  definst "vdppd" $ do
    pattern fun (v_3411 : imm int) (v_3415 : reg (bv 128)) (v_3416 : reg (bv 128)) (v_3417 : reg (bv 128)) => do
      v_6614 <- eval (handleImmediateWithSignExtend v_3411 8 8);
      v_6619 <- getRegister v_3416;
      v_6622 <- getRegister v_3415;
      v_6640 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_6614 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6619 64 128) 53 11) (MInt2Float (extract v_6622 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_6614 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6619 0 64) 53 11) (MInt2Float (extract v_6622 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3417) (concat (mux (eq (extract v_6614 6 7) (expression.bv_nat 1 1)) v_6640 (expression.bv_nat 64 0)) (mux (eq (extract v_6614 7 8) (expression.bv_nat 1 1)) v_6640 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3406 : imm int) (v_3405 : Mem) (v_3409 : reg (bv 128)) (v_3410 : reg (bv 128)) => do
      v_10759 <- eval (handleImmediateWithSignExtend v_3406 8 8);
      v_10764 <- getRegister v_3409;
      v_10767 <- evaluateAddress v_3405;
      v_10768 <- load v_10767 16;
      v_10786 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_10759 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10764 64 128) 53 11) (MInt2Float (extract v_10768 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_10759 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10764 0 64) 53 11) (MInt2Float (extract v_10768 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3410) (concat (mux (eq (extract v_10759 6 7) (expression.bv_nat 1 1)) v_10786 (expression.bv_nat 64 0)) (mux (eq (extract v_10759 7 8) (expression.bv_nat 1 1)) v_10786 (expression.bv_nat 64 0)));
      pure ()
    pat_end
