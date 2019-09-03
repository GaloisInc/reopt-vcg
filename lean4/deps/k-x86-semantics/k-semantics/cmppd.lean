def cmppd1 : instruction :=
  definst "cmppd" $ do
    pattern fun (v_3397 : imm int) (v_3398 : reg (bv 128)) (v_3399 : reg (bv 128)) => do
      v_5615 <- getRegister v_3399;
      v_5617 <- getRegister v_3398;
      v_5619 <- eval (handleImmediateWithSignExtend v_3397 8 8);
      setRegister (lhs.of_reg v_3399) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5615 0 64) (extract v_5617 0 64) v_5619) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5615 64 128) (extract v_5617 64 128) v_5619) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3393 : imm int) (v_3392 : Mem) (v_3394 : reg (bv 128)) => do
      v_8918 <- getRegister v_3394;
      v_8920 <- evaluateAddress v_3392;
      v_8921 <- load v_8920 16;
      v_8923 <- eval (handleImmediateWithSignExtend v_3393 8 8);
      setRegister (lhs.of_reg v_3394) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8918 0 64) (extract v_8921 0 64) v_8923) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8918 64 128) (extract v_8921 64 128) v_8923) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
