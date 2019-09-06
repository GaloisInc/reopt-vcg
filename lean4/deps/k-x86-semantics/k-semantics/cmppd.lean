def cmppd1 : instruction :=
  definst "cmppd" $ do
    pattern fun (v_3475 : imm int) (v_3476 : reg (bv 128)) (v_3477 : reg (bv 128)) => do
      v_5508 <- getRegister v_3477;
      v_5510 <- getRegister v_3476;
      v_5512 <- eval (handleImmediateWithSignExtend v_3475 8 8);
      setRegister (lhs.of_reg v_3477) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5508 0 64) (extract v_5510 0 64) v_5512) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5508 64 128) (extract v_5510 64 128) v_5512) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3470 : imm int) (v_3471 : Mem) (v_3472 : reg (bv 128)) => do
      v_8607 <- getRegister v_3472;
      v_8609 <- evaluateAddress v_3471;
      v_8610 <- load v_8609 16;
      v_8612 <- eval (handleImmediateWithSignExtend v_3470 8 8);
      setRegister (lhs.of_reg v_3472) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8607 0 64) (extract v_8610 0 64) v_8612) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8607 64 128) (extract v_8610 64 128) v_8612) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
