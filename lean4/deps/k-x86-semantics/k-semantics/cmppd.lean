def cmppd1 : instruction :=
  definst "cmppd" $ do
    pattern fun (v_3448 : imm int) (v_3449 : reg (bv 128)) (v_3450 : reg (bv 128)) => do
      v_5628 <- getRegister v_3450;
      v_5630 <- getRegister v_3449;
      v_5632 <- eval (handleImmediateWithSignExtend v_3448 8 8);
      setRegister (lhs.of_reg v_3450) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5628 0 64) (extract v_5630 0 64) v_5632) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5628 64 128) (extract v_5630 64 128) v_5632) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3443 : imm int) (v_3444 : Mem) (v_3445 : reg (bv 128)) => do
      v_8899 <- getRegister v_3445;
      v_8901 <- evaluateAddress v_3444;
      v_8902 <- load v_8901 16;
      v_8904 <- eval (handleImmediateWithSignExtend v_3443 8 8);
      setRegister (lhs.of_reg v_3445) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8899 0 64) (extract v_8902 0 64) v_8904) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8899 64 128) (extract v_8902 64 128) v_8904) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
