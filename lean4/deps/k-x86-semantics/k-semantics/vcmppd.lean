def vcmppd1 : instruction :=
  definst "vcmppd" $ do
    pattern fun (v_2918 : imm int) (v_2922 : reg (bv 128)) (v_2923 : reg (bv 128)) (v_2924 : reg (bv 128)) => do
      v_6027 <- getRegister v_2923;
      v_6029 <- getRegister v_2922;
      v_6031 <- eval (handleImmediateWithSignExtend v_2918 8 8);
      setRegister (lhs.of_reg v_2924) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_6027 0 64) (extract v_6029 0 64) v_6031) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_6027 64 128) (extract v_6029 64 128) v_6031) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2931 : imm int) (v_2932 : reg (bv 256)) (v_2933 : reg (bv 256)) (v_2934 : reg (bv 256)) => do
      v_6048 <- getRegister v_2933;
      v_6050 <- getRegister v_2932;
      v_6052 <- eval (handleImmediateWithSignExtend v_2931 8 8);
      setRegister (lhs.of_reg v_2934) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_6048 0 64) (extract v_6050 0 64) v_6052) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_6048 64 128) (extract v_6050 64 128) v_6052) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_6048 128 192) (extract v_6050 128 192) v_6052) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_6048 192 256) (extract v_6050 192 256) v_6052) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2913 : imm int) (v_2912 : Mem) (v_2916 : reg (bv 128)) (v_2917 : reg (bv 128)) => do
      v_11452 <- getRegister v_2916;
      v_11454 <- evaluateAddress v_2912;
      v_11455 <- load v_11454 16;
      v_11457 <- eval (handleImmediateWithSignExtend v_2913 8 8);
      setRegister (lhs.of_reg v_2917) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_11452 0 64) (extract v_11455 0 64) v_11457) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_11452 64 128) (extract v_11455 64 128) v_11457) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2926 : imm int) (v_2925 : Mem) (v_2927 : reg (bv 256)) (v_2928 : reg (bv 256)) => do
      v_11468 <- getRegister v_2927;
      v_11470 <- evaluateAddress v_2925;
      v_11471 <- load v_11470 32;
      v_11473 <- eval (handleImmediateWithSignExtend v_2926 8 8);
      setRegister (lhs.of_reg v_2928) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_11468 0 64) (extract v_11471 0 64) v_11473) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_11468 64 128) (extract v_11471 64 128) v_11473) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_11468 128 192) (extract v_11471 128 192) v_11473) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_11468 192 256) (extract v_11471 192 256) v_11473) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
