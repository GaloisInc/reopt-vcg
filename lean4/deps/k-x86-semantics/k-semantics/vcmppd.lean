def vcmppd1 : instruction :=
  definst "vcmppd" $ do
    pattern fun (v_2905 : imm int) (v_2909 : reg (bv 128)) (v_2910 : reg (bv 128)) (v_2911 : reg (bv 128)) => do
      v_5568 <- getRegister v_2910;
      v_5570 <- getRegister v_2909;
      v_5572 <- eval (handleImmediateWithSignExtend v_2905 8 8);
      setRegister (lhs.of_reg v_2911) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5568 0 64) (extract v_5570 0 64) v_5572) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5568 64 128) (extract v_5570 64 128) v_5572) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2918 : imm int) (v_2920 : reg (bv 256)) (v_2921 : reg (bv 256)) (v_2922 : reg (bv 256)) => do
      v_5589 <- getRegister v_2921;
      v_5591 <- getRegister v_2920;
      v_5593 <- eval (handleImmediateWithSignExtend v_2918 8 8);
      setRegister (lhs.of_reg v_2922) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5589 0 64) (extract v_5591 0 64) v_5593) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5589 64 128) (extract v_5591 64 128) v_5593) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5589 128 192) (extract v_5591 128 192) v_5593) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5589 192 256) (extract v_5591 192 256) v_5593) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2900 : imm int) (v_2899 : Mem) (v_2903 : reg (bv 128)) (v_2904 : reg (bv 128)) => do
      v_9910 <- getRegister v_2903;
      v_9912 <- evaluateAddress v_2899;
      v_9913 <- load v_9912 16;
      v_9915 <- eval (handleImmediateWithSignExtend v_2900 8 8);
      setRegister (lhs.of_reg v_2904) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9910 0 64) (extract v_9913 0 64) v_9915) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9910 64 128) (extract v_9913 64 128) v_9915) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2913 : imm int) (v_2912 : Mem) (v_2914 : reg (bv 256)) (v_2915 : reg (bv 256)) => do
      v_9926 <- getRegister v_2914;
      v_9928 <- evaluateAddress v_2912;
      v_9929 <- load v_9928 32;
      v_9931 <- eval (handleImmediateWithSignExtend v_2913 8 8);
      setRegister (lhs.of_reg v_2915) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9926 0 64) (extract v_9929 0 64) v_9931) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9926 64 128) (extract v_9929 64 128) v_9931) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9926 128 192) (extract v_9929 128 192) v_9931) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9926 192 256) (extract v_9929 192 256) v_9931) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
