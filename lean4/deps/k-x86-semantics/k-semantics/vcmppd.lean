def vcmppd1 : instruction :=
  definst "vcmppd" $ do
    pattern fun (v_2971 : imm int) (v_2973 : reg (bv 128)) (v_2974 : reg (bv 128)) (v_2975 : reg (bv 128)) => do
      v_5496 <- getRegister v_2974;
      v_5498 <- getRegister v_2973;
      v_5500 <- eval (handleImmediateWithSignExtend v_2971 8 8);
      setRegister (lhs.of_reg v_2975) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5496 0 64) (extract v_5498 0 64) v_5500) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5496 64 128) (extract v_5498 64 128) v_5500) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2984 : imm int) (v_2985 : reg (bv 256)) (v_2986 : reg (bv 256)) (v_2987 : reg (bv 256)) => do
      v_5517 <- getRegister v_2986;
      v_5519 <- getRegister v_2985;
      v_5521 <- eval (handleImmediateWithSignExtend v_2984 8 8);
      setRegister (lhs.of_reg v_2987) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5517 0 64) (extract v_5519 0 64) v_5521) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5517 64 128) (extract v_5519 64 128) v_5521) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5517 128 192) (extract v_5519 128 192) v_5521) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5517 192 256) (extract v_5519 192 256) v_5521) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2965 : imm int) (v_2966 : Mem) (v_2967 : reg (bv 128)) (v_2968 : reg (bv 128)) => do
      v_9678 <- getRegister v_2967;
      v_9680 <- evaluateAddress v_2966;
      v_9681 <- load v_9680 16;
      v_9683 <- eval (handleImmediateWithSignExtend v_2965 8 8);
      setRegister (lhs.of_reg v_2968) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9678 0 64) (extract v_9681 0 64) v_9683) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9678 64 128) (extract v_9681 64 128) v_9683) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2978 : imm int) (v_2979 : Mem) (v_2980 : reg (bv 256)) (v_2981 : reg (bv 256)) => do
      v_9694 <- getRegister v_2980;
      v_9696 <- evaluateAddress v_2979;
      v_9697 <- load v_9696 32;
      v_9699 <- eval (handleImmediateWithSignExtend v_2978 8 8);
      setRegister (lhs.of_reg v_2981) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9694 0 64) (extract v_9697 0 64) v_9699) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9694 64 128) (extract v_9697 64 128) v_9699) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9694 128 192) (extract v_9697 128 192) v_9699) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9694 192 256) (extract v_9697 192 256) v_9699) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
