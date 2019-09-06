def vcmppd1 : instruction :=
  definst "vcmppd" $ do
    pattern fun (v_2996 : imm int) (v_3000 : reg (bv 128)) (v_3001 : reg (bv 128)) (v_3002 : reg (bv 128)) => do
      v_5523 <- getRegister v_3001;
      v_5525 <- getRegister v_3000;
      v_5527 <- eval (handleImmediateWithSignExtend v_2996 8 8);
      setRegister (lhs.of_reg v_3002) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5523 0 64) (extract v_5525 0 64) v_5527) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5523 64 128) (extract v_5525 64 128) v_5527) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3009 : imm int) (v_3010 : reg (bv 256)) (v_3011 : reg (bv 256)) (v_3012 : reg (bv 256)) => do
      v_5544 <- getRegister v_3011;
      v_5546 <- getRegister v_3010;
      v_5548 <- eval (handleImmediateWithSignExtend v_3009 8 8);
      setRegister (lhs.of_reg v_3012) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5544 0 64) (extract v_5546 0 64) v_5548) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5544 64 128) (extract v_5546 64 128) v_5548) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5544 128 192) (extract v_5546 128 192) v_5548) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5544 192 256) (extract v_5546 192 256) v_5548) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2990 : imm int) (v_2991 : Mem) (v_2994 : reg (bv 128)) (v_2995 : reg (bv 128)) => do
      v_9705 <- getRegister v_2994;
      v_9707 <- evaluateAddress v_2991;
      v_9708 <- load v_9707 16;
      v_9710 <- eval (handleImmediateWithSignExtend v_2990 8 8);
      setRegister (lhs.of_reg v_2995) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9705 0 64) (extract v_9708 0 64) v_9710) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9705 64 128) (extract v_9708 64 128) v_9710) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3003 : imm int) (v_3004 : Mem) (v_3005 : reg (bv 256)) (v_3006 : reg (bv 256)) => do
      v_9721 <- getRegister v_3005;
      v_9723 <- evaluateAddress v_3004;
      v_9724 <- load v_9723 32;
      v_9726 <- eval (handleImmediateWithSignExtend v_3003 8 8);
      setRegister (lhs.of_reg v_3006) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9721 0 64) (extract v_9724 0 64) v_9726) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9721 64 128) (extract v_9724 64 128) v_9726) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9721 128 192) (extract v_9724 128 192) v_9726) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9721 192 256) (extract v_9724 192 256) v_9726) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
