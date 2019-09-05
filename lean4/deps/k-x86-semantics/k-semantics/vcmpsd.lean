def vcmpsd1 : instruction :=
  definst "vcmpsd" $ do
    pattern fun (v_3023 : imm int) (v_3025 : reg (bv 128)) (v_3026 : reg (bv 128)) (v_3027 : reg (bv 128)) => do
      v_5640 <- getRegister v_3026;
      v_5643 <- getRegister v_3025;
      setRegister (lhs.of_reg v_3027) (concat (extract v_5640 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5640 64 128) (extract v_5643 64 128) (handleImmediateWithSignExtend v_3023 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3017 : imm int) (v_3018 : Mem) (v_3019 : reg (bv 128)) (v_3020 : reg (bv 128)) => do
      v_9802 <- getRegister v_3019;
      v_9805 <- evaluateAddress v_3018;
      v_9806 <- load v_9805 8;
      setRegister (lhs.of_reg v_3020) (concat (extract v_9802 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9802 64 128) v_9806 (handleImmediateWithSignExtend v_3017 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
