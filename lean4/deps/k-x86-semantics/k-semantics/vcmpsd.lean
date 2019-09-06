def vcmpsd1 : instruction :=
  definst "vcmpsd" $ do
    pattern fun (v_3048 : imm int) (v_3052 : reg (bv 128)) (v_3053 : reg (bv 128)) (v_3054 : reg (bv 128)) => do
      v_5667 <- getRegister v_3053;
      v_5670 <- getRegister v_3052;
      setRegister (lhs.of_reg v_3054) (concat (extract v_5667 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5667 64 128) (extract v_5670 64 128) (handleImmediateWithSignExtend v_3048 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3042 : imm int) (v_3043 : Mem) (v_3046 : reg (bv 128)) (v_3047 : reg (bv 128)) => do
      v_9829 <- getRegister v_3046;
      v_9832 <- evaluateAddress v_3043;
      v_9833 <- load v_9832 8;
      setRegister (lhs.of_reg v_3047) (concat (extract v_9829 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_9829 64 128) v_9833 (handleImmediateWithSignExtend v_3042 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
