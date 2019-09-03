def vcmpsd1 : instruction :=
  definst "vcmpsd" $ do
    pattern fun (v_2970 : imm int) (v_2974 : reg (bv 128)) (v_2975 : reg (bv 128)) (v_2976 : reg (bv 128)) => do
      v_6171 <- getRegister v_2975;
      v_6174 <- getRegister v_2974;
      setRegister (lhs.of_reg v_2976) (concat (extract v_6171 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_6171 64 128) (extract v_6174 64 128) (handleImmediateWithSignExtend v_2970 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2965 : imm int) (v_2964 : Mem) (v_2968 : reg (bv 128)) (v_2969 : reg (bv 128)) => do
      v_11576 <- getRegister v_2968;
      v_11579 <- evaluateAddress v_2964;
      v_11580 <- load v_11579 8;
      setRegister (lhs.of_reg v_2969) (concat (extract v_11576 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_11576 64 128) v_11580 (handleImmediateWithSignExtend v_2965 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
