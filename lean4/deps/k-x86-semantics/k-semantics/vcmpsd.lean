def vcmpsd1 : instruction :=
  definst "vcmpsd" $ do
    pattern fun (v_2957 : imm int) (v_2961 : reg (bv 128)) (v_2962 : reg (bv 128)) (v_2963 : reg (bv 128)) => do
      v_5712 <- getRegister v_2962;
      v_5715 <- getRegister v_2961;
      setRegister (lhs.of_reg v_2963) (concat (extract v_5712 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5712 64 128) (extract v_5715 64 128) (handleImmediateWithSignExtend v_2957 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2952 : imm int) (v_2951 : Mem) (v_2955 : reg (bv 128)) (v_2956 : reg (bv 128)) => do
      v_10034 <- getRegister v_2955;
      v_10037 <- evaluateAddress v_2951;
      v_10038 <- load v_10037 8;
      setRegister (lhs.of_reg v_2956) (concat (extract v_10034 0 64) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_10034 64 128) v_10038 (handleImmediateWithSignExtend v_2952 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
