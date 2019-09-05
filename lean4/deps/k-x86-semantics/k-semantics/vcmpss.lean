def vcmpss1 : instruction :=
  definst "vcmpss" $ do
    pattern fun (v_3036 : imm int) (v_3038 : reg (bv 128)) (v_3039 : reg (bv 128)) (v_3040 : reg (bv 128)) => do
      v_5657 <- getRegister v_3039;
      v_5660 <- getRegister v_3038;
      setRegister (lhs.of_reg v_3040) (concat (extract v_5657 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5657 96 128) (extract v_5660 96 128) (handleImmediateWithSignExtend v_3036 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3030 : imm int) (v_3031 : Mem) (v_3032 : reg (bv 128)) (v_3033 : reg (bv 128)) => do
      v_9813 <- getRegister v_3032;
      v_9816 <- evaluateAddress v_3031;
      v_9817 <- load v_9816 4;
      setRegister (lhs.of_reg v_3033) (concat (extract v_9813 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9813 96 128) v_9817 (handleImmediateWithSignExtend v_3030 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end
