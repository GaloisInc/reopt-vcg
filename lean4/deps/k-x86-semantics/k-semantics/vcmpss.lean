def vcmpss1 : instruction :=
  definst "vcmpss" $ do
    pattern fun (v_3061 : imm int) (v_3065 : reg (bv 128)) (v_3066 : reg (bv 128)) (v_3067 : reg (bv 128)) => do
      v_5684 <- getRegister v_3066;
      v_5687 <- getRegister v_3065;
      setRegister (lhs.of_reg v_3067) (concat (extract v_5684 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5684 96 128) (extract v_5687 96 128) (handleImmediateWithSignExtend v_3061 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3055 : imm int) (v_3056 : Mem) (v_3059 : reg (bv 128)) (v_3060 : reg (bv 128)) => do
      v_9840 <- getRegister v_3059;
      v_9843 <- evaluateAddress v_3056;
      v_9844 <- load v_9843 4;
      setRegister (lhs.of_reg v_3060) (concat (extract v_9840 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9840 96 128) v_9844 (handleImmediateWithSignExtend v_3055 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end
