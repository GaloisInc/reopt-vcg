def vcmpss1 : instruction :=
  definst "vcmpss" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister xmm_2;
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 4;
      setRegister (lhs.of_reg xmm_3) (concat (extract v_4 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_4 96 128) v_6 (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister xmm_2;
      v_5 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_3) (concat (extract v_4 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_4 96 128) (extract v_5 96 128) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end
