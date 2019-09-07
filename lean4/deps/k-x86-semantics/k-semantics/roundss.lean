def roundss1 : instruction :=
  definst "roundss" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_2;
      v_4 <- evaluateAddress mem_1;
      v_5 <- load v_4 4;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_5 (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_2;
      v_4 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_4 96 128) (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end
