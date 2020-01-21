def roundsd : instruction :=
  definst "roundsd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- evaluateAddress mem_1;
      v_5 <- load v_4 8;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_5 (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_4 64 128) (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end
