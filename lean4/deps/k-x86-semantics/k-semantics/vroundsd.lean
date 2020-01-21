def vroundsd : instruction :=
  definst "vroundsd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 8;
      setRegister (lhs.of_reg xmm_3) (concat (extract v_4 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_6 (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_3) (concat (extract v_4 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5 64 128) (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end
