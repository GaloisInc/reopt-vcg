def vroundsd : instruction :=
  definst "vroundsd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 8;
      setRegister (lhs.of_reg xmm_3) (concat v_5 (/- (_,_) -/  cvt_double_to_int64_rm v_7 (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      setRegister (lhs.of_reg xmm_3) (concat v_5 (/- (_,_) -/  cvt_double_to_int64_rm v_7 (handleImmediateWithSignExtend imm_0 8 8)));
      pure ()
    pat_end
