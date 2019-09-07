def blendpd1 : instruction :=
  definst "blendpd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister xmm_2;
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 6) (extract v_4 0 64) (extract v_6 0 64)) (mux (isBitClear v_3 7) (extract v_4 64 128) (extract v_6 64 128)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister xmm_2;
      v_5 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 6) (extract v_4 0 64) (extract v_5 0 64)) (mux (isBitClear v_3 7) (extract v_4 64 128) (extract v_5 64 128)));
      pure ()
    pat_end
