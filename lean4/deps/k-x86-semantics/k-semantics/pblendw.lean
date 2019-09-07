def pblendw1 : instruction :=
  definst "pblendw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister xmm_2;
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 0) (extract v_4 0 16) (extract v_6 0 16)) (concat (mux (isBitClear v_3 1) (extract v_4 16 32) (extract v_6 16 32)) (concat (mux (isBitClear v_3 2) (extract v_4 32 48) (extract v_6 32 48)) (concat (mux (isBitClear v_3 3) (extract v_4 48 64) (extract v_6 48 64)) (concat (mux (isBitClear v_3 4) (extract v_4 64 80) (extract v_6 64 80)) (concat (mux (isBitClear v_3 5) (extract v_4 80 96) (extract v_6 80 96)) (concat (mux (isBitClear v_3 6) (extract v_4 96 112) (extract v_6 96 112)) (mux (isBitClear v_3 7) (extract v_4 112 128) (extract v_6 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister xmm_2;
      v_5 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 0) (extract v_4 0 16) (extract v_5 0 16)) (concat (mux (isBitClear v_3 1) (extract v_4 16 32) (extract v_5 16 32)) (concat (mux (isBitClear v_3 2) (extract v_4 32 48) (extract v_5 32 48)) (concat (mux (isBitClear v_3 3) (extract v_4 48 64) (extract v_5 48 64)) (concat (mux (isBitClear v_3 4) (extract v_4 64 80) (extract v_5 64 80)) (concat (mux (isBitClear v_3 5) (extract v_4 80 96) (extract v_5 80 96)) (concat (mux (isBitClear v_3 6) (extract v_4 96 112) (extract v_5 96 112)) (mux (isBitClear v_3 7) (extract v_4 112 128) (extract v_5 112 128)))))))));
      pure ()
    pat_end
