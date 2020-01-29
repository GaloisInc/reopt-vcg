def pblendw : instruction :=
  definst "pblendw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 16)) <- eval (extract v_7 0 16);
      (v_9 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_7 16 32);
      (v_11 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_7 32 48);
      (v_13 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_14 : expression (bv 16)) <- eval (extract v_7 48 64);
      (v_15 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_16 : expression (bv 16)) <- eval (extract v_7 64 80);
      (v_17 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_18 : expression (bv 16)) <- eval (extract v_7 80 96);
      (v_19 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_20 : expression (bv 16)) <- eval (extract v_7 96 112);
      (v_21 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_22 : expression (bv 16)) <- eval (extract v_7 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 0) v_5 v_8) (concat (mux (isBitClear v_3 1) v_9 v_10) (concat (mux (isBitClear v_3 2) v_11 v_12) (concat (mux (isBitClear v_3 3) v_13 v_14) (concat (mux (isBitClear v_3 4) v_15 v_16) (concat (mux (isBitClear v_3 5) v_17 v_18) (concat (mux (isBitClear v_3 6) v_19 v_20) (mux (isBitClear v_3 7) v_21 v_22))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_21 : expression (bv 16)) <- eval (extract v_6 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 0) v_5 v_7) (concat (mux (isBitClear v_3 1) v_8 v_9) (concat (mux (isBitClear v_3 2) v_10 v_11) (concat (mux (isBitClear v_3 3) v_12 v_13) (concat (mux (isBitClear v_3 4) v_14 v_15) (concat (mux (isBitClear v_3 5) v_16 v_17) (concat (mux (isBitClear v_3 6) v_18 v_19) (mux (isBitClear v_3 7) v_20 v_21))))))));
      pure ()
    pat_end
