def vshufpd : instruction :=
  definst "vshufpd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      v_7 <- getRegister (lhs.of_reg xmm_2);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) (extract v_6 0 64) (extract v_6 64 128)) (mux (isBitSet v_4 7) (extract v_7 0 64) (extract v_7 64 128)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 32;
      v_7 <- getRegister (lhs.of_reg ymm_2);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitSet v_4 4) (extract v_6 0 64) (extract v_6 64 128)) (concat (mux (isBitSet v_4 5) (extract v_7 0 64) (extract v_7 64 128)) (concat (mux (isBitSet v_4 6) (extract v_6 128 192) (extract v_6 192 256)) (mux (isBitSet v_4 7) (extract v_7 128 192) (extract v_7 192 256)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      v_6 <- getRegister (lhs.of_reg xmm_2);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) (extract v_5 0 64) (extract v_5 64 128)) (mux (isBitSet v_4 7) (extract v_6 0 64) (extract v_6 64 128)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      v_6 <- getRegister (lhs.of_reg ymm_2);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitSet v_4 4) (extract v_5 0 64) (extract v_5 64 128)) (concat (mux (isBitSet v_4 5) (extract v_6 0 64) (extract v_6 64 128)) (concat (mux (isBitSet v_4 6) (extract v_5 128 192) (extract v_5 192 256)) (mux (isBitSet v_4 7) (extract v_6 128 192) (extract v_6 192 256)))));
      pure ()
    pat_end
