def vinserti128 : instruction :=
  definst "vinserti128" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      setRegister (lhs.of_reg ymm_3) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) (concat (extract v_4 0 128) v_6) (concat v_6 (extract v_4 128 256)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg ymm_3) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) (concat (extract v_4 0 128) v_5) (concat v_5 (extract v_4 128 256)));
      pure ()
    pat_end
