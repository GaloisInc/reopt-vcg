def psrad1 : instruction :=
  definst "psrad" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_3) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_3));
      setRegister (lhs.of_reg xmm_1) (concat (ashr (extract v_2 0 32) v_4) (concat (ashr (extract v_2 32 64) v_4) (concat (ashr (extract v_2 64 96) v_4) (ashr (extract v_2 96 128) v_4))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (mux (ugt (extract v_4 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_4 96 128));
      setRegister (lhs.of_reg xmm_1) (concat (ashr (extract v_2 0 32) v_5) (concat (ashr (extract v_2 32 64) v_5) (concat (ashr (extract v_2 64 96) v_5) (ashr (extract v_2 96 128) v_5))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      v_4 <- eval (mux (ugt (extract v_3 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_3 96 128));
      setRegister (lhs.of_reg xmm_1) (concat (ashr (extract v_2 0 32) v_4) (concat (ashr (extract v_2 32 64) v_4) (concat (ashr (extract v_2 64 96) v_4) (ashr (extract v_2 96 128) v_4))));
      pure ()
    pat_end
