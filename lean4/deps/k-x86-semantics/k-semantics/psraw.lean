def psraw : instruction :=
  definst "psraw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_3) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_3));
      setRegister (lhs.of_reg xmm_1) (concat (ashr (extract v_2 0 16) v_4) (concat (ashr (extract v_2 16 32) v_4) (concat (ashr (extract v_2 32 48) v_4) (concat (ashr (extract v_2 48 64) v_4) (concat (ashr (extract v_2 64 80) v_4) (concat (ashr (extract v_2 80 96) v_4) (concat (ashr (extract v_2 96 112) v_4) (ashr (extract v_2 112 128) v_4))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (mux (ugt (extract v_4 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_4 112 128));
      setRegister (lhs.of_reg xmm_1) (concat (ashr (extract v_2 0 16) v_5) (concat (ashr (extract v_2 16 32) v_5) (concat (ashr (extract v_2 32 48) v_5) (concat (ashr (extract v_2 48 64) v_5) (concat (ashr (extract v_2 64 80) v_5) (concat (ashr (extract v_2 80 96) v_5) (concat (ashr (extract v_2 96 112) v_5) (ashr (extract v_2 112 128) v_5))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (mux (ugt (extract v_3 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_3 112 128));
      setRegister (lhs.of_reg xmm_1) (concat (ashr (extract v_2 0 16) v_4) (concat (ashr (extract v_2 16 32) v_4) (concat (ashr (extract v_2 32 48) v_4) (concat (ashr (extract v_2 48 64) v_4) (concat (ashr (extract v_2 64 80) v_4) (concat (ashr (extract v_2 80 96) v_4) (concat (ashr (extract v_2 96 112) v_4) (ashr (extract v_2 112 128) v_4))))))));
      pure ()
    pat_end
