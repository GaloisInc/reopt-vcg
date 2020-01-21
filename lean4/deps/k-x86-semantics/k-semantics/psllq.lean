def psllq : instruction :=
  definst "psllq" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      v_3 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_2 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_3 0 64) v_2) 0 64) (extract (shl (extract v_3 64 128) v_2) 0 64)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_5 0 64) v_4) 0 64) (extract (shl (extract v_5 64 128) v_4) 0 64)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- eval (extract v_2 64 128);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_4 0 64) v_3) 0 64) (extract (shl (extract v_4 64 128) v_3) 0 64)));
      pure ()
    pat_end
