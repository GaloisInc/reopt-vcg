def vpslldq : instruction :=
  definst "vpslldq" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_2) (extract (shl v_3 (extract (shl (mux (ugt v_4 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_4)) (expression.bv_nat 128 3)) 0 128)) 0 128);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (extract (shl (mux (ugt v_4 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_4)) (expression.bv_nat 128 3)) 0 128);
      setRegister (lhs.of_reg ymm_2) (concat (extract (shl (extract v_3 0 128) v_5) 0 128) (extract (shl (extract v_3 128 256) v_5) 0 128));
      pure ()
    pat_end
