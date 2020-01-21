def vcvtps2ph : instruction :=
  definst "vcvtps2ph" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      store v_3 (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 0 32) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 32 64) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 64 96) 24 8) v_5) 16) (Float2MInt (Float2Half (MInt2Float (extract v_4 96 128) 24 8) v_5) 16)))) 8;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      setRegister (lhs.of_reg xmm_2) (concat (expression.bv_nat 64 0) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 0 32) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 32 64) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 64 96) 24 8) v_4) 16) (Float2MInt (Float2Half (MInt2Float (extract v_3 96 128) 24 8) v_4) 16)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg ymm_1);
      v_5 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      store v_3 (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 0 32) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 32 64) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 64 96) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 96 128) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 128 160) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 160 192) 24 8) v_5) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_4 192 224) 24 8) v_5) 16) (Float2MInt (Float2Half (MInt2Float (extract v_4 224 256) 24 8) v_5) 16)))))))) 16;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      setRegister (lhs.of_reg xmm_2) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 0 32) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 32 64) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 64 96) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 96 128) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 128 160) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 160 192) 24 8) v_4) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_3 192 224) 24 8) v_4) 16) (Float2MInt (Float2Half (MInt2Float (extract v_3 224 256) 24 8) v_4) 16))))))));
      pure ()
    pat_end
