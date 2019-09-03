def vpextrw1 : instruction :=
  definst "vpextrw" $ do
    pattern fun (v_3130 : imm int) (v_3134 : reg (bv 128)) (v_3135 : reg (bv 32)) => do
      v_8930 <- getRegister v_3134;
      v_8933 <- eval (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3130 8 8) 5 8));
      setRegister (lhs.of_reg v_3135) (concat (expression.bv_nat 16 0) (extract (lshr v_8930 (uvalueMInt (extract (shl v_8933 4) 0 (bitwidthMInt v_8933)))) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3136 : imm int) (v_3140 : reg (bv 128)) (v_3141 : reg (bv 64)) => do
      v_8942 <- getRegister v_3140;
      v_8945 <- eval (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3136 8 8) 5 8));
      setRegister (lhs.of_reg v_3141) (concat (expression.bv_nat 48 0) (extract (lshr v_8942 (uvalueMInt (extract (shl v_8945 4) 0 (bitwidthMInt v_8945)))) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3125 : imm int) (v_3129 : reg (bv 128)) (v_3128 : Mem) => do
      v_20396 <- evaluateAddress v_3128;
      v_20397 <- getRegister v_3129;
      v_20400 <- eval (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3125 8 8) 5 8));
      store v_20396 (extract (lshr v_20397 (uvalueMInt (extract (shl v_20400 4) 0 (bitwidthMInt v_20400)))) 112 128) 2;
      pure ()
    pat_end
