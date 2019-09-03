def vpextrb1 : instruction :=
  definst "vpextrb" $ do
    pattern fun (v_3091 : imm int) (v_3095 : reg (bv 128)) (v_3096 : reg (bv 32)) => do
      v_8869 <- getRegister v_3095;
      v_8872 <- eval (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3091 8 8) 4 8));
      setRegister (lhs.of_reg v_3096) (concat (expression.bv_nat 24 0) (extract (lshr v_8869 (uvalueMInt (extract (shl v_8872 3) 0 (bitwidthMInt v_8872)))) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3097 : imm int) (v_3101 : reg (bv 128)) (v_3102 : reg (bv 64)) => do
      v_8881 <- getRegister v_3101;
      v_8884 <- eval (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3097 8 8) 4 8));
      setRegister (lhs.of_reg v_3102) (concat (expression.bv_nat 56 0) (extract (lshr v_8881 (uvalueMInt (extract (shl v_8884 3) 0 (bitwidthMInt v_8884)))) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3086 : imm int) (v_3090 : reg (bv 128)) (v_3089 : Mem) => do
      v_20360 <- evaluateAddress v_3089;
      v_20361 <- getRegister v_3090;
      v_20364 <- eval (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3086 8 8) 4 8));
      store v_20360 (extract (lshr v_20361 (uvalueMInt (extract (shl v_20364 3) 0 (bitwidthMInt v_20364)))) 120 128) 1;
      pure ()
    pat_end
