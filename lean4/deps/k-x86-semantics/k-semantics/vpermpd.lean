def vpermpd1 : instruction :=
  definst "vpermpd" $ do
    pattern fun (v_3073 : imm int) (v_3075 : reg (bv 256)) (v_3076 : reg (bv 256)) => do
      v_8583 <- getRegister v_3075;
      v_8584 <- eval (handleImmediateWithSignExtend v_3073 8 8);
      setRegister (lhs.of_reg v_3076) (concat (extract (lshr v_8583 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8584 0 2)) 6) 0 256))) 192 256) (concat (extract (lshr v_8583 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8584 2 4)) 6) 0 256))) 192 256) (concat (extract (lshr v_8583 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8584 4 6)) 6) 0 256))) 192 256) (extract (lshr v_8583 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8584 6 8)) 6) 0 256))) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3069 : imm int) (v_3068 : Mem) (v_3070 : reg (bv 256)) => do
      v_17337 <- evaluateAddress v_3068;
      v_17338 <- load v_17337 32;
      v_17339 <- eval (handleImmediateWithSignExtend v_3069 8 8);
      setRegister (lhs.of_reg v_3070) (concat (extract (lshr v_17338 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17339 0 2)) 6) 0 256))) 192 256) (concat (extract (lshr v_17338 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17339 2 4)) 6) 0 256))) 192 256) (concat (extract (lshr v_17338 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17339 4 6)) 6) 0 256))) 192 256) (extract (lshr v_17338 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17339 6 8)) 6) 0 256))) 192 256))));
      pure ()
    pat_end
