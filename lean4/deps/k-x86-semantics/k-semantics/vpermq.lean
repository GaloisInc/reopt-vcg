def vpermq1 : instruction :=
  definst "vpermq" $ do
    pattern fun (v_3080 : imm int) (v_3084 : reg (bv 256)) (v_3085 : reg (bv 256)) => do
      v_8826 <- getRegister v_3084;
      v_8827 <- eval (handleImmediateWithSignExtend v_3080 8 8);
      v_8829 <- eval (concat (expression.bv_nat 254 0) (extract v_8827 0 2));
      v_8837 <- eval (concat (expression.bv_nat 254 0) (extract v_8827 2 4));
      v_8845 <- eval (concat (expression.bv_nat 254 0) (extract v_8827 4 6));
      v_8853 <- eval (concat (expression.bv_nat 254 0) (extract v_8827 6 8));
      setRegister (lhs.of_reg v_3085) (concat (extract (lshr v_8826 (uvalueMInt (extract (shl v_8829 6) 0 (bitwidthMInt v_8829)))) 192 256) (concat (extract (lshr v_8826 (uvalueMInt (extract (shl v_8837 6) 0 (bitwidthMInt v_8837)))) 192 256) (concat (extract (lshr v_8826 (uvalueMInt (extract (shl v_8845 6) 0 (bitwidthMInt v_8845)))) 192 256) (extract (lshr v_8826 (uvalueMInt (extract (shl v_8853 6) 0 (bitwidthMInt v_8853)))) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3075 : imm int) (v_3078 : Mem) (v_3079 : reg (bv 256)) => do
      v_17944 <- evaluateAddress v_3078;
      v_17945 <- load v_17944 32;
      v_17946 <- eval (handleImmediateWithSignExtend v_3075 8 8);
      v_17948 <- eval (concat (expression.bv_nat 254 0) (extract v_17946 0 2));
      v_17956 <- eval (concat (expression.bv_nat 254 0) (extract v_17946 2 4));
      v_17964 <- eval (concat (expression.bv_nat 254 0) (extract v_17946 4 6));
      v_17972 <- eval (concat (expression.bv_nat 254 0) (extract v_17946 6 8));
      setRegister (lhs.of_reg v_3079) (concat (extract (lshr v_17945 (uvalueMInt (extract (shl v_17948 6) 0 (bitwidthMInt v_17948)))) 192 256) (concat (extract (lshr v_17945 (uvalueMInt (extract (shl v_17956 6) 0 (bitwidthMInt v_17956)))) 192 256) (concat (extract (lshr v_17945 (uvalueMInt (extract (shl v_17964 6) 0 (bitwidthMInt v_17964)))) 192 256) (extract (lshr v_17945 (uvalueMInt (extract (shl v_17972 6) 0 (bitwidthMInt v_17972)))) 192 256))));
      pure ()
    pat_end
