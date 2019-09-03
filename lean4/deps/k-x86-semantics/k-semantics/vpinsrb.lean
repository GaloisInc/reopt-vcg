def vpinsrb1 : instruction :=
  definst "vpinsrb" $ do
    pattern fun (v_3289 : imm int) (v_3295 : reg (bv 32)) (v_3293 : reg (bv 128)) (v_3294 : reg (bv 128)) => do
      v_9992 <- getRegister v_3293;
      v_9995 <- eval (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3289 8 8) 4 8));
      v_9999 <- eval (uvalueMInt (extract (shl v_9995 3) 0 (bitwidthMInt v_9995)));
      v_10001 <- eval (extract (shl (expression.bv_nat 128 255) v_9999) 0 128);
      v_10006 <- getRegister v_3295;
      v_10007 <- eval (concat (expression.bv_nat 96 0) v_10006);
      setRegister (lhs.of_reg v_3294) (bv_or (bv_and v_9992 (bv_xor v_10001 (mi (bitwidthMInt v_10001) -1))) (bv_and (extract (shl v_10007 v_9999) 0 (bitwidthMInt v_10007)) v_10001));
      pure ()
    pat_end;
    pattern fun (v_3283 : imm int) (v_3286 : Mem) (v_3287 : reg (bv 128)) (v_3288 : reg (bv 128)) => do
      v_18968 <- getRegister v_3287;
      v_18971 <- eval (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3283 8 8) 4 8));
      v_18975 <- eval (uvalueMInt (extract (shl v_18971 3) 0 (bitwidthMInt v_18971)));
      v_18977 <- eval (extract (shl (expression.bv_nat 128 255) v_18975) 0 128);
      v_18982 <- evaluateAddress v_3286;
      v_18983 <- load v_18982 1;
      v_18984 <- eval (concat (expression.bv_nat 120 0) v_18983);
      setRegister (lhs.of_reg v_3288) (bv_or (bv_and v_18968 (bv_xor v_18977 (mi (bitwidthMInt v_18977) -1))) (bv_and (extract (shl v_18984 v_18975) 0 (bitwidthMInt v_18984)) v_18977));
      pure ()
    pat_end
