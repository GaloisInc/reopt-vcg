def vpermpd1 : instruction :=
  definst "vpermpd" $ do
    pattern fun (v_3058 : imm int) (v_3062 : reg (bv 256)) (v_3063 : reg (bv 256)) => do
      v_8720 <- getRegister v_3062;
      v_8721 <- eval (handleImmediateWithSignExtend v_3058 8 8);
      v_8723 <- eval (concat (expression.bv_nat 254 0) (extract v_8721 0 2));
      v_8731 <- eval (concat (expression.bv_nat 254 0) (extract v_8721 2 4));
      v_8739 <- eval (concat (expression.bv_nat 254 0) (extract v_8721 4 6));
      v_8747 <- eval (concat (expression.bv_nat 254 0) (extract v_8721 6 8));
      setRegister (lhs.of_reg v_3063) (concat (extract (lshr v_8720 (uvalueMInt (extract (shl v_8723 6) 0 (bitwidthMInt v_8723)))) 192 256) (concat (extract (lshr v_8720 (uvalueMInt (extract (shl v_8731 6) 0 (bitwidthMInt v_8731)))) 192 256) (concat (extract (lshr v_8720 (uvalueMInt (extract (shl v_8739 6) 0 (bitwidthMInt v_8739)))) 192 256) (extract (lshr v_8720 (uvalueMInt (extract (shl v_8747 6) 0 (bitwidthMInt v_8747)))) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3053 : imm int) (v_3056 : Mem) (v_3057 : reg (bv 256)) => do
      v_17846 <- evaluateAddress v_3056;
      v_17847 <- load v_17846 32;
      v_17848 <- eval (handleImmediateWithSignExtend v_3053 8 8);
      v_17850 <- eval (concat (expression.bv_nat 254 0) (extract v_17848 0 2));
      v_17858 <- eval (concat (expression.bv_nat 254 0) (extract v_17848 2 4));
      v_17866 <- eval (concat (expression.bv_nat 254 0) (extract v_17848 4 6));
      v_17874 <- eval (concat (expression.bv_nat 254 0) (extract v_17848 6 8));
      setRegister (lhs.of_reg v_3057) (concat (extract (lshr v_17847 (uvalueMInt (extract (shl v_17850 6) 0 (bitwidthMInt v_17850)))) 192 256) (concat (extract (lshr v_17847 (uvalueMInt (extract (shl v_17858 6) 0 (bitwidthMInt v_17858)))) 192 256) (concat (extract (lshr v_17847 (uvalueMInt (extract (shl v_17866 6) 0 (bitwidthMInt v_17866)))) 192 256) (extract (lshr v_17847 (uvalueMInt (extract (shl v_17874 6) 0 (bitwidthMInt v_17874)))) 192 256))));
      pure ()
    pat_end
