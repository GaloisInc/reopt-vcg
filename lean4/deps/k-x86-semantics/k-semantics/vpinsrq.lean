def vpinsrq1 : instruction :=
  definst "vpinsrq" $ do
    pattern fun (v_3315 : imm int) (v_3321 : reg (bv 64)) (v_3319 : reg (bv 128)) (v_3320 : reg (bv 128)) => do
      v_10048 <- getRegister v_3319;
      v_10051 <- eval (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3315 8 8) 7 8));
      v_10055 <- eval (uvalueMInt (extract (shl v_10051 6) 0 (bitwidthMInt v_10051)));
      v_10057 <- eval (extract (shl (expression.bv_nat 128 18446744073709551615) v_10055) 0 128);
      v_10062 <- getRegister v_3321;
      v_10063 <- eval (concat (expression.bv_nat 64 0) v_10062);
      setRegister (lhs.of_reg v_3320) (bv_or (bv_and v_10048 (bv_xor v_10057 (mi (bitwidthMInt v_10057) -1))) (bv_and (extract (shl v_10063 v_10055) 0 (bitwidthMInt v_10063)) v_10057));
      pure ()
    pat_end;
    pattern fun (v_3309 : imm int) (v_3312 : Mem) (v_3313 : reg (bv 128)) (v_3314 : reg (bv 128)) => do
      v_19014 <- getRegister v_3313;
      v_19017 <- eval (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3309 8 8) 7 8));
      v_19021 <- eval (uvalueMInt (extract (shl v_19017 6) 0 (bitwidthMInt v_19017)));
      v_19023 <- eval (extract (shl (expression.bv_nat 128 18446744073709551615) v_19021) 0 128);
      v_19028 <- evaluateAddress v_3312;
      v_19029 <- load v_19028 8;
      v_19030 <- eval (concat (expression.bv_nat 64 0) v_19029);
      setRegister (lhs.of_reg v_3314) (bv_or (bv_and v_19014 (bv_xor v_19023 (mi (bitwidthMInt v_19023) -1))) (bv_and (extract (shl v_19030 v_19021) 0 (bitwidthMInt v_19030)) v_19023));
      pure ()
    pat_end
