def vpinsrw1 : instruction :=
  definst "vpinsrw" $ do
    pattern fun (v_3328 : imm int) (v_3334 : reg (bv 32)) (v_3332 : reg (bv 128)) (v_3333 : reg (bv 128)) => do
      v_10076 <- getRegister v_3332;
      v_10079 <- eval (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3328 8 8) 5 8));
      v_10083 <- eval (uvalueMInt (extract (shl v_10079 4) 0 (bitwidthMInt v_10079)));
      v_10085 <- eval (extract (shl (expression.bv_nat 128 65535) v_10083) 0 128);
      v_10090 <- getRegister v_3334;
      v_10091 <- eval (concat (expression.bv_nat 96 0) v_10090);
      setRegister (lhs.of_reg v_3333) (bv_or (bv_and v_10076 (bv_xor v_10085 (mi (bitwidthMInt v_10085) -1))) (bv_and (extract (shl v_10091 v_10083) 0 (bitwidthMInt v_10091)) v_10085));
      pure ()
    pat_end;
    pattern fun (v_3322 : imm int) (v_3325 : Mem) (v_3326 : reg (bv 128)) (v_3327 : reg (bv 128)) => do
      v_19037 <- getRegister v_3326;
      v_19040 <- eval (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3322 8 8) 5 8));
      v_19044 <- eval (uvalueMInt (extract (shl v_19040 4) 0 (bitwidthMInt v_19040)));
      v_19046 <- eval (extract (shl (expression.bv_nat 128 65535) v_19044) 0 128);
      v_19051 <- evaluateAddress v_3325;
      v_19052 <- load v_19051 2;
      v_19053 <- eval (concat (expression.bv_nat 112 0) v_19052);
      setRegister (lhs.of_reg v_3327) (bv_or (bv_and v_19037 (bv_xor v_19046 (mi (bitwidthMInt v_19046) -1))) (bv_and (extract (shl v_19053 v_19044) 0 (bitwidthMInt v_19053)) v_19046));
      pure ()
    pat_end
