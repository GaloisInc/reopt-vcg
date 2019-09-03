def vpinsrd1 : instruction :=
  definst "vpinsrd" $ do
    pattern fun (v_3302 : imm int) (v_3308 : reg (bv 32)) (v_3306 : reg (bv 128)) (v_3307 : reg (bv 128)) => do
      v_10020 <- getRegister v_3306;
      v_10023 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3302 8 8) 6 8));
      v_10027 <- eval (uvalueMInt (extract (shl v_10023 5) 0 (bitwidthMInt v_10023)));
      v_10029 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_10027) 0 128);
      v_10034 <- getRegister v_3308;
      v_10035 <- eval (concat (expression.bv_nat 96 0) v_10034);
      setRegister (lhs.of_reg v_3307) (bv_or (bv_and v_10020 (bv_xor v_10029 (mi (bitwidthMInt v_10029) -1))) (bv_and (extract (shl v_10035 v_10027) 0 (bitwidthMInt v_10035)) v_10029));
      pure ()
    pat_end;
    pattern fun (v_3296 : imm int) (v_3299 : Mem) (v_3300 : reg (bv 128)) (v_3301 : reg (bv 128)) => do
      v_18991 <- getRegister v_3300;
      v_18994 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3296 8 8) 6 8));
      v_18998 <- eval (uvalueMInt (extract (shl v_18994 5) 0 (bitwidthMInt v_18994)));
      v_19000 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_18998) 0 128);
      v_19005 <- evaluateAddress v_3299;
      v_19006 <- load v_19005 4;
      v_19007 <- eval (concat (expression.bv_nat 96 0) v_19006);
      setRegister (lhs.of_reg v_3301) (bv_or (bv_and v_18991 (bv_xor v_19000 (mi (bitwidthMInt v_19000) -1))) (bv_and (extract (shl v_19007 v_18998) 0 (bitwidthMInt v_19007)) v_19000));
      pure ()
    pat_end
