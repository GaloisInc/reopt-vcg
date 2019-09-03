def vpslldq1 : instruction :=
  definst "vpslldq" $ do
    pattern fun (v_3079 : imm int) (v_3081 : reg (bv 128)) (v_3082 : reg (bv 128)) => do
      v_7732 <- getRegister v_3081;
      v_7733 <- eval (handleImmediateWithSignExtend v_3079 8 8);
      v_7736 <- eval (mux (ugt v_7733 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7733));
      setRegister (lhs.of_reg v_3082) (extract (shl v_7732 (uvalueMInt (extract (shl v_7736 3) 0 (bitwidthMInt v_7736)))) 0 128);
      pure ()
    pat_end;
    pattern fun (v_3085 : imm int) (v_3088 : reg (bv 256)) (v_3089 : reg (bv 256)) => do
      v_7744 <- getRegister v_3088;
      v_7746 <- eval (handleImmediateWithSignExtend v_3085 8 8);
      v_7749 <- eval (mux (ugt v_7746 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7746));
      v_7753 <- eval (uvalueMInt (extract (shl v_7749 3) 0 (bitwidthMInt v_7749)));
      setRegister (lhs.of_reg v_3089) (concat (extract (shl (extract v_7744 0 128) v_7753) 0 128) (extract (shl (extract v_7744 128 256) v_7753) 0 128));
      pure ()
    pat_end
