def pslldq1 : instruction :=
  definst "pslldq" $ do
    pattern fun (v_2983 : imm int) (v_2984 : reg (bv 128)) => do
      v_7578 <- getRegister v_2984;
      v_7579 <- eval (handleImmediateWithSignExtend v_2983 8 8);
      v_7582 <- eval (mux (ugt v_7579 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7579));
      setRegister (lhs.of_reg v_2984) (extract (shl v_7578 (uvalueMInt (extract (shl v_7582 3) 0 (bitwidthMInt v_7582)))) 0 128);
      pure ()
    pat_end
