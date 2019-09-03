def psrldq1 : instruction :=
  definst "psrldq" $ do
    pattern fun (v_3058 : imm int) (v_3059 : reg (bv 128)) => do
      v_7902 <- getRegister v_3059;
      v_7903 <- eval (handleImmediateWithSignExtend v_3058 8 8);
      v_7906 <- eval (mux (ugt v_7903 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7903));
      setRegister (lhs.of_reg v_3059) (lshr v_7902 (uvalueMInt (extract (shl v_7906 3) 0 (bitwidthMInt v_7906))));
      pure ()
    pat_end
