def psrldq1 : instruction :=
  definst "psrldq" $ do
    pattern fun (v_3045 : imm int) (v_3044 : reg (bv 128)) => do
      v_8172 <- getRegister v_3044;
      v_8173 <- eval (handleImmediateWithSignExtend v_3045 8 8);
      v_8176 <- eval (mux (ugt v_8173 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8173));
      setRegister (lhs.of_reg v_3044) (lshr v_8172 (uvalueMInt (extract (shl v_8176 3) 0 (bitwidthMInt v_8176))));
      pure ()
    pat_end
