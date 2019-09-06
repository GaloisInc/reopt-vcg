def psrldq1 : instruction :=
  definst "psrldq" $ do
    pattern fun (v_3135 : imm int) (v_3136 : reg (bv 128)) => do
      v_7870 <- getRegister v_3136;
      v_7871 <- eval (handleImmediateWithSignExtend v_3135 8 8);
      setRegister (lhs.of_reg v_3136) (lshr v_7870 (extract (shl (mux (ugt v_7871 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7871)) (expression.bv_nat 128 3)) 0 128));
      pure ()
    pat_end
