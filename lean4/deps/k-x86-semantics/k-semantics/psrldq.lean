def psrldq1 : instruction :=
  definst "psrldq" $ do
    pattern fun (v_3108 : imm int) (v_3107 : reg (bv 128)) => do
      v_7843 <- getRegister v_3107;
      v_7844 <- eval (handleImmediateWithSignExtend v_3108 8 8);
      setRegister (lhs.of_reg v_3107) (lshr v_7843 (extract (shl (mux (ugt v_7844 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7844)) (expression.bv_nat 128 3)) 0 128));
      pure ()
    pat_end
