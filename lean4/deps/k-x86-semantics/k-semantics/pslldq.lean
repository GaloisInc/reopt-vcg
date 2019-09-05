def pslldq1 : instruction :=
  definst "pslldq" $ do
    pattern fun (v_3033 : imm int) (v_3032 : reg (bv 128)) => do
      v_7579 <- getRegister v_3032;
      v_7580 <- eval (handleImmediateWithSignExtend v_3033 8 8);
      setRegister (lhs.of_reg v_3032) (extract (shl v_7579 (extract (shl (mux (ugt v_7580 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7580)) (expression.bv_nat 128 3)) 0 128)) 0 128);
      pure ()
    pat_end
