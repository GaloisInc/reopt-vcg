def pslldq1 : instruction :=
  definst "pslldq" $ do
    pattern fun (v_3060 : imm int) (v_3061 : reg (bv 128)) => do
      v_7606 <- getRegister v_3061;
      v_7607 <- eval (handleImmediateWithSignExtend v_3060 8 8);
      setRegister (lhs.of_reg v_3061) (extract (shl v_7606 (extract (shl (mux (ugt v_7607 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7607)) (expression.bv_nat 128 3)) 0 128)) 0 128);
      pure ()
    pat_end
