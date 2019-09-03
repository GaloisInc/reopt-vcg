def pslldq1 : instruction :=
  definst "pslldq" $ do
    pattern fun (v_2970 : imm int) (v_2969 : reg (bv 128)) => do
      v_7803 <- getRegister v_2969;
      v_7804 <- eval (handleImmediateWithSignExtend v_2970 8 8);
      v_7807 <- eval (mux (ugt v_7804 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7804));
      setRegister (lhs.of_reg v_2969) (extract (shl v_7803 (uvalueMInt (extract (shl v_7807 3) 0 (bitwidthMInt v_7807)))) 0 (bitwidthMInt v_7803));
      pure ()
    pat_end
