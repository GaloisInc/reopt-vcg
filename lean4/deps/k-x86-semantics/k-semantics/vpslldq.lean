def vpslldq1 : instruction :=
  definst "vpslldq" $ do
    pattern fun (v_3130 : imm int) (v_3134 : reg (bv 128)) (v_3135 : reg (bv 128)) => do
      v_7779 <- getRegister v_3134;
      v_7780 <- eval (handleImmediateWithSignExtend v_3130 8 8);
      setRegister (lhs.of_reg v_3135) (extract (shl v_7779 (extract (shl (mux (ugt v_7780 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7780)) (expression.bv_nat 128 3)) 0 128)) 0 128);
      pure ()
    pat_end;
    pattern fun (v_3136 : imm int) (v_3140 : reg (bv 256)) (v_3141 : reg (bv 256)) => do
      v_7789 <- getRegister v_3140;
      v_7791 <- eval (handleImmediateWithSignExtend v_3136 8 8);
      v_7796 <- eval (extract (shl (mux (ugt v_7791 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7791)) (expression.bv_nat 128 3)) 0 128);
      setRegister (lhs.of_reg v_3141) (concat (extract (shl (extract v_7789 0 128) v_7796) 0 128) (extract (shl (extract v_7789 128 256) v_7796) 0 128));
      pure ()
    pat_end
