def cmovsq1 : instruction :=
  definst "cmovsq" $ do
    pattern fun (v_3263 : reg (bv 64)) (v_3264 : reg (bv 64)) => do
      v_5160 <- getRegister sf;
      v_5162 <- getRegister v_3263;
      v_5163 <- getRegister v_3264;
      setRegister (lhs.of_reg v_3264) (mux (eq v_5160 (expression.bv_nat 1 1)) v_5162 v_5163);
      pure ()
    pat_end;
    pattern fun (v_3255 : Mem) (v_3256 : reg (bv 64)) => do
      v_8583 <- getRegister sf;
      v_8585 <- evaluateAddress v_3255;
      v_8586 <- load v_8585 8;
      v_8587 <- getRegister v_3256;
      setRegister (lhs.of_reg v_3256) (mux (eq v_8583 (expression.bv_nat 1 1)) v_8586 v_8587);
      pure ()
    pat_end
